{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}

module TypeChecker where

import Control.Applicative
import Control.Lens hiding (Level)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Functor
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Debug.Trace

import qualified Sit.Abs as A
import Sit.Print
import Sit.ErrM

import Abstract as A
import Internal
import Evaluation

import Impossible
#include "undefined.h"

-- | Type errors are just strings.
type TypeError = String

-- | Local context

type Cxt = [ (Id, Dom VType) ]

data TCEnv = TCEnv
  { _envCxt :: Cxt  -- ^ Typing context.
  , _envEnv :: Env  -- ^ Default environment.
  }

makeLenses ''TCEnv

-- | Global state

data TCSt = TCSt
  { _stTySigs :: Map Id VType
  , _stDefs   :: Map Id Val
  }

makeLenses ''TCSt

-- | The type checking monad
type Check = ReaderT TCEnv (StateT TCSt (Except TypeError))

-- * Type checker

typeCheck :: [A.Decl] -> Either String ()
typeCheck decls = runExcept (evalStateT (runReaderT (checkDecls decls) initEnv) initSt)
  where
  initEnv = TCEnv { _envCxt   = []        , _envEnv = []        }
  initSt  = TCSt  { _stTySigs = Map.empty , _stDefs = Map.empty }

checkDecls :: [A.Decl] -> Check ()
checkDecls = mapM_ checkDecl

checkDecl :: A.Decl -> Check ()
checkDecl = \case
  A.Open{} -> return ()
  A.Sig x a -> checkSig x a
  A.Def x e -> checkDef x e

-- | Check a type signature.

checkSig :: A.Ident -> A.Exp -> Check ()
checkSig x0@(A.Ident x) a = traceCheck (A.Sig x0 a) $ do

  -- Check that x is not already defined
  mt <- lookupTySig x
  unless (isNothing mt) $
    throwError $ "Duplicate type signature for " ++ x

  -- Check type and add to signature
  t <- checkType a
  addTySig x =<< evaluate t

-- | Check a definition.

checkDef :: A.Ident -> A.Exp -> Check ()
checkDef x0@(A.Ident x) e = traceCheck (A.Def x0 e) $ do

  -- Check that x has a signature
  let noSig = throwError $ "Missing type signature for " ++ x
  t <- maybe noSig return =<< lookupTySig x

  -- Check that x has not yet a definition
  mv <- lookupDef x
  unless (isNothing mv) $
    throwError $ "Duplicate definition of " ++ x

  -- Check definition and add to signature
  v <- checkExp e t
  addDef x =<< evaluate v

-- | Check well-formedness of a type.

checkType :: A.Exp -> Check Type
checkType e = fst <$> inferType e

-- | Check that something is a type and infer its universe level.

inferType :: A.Exp -> Check (Type, VLevel)
inferType e = do
  let invalidType = throwError $ "Not a valid type expression: " ++ printTree e
  case e of

    -- Universes

    A.Set  -> return (Type sZero, vsConst 1)
    A.Set1 -> return (Type $ sSuc sZero, vsConst 2)
    A.Set2 -> return (Type $ sSuc $ sSuc sZero, vsConst 3)
    A.App A.Set l -> do
      a <- checkLevel l
      v <- evaluate a
      return (Type a, vsSuc v)

    -- Natural number type

    A.App A.Nat s -> do
      a <- checkSize s
      v <- evaluate a
      return (Nat a, vsZero)

    -- Function types

    A.Arrow a b -> do
      (u, l1) <- inferType a
      (t, l2) <- inferType b
      return (Pi (defaultDom u) (NoAbs "_" t) , maxSize l1 l2)

    A.Pi xs a b -> inferPisType (map (, defaultDom a) xs) $ inferType b

    A.Forall bs c -> inferPisType (fromBind =<< bs) $ inferType c
      where
      fromBind :: A.Bind -> [(A.IdU, Dom A.Exp)]
      fromBind = \case
        A.BIrrel x  -> return (A.Id x, Dom Irrelevant A.Size)
        A.BRel   x  -> return (A.Id x, Dom ShapeIrr   A.Size)
        A.BAnn xs a -> map (\ x -> (A.Id x, defaultDom a)) xs

    -- Neutral types

    e | A.introduction e -> invalidType

    e -> do
      (t,v) <- inferExp e
      case v of
        VType l -> return (t,l)
        _ -> invalidType

inferPisType :: [(A.IdU, Dom A.Exp)] -> Check (Type, VLevel) -> Check (Type, VLevel)
inferPisType = foldr (.) id . map (uncurry inferPiType)

inferPiType :: A.IdU -> Dom A.Exp -> Check (Type, VLevel) -> Check (Type, VLevel)
inferPiType x dom cont = do

  -- Check the domain
  (u, l1) <- inferType $ unDom dom

  -- Check the codomain in the extended context.
  v <- evaluate u
  addContext (x, v) $ do
    (t, l2) <- cont

    -- Compute the universe level of the Pi-type.
    let l0 = maxSize l1 l2

    -- Check that the level does not mention the bound variable
    -- If yes, return oo instead.
    l <- case fromMaybe __IMPOSSIBLE__ $ sizeView l0 of
      SVVar k' _ -> do
        k <- length <$> asks _envCxt
        return $ if k' >= k then VInfty else l0
      _ -> return l0

    -- Construct the function type
    return ( Pi (dom $> u) $ Abs (fromIdU x) t , l )

checkSize :: A.Exp -> Check Size
checkSize = \case
  A.LZero        -> return $ sZero
  A.App A.LSuc e -> sSuc <$> checkSize e
  e@(A.Var x)    -> checkExp e VSize
  e -> throwError $ "Not a valid size expression: " ++ printTree e

checkLevel :: A.Exp -> Check Level
checkLevel = \case
  A.LZero        -> return $ sZero
  A.App A.LSuc e -> sSuc <$> checkLevel e
  e@(A.Var x)    -> checkExp e VSize
  e -> throwError $ "Not a valid level expression: " ++ printTree e

-- maxLevel :: A.Exp -> VLevel -> VLevel -> Check VLevel
-- maxLevel e l1 l2 = maybe failure return $ maxSize l1 l2
--   where failure = throwError $ "Cannot assign a universe level to type " ++ printTree e

checkExp :: A.Exp -> VType -> Check Term
checkExp e0 t = do
  case e0 of
    A.Lam []     e -> checkExp e t
    A.Lam (x:xs) e -> do
      case t of
        VPi dom cl -> addContext (x, dom) $ do
          t' <- applyClosure cl =<< lastVal
          u  <- checkExp (A.Lam xs e) t'
          return $ Lam (domInfo dom) $ Abs (fromIdU x) u
        _ -> throwError $ "Lambda abstraction expects function type, but got " ++ show t
    e -> do
      (u, ti) <- inferExp e
      coerce u ti t
    -- e -> nyi $ "checking " ++ printTree e

-- | Precondition: @not (A.introduction e)@.

inferExp :: A.Exp -> Check (Term, VType)
inferExp = \case

  e | mustBeType e -> do
    (t, l) <- inferType e
    return (t, VType l)

  A.Var x -> do
    (u, Dom r t) <- inferVar x
    if r == Relevant then return (u,t) else
      throwError $ "Illegal reference to variable: " ++ printTree x

  A.App f e -> nyi "application"
  A.Case{}  -> nyi "case"

  _ -> __IMPOSSIBLE__

-- | Infer type of a variable

inferVar :: A.Ident -> Check (Term, Dom VType)
inferVar (A.Ident x) = do
  (lookupCxt x <$> asks _envCxt) >>= \case
    Nothing     -> throwError $ "Variable not in scope: " ++ x
    Just (i, t) -> return (var $ Index i, t)

-- | Coercion / subtype checking.

coerce :: Term -> VType -> VType -> Check Term
coerce u ti tc = nyi "Coercion"

-- | Type checker auxiliary functions.

traceCheck :: Print a => a -> b -> b
traceCheck a = trace $ "Checking " ++ printTree a

nyi :: String -> Check a
nyi = throwError . ("Not yet implemented: " ++)

-- | Signature auxiliary functions

lookupTySig :: Id -> Check (Maybe VType)
lookupTySig x = Map.lookup x <$> use stTySigs

lookupDef :: Id -> Check (Maybe Val)
lookupDef x = Map.lookup x <$> use stDefs

addTySig :: Id -> VType -> Check ()
addTySig x t = stTySigs %= Map.insert x t

addDef :: Id -> Val -> Check ()
addDef x v = stDefs %= Map.insert x v

-- * Invoking evaluation

instance MonadEval (Reader (Map Id Val)) where
  getDef x = fromMaybe __IMPOSSIBLE__ . Map.lookup x <$> ask

evaluate :: Term -> Check Val
evaluate t = do
  sig   <- use stDefs
  delta <- asks _envEnv
  return $ runReader (evalIn t delta) sig

applyClosure :: VClos -> Val -> Check Val
applyClosure cl v =
  runReader (applyClos cl v) <$> use stDefs

-- * Context manipulation

-- | Looking up in the typing context

lookupCxt :: Id -> Cxt -> Maybe (Int, Dom VType)
lookupCxt x cxt = loop 0 cxt
  where
  loop i = \case
    [] -> Nothing
    ((y,t) : cxt)
      | x == y    -> Just (i,t)
      | otherwise -> loop (succ i) cxt


-- | Value of last variable added to context.

lastVal :: Check Val
lastVal = head <$> asks _envEnv

-- | Extending the typing context

class AddContext a where
  addContext :: a -> Check b -> Check b

instance AddContext a => AddContext [a] where
  addContext as = foldr (.) id $ map addContext as

-- A.IdU instances

instance AddContext (A.IdU, Type) where
  addContext (x,t) = addContext (fromIdU x, t)

instance AddContext (A.IdU, VType) where
  addContext (x,t) = addContext (fromIdU x, t)

instance AddContext (A.IdU, Dom VType) where
  addContext (x,t) = addContext (fromIdU x, t)

-- Id instances

instance AddContext (Id, Type) where
  addContext (x,t) cont = do
    t <- evaluate t
    addContext (x,t) cont

instance AddContext (Id, VType) where
  addContext (x,t) = addContext (x, defaultDom t)

instance AddContext (Id, Dom VType) where
  addContext (x,t) = local
    $ over envCxt ((x,t):)
    . over envEnv nextVar
    where nextVar delta = vVar (unDom t) (length delta) : delta
