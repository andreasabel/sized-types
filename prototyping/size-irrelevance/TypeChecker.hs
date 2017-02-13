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

checkSig :: A.Ident -> A.Exp -> Check ()
checkSig x0@(A.Ident x) a = traceCheck (A.Sig x0 a) $ do

  -- Check that x is not already defined
  mt <- lookupTySig x
  unless (isNothing mt) $
    throwError $ "Duplicate type signature for " ++ x

  -- Check type and add to signature
  t <- checkType a
  addTySig x =<< evaluate t

checkDef :: A.Ident -> A.Exp -> Check ()
checkDef x0@(A.Ident x) e = traceCheck (A.Def x0 e) $ do

  -- Check that x has a signature
  let noSig = throwError $ "Missing type signature for " ++ x
  t <- maybe noSig return =<< lookupTySig x

  -- Check that x has not yet a definition
  mv <- lookupTySig x
  unless (isNothing mv) $
    throwError $ "Duplicate definition of " ++ x

  -- Check definition and add to signature
  v <- checkExp e t
  addDef x =<< evaluate v

checkType :: A.Exp -> Check Type
checkType e = fst <$> inferType e

-- | Check that something is a type and infer its universe level
inferType :: A.Exp -> Check (Type, VLevel)
inferType = \case

  -- Universe
  A.Set  -> return (Type sZero, vsConst 1)
  A.Set1 -> return (Type $ sSuc sZero, vsConst 2)
  A.Set2 -> return (Type $ sSuc $ sSuc sZero, vsConst 3)
  A.App A.Set l -> do
    a <- checkLevel l
    v <- evaluate a
    return (Type a, vsSuc v)

  -- Function types
  e@(A.Arrow a b) -> do
    (u, l1) <- inferType a
    (t, l2) <- inferType b
    l <- maxLevel e l1 l2
    return (Pi (defaultDom u) (NoAbs "_" t) , l)

  e@(A.Pi xs a b) -> do
    (u, l1) <- inferType a
    v <- evaluate u
    addContext (map (,v) xs) $ do
      (t, l2) <- inferType b
      return __IMPOSSIBLE__

  _ -> __IMPOSSIBLE__

checkLevel :: A.Exp -> Check Level
checkLevel = \case
  A.LZero        -> return $ sZero
  A.App A.LSuc e -> sSuc <$> checkLevel e
  e@(A.Var x)    -> checkExp e VSize
  e -> throwError $ "Not a valid level expression: " ++ printTree e

maxLevel :: A.Exp -> VLevel -> VLevel -> Check VLevel
maxLevel e l1 l2 = maybe failure return $ maxSize l1 l2
  where failure = throwError $ "Cannot assign a universe level to type " ++ printTree e

checkExp :: A.Exp -> VType -> Check Term
checkExp = \case
  _ -> __IMPOSSIBLE__

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

evaluate :: Term -> Check Val
evaluate t = do
  sig   <- use stDefs
  delta <- asks _envEnv
  return $ runReader (evalIn t delta) sig

instance MonadEval (Reader (Map Id Val)) where
  getDef x = fromMaybe __IMPOSSIBLE__ . Map.lookup x <$> ask

-- | Extend the typing context

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

fromIdU :: A.IdU -> String
fromIdU = \case
  A.Id (A.Ident x) -> x
  A.Under -> "_"
