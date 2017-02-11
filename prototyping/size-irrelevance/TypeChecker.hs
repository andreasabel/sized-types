{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module TypeChecker where

import Control.Applicative
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

-- | Type errors are just strings.
type TypeError = String

-- | The type checking monad
type Check = ReaderT Env (StateT St (Except TypeError))

-- | Local context

data Env = Env
  { envCxt :: Cxt
  }

type Cxt = [ (Id, Type) ]

type Id = String

-- | Global state

data St = St
  { stSig :: Sig
  }

type Sig = Map Id Function

data Function = Function
  { funType :: Type
  , funVal  :: Term
  }

typeCheck :: [A.Decl] -> Either String ()
typeCheck decls = runExcept (evalStateT (runReaderT (checkDecls decls) initEnv) initSt)
  where
  initEnv = Env { envCxt = [] }
  initSt  = St  { stSig  = Map.empty }

checkDecls :: [A.Decl] -> Check ()
checkDecls = mapM_ checkDecl

checkDecl :: A.Decl -> Check ()
checkDecl = \case
  A.Open{} -> return ()
  A.Sig x a -> checkSig x a
  A.Def x e -> checkDef x e

checkSig :: A.Ident -> A.Exp -> Check ()
checkSig x a = traceCheck (A.Sig x a) $ do
  nyi "checking a type signature"

checkDef :: A.Ident -> A.Exp -> Check ()
checkDef x e = traceCheck (A.Def x e) $ do
  nyi "checking a  definition"

traceCheck :: Print a => a -> b -> b
traceCheck a = trace $ "Checking " ++ printTree a

nyi :: String -> Check a
nyi = throwError . ("Not yet implemented: " ++)
