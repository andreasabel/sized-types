{-# LANGUAGE LambdaCase #-}

-- | Auxiliary functions for abstract syntax.

module Abstract where

import Sit.Abs as A

introduction :: Exp -> Bool
introduction = \case
  Var{}    -> False
  App{}    -> False
  Case{}   -> False
  Int{}    -> True
  Infty    -> True
  Nat      -> True
  Set      -> True
  Set1     -> True
  Set2     -> True
  Zero     -> True
  Suc      -> True
  Fix      -> True
  LZero    -> True
  LSuc     -> True
  Lam{}    -> True
  Forall{} -> True
  Pi{}     -> True
  Arrow{}  -> True
  Plus{}   -> True
  ELam{}   -> True

fromIdU :: A.IdU -> String
fromIdU = \case
  A.Id (A.Ident x) -> x
  A.Under -> "_"
