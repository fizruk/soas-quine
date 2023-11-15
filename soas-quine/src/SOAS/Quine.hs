{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module SOAS.Quine where

import Data.Bifunctor

import Control.Monad
import Free.Scoped
import Free.Scoped.TH
import Data.Bifunctor.TH
import Data.Void
import Data.Bitraversable
import Data.Bifoldable
import Data.Maybe (mapMaybe)

-- * SOAS

data MetaF metavar scope term
  = MetaVarF metavar [term]
  deriving (Eq, Show, Functor)
deriveBifunctor ''MetaF
deriveBifoldable ''MetaF
deriveBitraversable ''MetaF

type SOAS sig metavar var = FS (sig :+: MetaF metavar) var

data Equation sig metavar var =
  SOAS sig metavar var :==: SOAS sig metavar var

deriving instance (forall scope term. (Eq scope, Eq term) => Eq (sig scope term), Eq var, Eq metavar) => Eq (Equation sig metavar var)
deriving instance (forall scope term. (Show scope, Show term) => Show (sig scope term), Show var, Show metavar) => Show (Equation sig metavar var)

pattern M :: metavar -> [SOAS sig metavar var] -> SOAS sig metavar var
pattern M m args = Free (InR (MetaVarF m args))

data IncMany var
  = BoundVar Int -- bound variable
  | FreeVar var
  deriving (Eq, Show, Functor, Foldable, Traversable)

newtype MetaSubst sig metavar metavar' var
  = MetaSubst { getMetaSubsts :: [(metavar, SOAS sig metavar' (IncMany var))] }
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)

deriving instance (forall scope term. (Eq scope, Eq term) => Eq (sig scope term), Eq var, Eq metavar, Eq metavar') => Eq (MetaSubst sig metavar metavar' var)
deriving instance (forall scope term. (Show scope, Show term) => Show (sig scope term), Show var, Show metavar, Show metavar') => Show (MetaSubst sig metavar metavar' var)

applyMetaSubst :: (Eq metavar, Bifunctor sig)
  => MetaSubst sig metavar metavar' var -> SOAS sig metavar var -> SOAS sig metavar' var
applyMetaSubst substs = \case
  Pure x -> Pure x
  Free (InR (MetaVarF m args)) ->
    case lookup m (getMetaSubsts substs) of
      Nothing -> error "undefined metavariable!"
      Just body -> body >>= f (map (applyMetaSubst substs) args)
  t@(Free (InL op)) -> Free (InL (bimap (applyMetaSubst (fmap S substs)) (applyMetaSubst substs) op))
  where
    f args (BoundVar i) = args !! i
    f _args (FreeVar x) = Pure x

-- >>> applyMetaSubstEquation exSubst beta
-- Free (InL (AppF (Free (InL (LamF (Free (InL (LamF (Free (InL (AppF (Pure (S Z)) (Free (InL (AppF (Pure (S Z)) (Pure Z))))))))))))) (Pure "f"))) :==: Free (InL (LamF (Free (InL (AppF (Pure (S "f")) (Free (InL (AppF (Pure (S "f")) (Pure Z)))))))))
applyMetaSubstEquation :: (Eq metavar, Bifunctor sig)
  => MetaSubst sig metavar metavar' var -> Equation sig metavar var -> Equation sig metavar' var
applyMetaSubstEquation substs (x :==: y) = x' :==: y'
  where
    x' = applyMetaSubst substs x
    y' = applyMetaSubst substs y

-- * Zip-match

class ZipMatch sig where
  zipMatch
    :: sig scope term -> sig scope' term' -> Maybe (sig (scope, scope') (term, term'))

instance ZipMatch LambdaF where
  zipMatch (AppF fun1 arg1) (AppF fun2 arg2)
    = Just (AppF (fun1, fun2) (arg1, arg2))
  zipMatch (LamF body1) (LamF body2)
    = Just (LamF (body1, body2))
  zipMatch _ _ = Nothing

-- * Matching

closed :: Bitraversable sig => SOAS sig metavar var -> Maybe (SOAS sig metavar Void)
closed = traverse (const Nothing)

closed2 :: Bitraversable sig => SOAS sig metavar var -> Maybe (SOAS sig metavar' var')
closed2 = traverse (const Nothing) >=> traverseFS f
  where
    f (InR MetaVarF{}) = Nothing
    f (InL x) = Just (InL x)

closedSubst :: Bitraversable sig => MetaSubst sig metavar metavar' (Inc var) -> Maybe (MetaSubst sig metavar metavar' var)
closedSubst = traverse (const Nothing)

-- \ z. M []   `match`   \z. z    M[] := z INVALID

-- f = \ x . f x
-- \ z . M[] z  =  M[]

-- M[x, x]  `match`  x       M[x1,x2] := x1  OR  M[x1,x2] := x2

-- Current assumptions/limitations:
-- * LHS (pattern) has distinct metavariables (no duplicate names)
match
  :: (ZipMatch sig, Bitraversable sig, Eq metavar, Eq var, forall scope term. (Eq scope, Eq term) => Eq (sig scope term))
  => SOAS sig metavar var
  -> SOAS sig metavar' var
  -> [MetaSubst sig metavar metavar' var]
match lhs rhs =
  case lhs of
    Free (InR (MetaVarF m []))
      | Just rhs' <- closed2 rhs
      -> return (MetaSubst [(m, absurd <$> rhs')])

    Free (InR (MetaVarF m args)) ->
      [ MetaSubst ((m, Pure (BoundVar i)) : subst)
      | (i, arg) <- zip [0..] args
      , MetaSubst subst <- match arg rhs
      ]

    Free (InL opL) ->
      case rhs of
        Free (InL opR) ->
          case zipMatch opL opR of
            Just op -> do
              op' <- bitraverse (mapMaybe closedSubst . uncurry match) (uncurry match) op
              return (bifold op')
            Nothing -> []
        _ -> []

    Pure x ->
      case rhs of
        Pure y | x == y -> return (MetaSubst [])
        _ -> []

-- * E-unification



-- * Example (untyped lambda calculus)

data LambdaF scope term
  = AppF term term
  | LamF scope
  deriving (Eq, Show, Functor, Foldable, Traversable)
deriveBifunctor ''LambdaF
deriveBifoldable ''LambdaF
deriveBitraversable ''LambdaF
makePatternsAll ''LambdaF

pattern Var x = Pure x

type Lambda = FS LambdaF
type LambdaE metavar var = SOAS LambdaF metavar var

two :: SOAS LambdaF metavar var
two = LamE (LamE (AppE s (AppE s z)))
  where
    s = Pure (S Z)
    z = Pure Z

-- (\ z. M[z]) N[] = M[N[]]
beta :: Equation LambdaF String var
beta = AppE (LamE (M "M" [Var Z])) (M "N" []) :==: M "M" [M "N" []]

-- (\ s. \z. s (s z)) f
-- M[z'] := \z. z' (z' z)
-- N[] := f
exSubst :: MetaSubst LambdaF String metavar String
exSubst = MetaSubst
  [ let z' = Pure (S (BoundVar 0))
        z  = Pure Z
    in ("M", LamE (AppE z' (AppE z' z)))
  , ("N", Var (FreeVar "f"))
  ]
