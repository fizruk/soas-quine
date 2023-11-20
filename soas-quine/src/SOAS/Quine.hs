{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
module SOAS.Quine where

import Data.Bifunctor ( Bifunctor(first, bimap) )

import Control.Monad ( (>=>) )
import Free.Scoped
    ( traverseFS, type (:+:), FS(..), Inc(..), Sum(InL, InR) )
import Free.Scoped.TH ( makePatternsAll )
import Data.Bifunctor.TH
    ( deriveBifoldable, deriveBifunctor, deriveBitraversable )
import Data.Void ( Void, absurd )
import Data.Bitraversable ( Bitraversable(..) )
import Data.Bifoldable ( Bifoldable(bifold) )
import Data.Maybe (mapMaybe, maybeToList)
import Data.List (intercalate)

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
  Free (InL op) -> Free (InL (bimap (applyMetaSubst (fmap S substs)) (applyMetaSubst substs) op))
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

-- >>> matchMetaVar [AppE (Var "A") (M "N" [Var "B"]), Var "C"] [] (Var "C")
-- [(Pure (BoundVar 1),MetaSubst {getMetaSubsts = []})]
--
-- M[A,B,A N[B],C] =?= Π (x : A B), C x
-- 1) M[a1,a2,a3,a4] := Π (x : a3), a4 x
--    N[a1] := a1
-- 2) M[a1,a2,a3,a4] := Π (x : a1 a2), a4 x
-- >>> matchMetaVar [Var "A", Var "B", AppE (Var "A") (M "N" [Var "B"]), Var "C"] [] (PiE (AppE (Var "A") (Var "B")) (AppE (Var (S "C")) (Var Z)))
-- [(Free (InL (PiF (Pure (BoundVar 2)) (Free (InL (AppF (Pure (S (BoundVar 3))) (Pure Z)))))),MetaSubst {getMetaSubsts = [("N",Pure (BoundVar 0))]}),(Free (InL (PiF (Free (InL (AppF (Pure (BoundVar 0)) (Pure (BoundVar 1))))) (Free (InL (AppF (Pure (S (BoundVar 3))) (Pure Z)))))),MetaSubst {getMetaSubsts = []})]
-- >>> matchMetaVar [AppE (Var "A") (M "N" [Var "B"]), Var "C"] [] (AppE (Var "A") (Var "B"))
-- [(Pure (BoundVar 0),MetaSubst {getMetaSubsts = [("N",Pure (BoundVar 0))]})]
matchMetaVar
  :: (ZipMatch sig, Bitraversable sig, Eq metavar, Eq var, forall scope term. (Eq scope, Eq term) => Eq (sig scope term))
  => [SOAS sig metavar var]
  -> [var]
  -> SOAS sig metavar' var
  -> [(SOAS sig metavar' (IncMany var), MetaSubst sig metavar metavar' var)]
matchMetaVar args boundVars rhs = projections ++ projectionsBoundVars ++ imitations
  where
    projections =
      [ (Pure (BoundVar i), subst)
      | (i, arg) <- zip [0..] args
      , subst <- match arg rhs
      ]
    projectionsBoundVars =
      [ (Pure (FreeVar boundVar), subst)
      | boundVar <- boundVars
      , subst <- match (Pure boundVar) rhs
      ]

    k :: IncMany (Inc a) -> Inc (IncMany a)
    k (BoundVar i) = S (BoundVar i)
    k (FreeVar Z) = Z
    k (FreeVar (S x)) = S (FreeVar x)

    imitations =
      [ (Free (InL (first (fmap k) body)), subst)
      | Free (InL opR) <- [rhs]     -- M[A + N[B], C] =?= Π (x : A + B), C x
                                    -- M[X,Y] := Π (x : X), Y x
      , opR' :: sig (SOAS sig metavar' (IncMany (Inc var)), MetaSubst sig metavar metavar' (Inc var))
                    (SOAS sig metavar' (IncMany var), MetaSubst sig metavar metavar' var)
          <- bitraverse (matchMetaVar (fmap (fmap S) args) (Z : fmap S boundVars)) (matchMetaVar args boundVars) opR
      -- opR' = Π (x : (Bound 1, [N[B] := B])), (AppE (S (Bound 2)) Z, [])
      , let body = bimap fst fst opR'
      , op' <- bitraverse (maybeToList . closedSubst . snd) (pure . snd) opR'
      , let subst = bifold op'
      ]

-- Current assumptions/limitations:
-- * LHS (pattern) has distinct metavariables (no duplicate names)
--
-- >>> lhs :==: _rhs = beta
-- >>> match lhs (AppE (LamE (Pure Z)) two) :: [MetaSubst LambdaF String String String]
-- [MetaSubst {getMetaSubsts = [("M",Pure (BoundVar 0)),("N",Free (InL (LamF (Free (InL (LamF (Free (InL (AppF (Pure (S Z)) (Free (InL (AppF (Pure (S Z)) (Pure Z)))))))))))))]}]
-- >>> match lhs (AppE two two)
-- [MetaSubst {getMetaSubsts = [("M",Free (InL (LamF (Free (InL (AppF (Pure (S (BoundVar 0))) (Free (InL (AppF (Pure (S (BoundVar 0))) (Pure Z)))))))))),("N",Free (InL (LamF (Free (InL (LamF (Free (InL (AppF (Pure (S Z)) (Free (InL (AppF (Pure (S Z)) (Pure Z)))))))))))))]}]
match
  :: (ZipMatch sig, Bitraversable sig, Eq metavar, Eq var, forall scope term. (Eq scope, Eq term) => Eq (sig scope term))
  => SOAS sig metavar var
  -> SOAS sig metavar' var
  -> [MetaSubst sig metavar metavar' var]
match lhs rhs =
  case lhs of
    Free (InR (MetaVarF m []))
      | Just rhs' <- closed2 rhs
      -> return (MetaSubst [(m, absurd <$> rhs')])    -- projection

    Free (InR (MetaVarF m args)) ->
      [ MetaSubst [(m, body)] <> subst
      | (body, subst) <- matchMetaVar args [] rhs
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
  | PiF term scope
  deriving (Eq, Show, Functor, Foldable, Traversable)
deriveBifunctor ''LambdaF
deriveBifoldable ''LambdaF
deriveBitraversable ''LambdaF
makePatternsAll ''LambdaF

pattern Var x = Pure x

type Lambda = FS LambdaF
type LambdaE metavar var = SOAS LambdaF metavar var

instance {-# OVERLAPPING #-} Show var => Show (LambdaE String var) where
  show = ppLambdaE defaultVars . fmap show
    where
      defaultVars = [ "x" <> show n | n <- [1..] ]

instance {-# OVERLAPPING #-} Show var => Show (MetaSubst LambdaF String String var) where
  show (MetaSubst substs) = show substs

ppLambdaE :: [String] -> LambdaE String String -> String
ppLambdaE = go id
  where
    go :: (var -> String) -> [String] -> LambdaE String var -> String
    go varName freshVars = \case
      Pure x -> varName x
      Free (InR (MetaVarF m args)) -> m ++ "[" ++ intercalate "," (map (go varName freshVars) args) ++  "]"
      Free (InL (AppF fun arg)) -> "(" ++ go varName freshVars fun ++ ") " ++ go varName freshVars arg
      Free (InL (LamF body)) -> withScope $ \ z zs varName' ->
        "λ " ++ z ++ " . " ++ go varName' zs body
      Free (InL (PiF a b)) -> withScope $ \ z zs varName' ->
        "Π (" ++ z ++ " : " ++ go varName freshVars a ++ "), " ++ go varName' zs b
      where
        withScope f = case freshVars of
          [] -> error "not enough fresh variables"
          z:zs ->
            let varName' Z = z
                varName' (S x) = varName x
            in f z zs varName'

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
