{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
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
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}
module SOAS.Quine where

import Data.Bifunctor ( Bifunctor(first, bimap) )
import Data.Bifoldable ( Bifoldable(bifoldMap, bifold) )

import Control.Monad ( (>=>), guard )
import Free.Scoped
    ( traverseFS, type (:+:), FS(..), Inc(..), Sum(InL, InR), transFS )
import Free.Scoped.TH ( makePatternsAll )
import Data.Bifunctor.TH
    ( deriveBifoldable, deriveBifunctor, deriveBitraversable )
import Data.Void ( Void, absurd )
import Data.Bitraversable ( Bitraversable(..) )
import Data.Maybe (mapMaybe, maybeToList)
import Data.List (intercalate, tails, inits, nub, (\\))

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
  deriving (Functor)

instance Bifunctor sig => Bifunctor (Equation sig) where
  bimap f g (lhs :==: rhs) =
    transFS k (fmap g lhs) :==: transFS k (fmap g rhs)
    where
      k (InL l) = InL l
      k (InR (MetaVarF m args)) = InR (MetaVarF (f m) args)

instance Bifoldable sig => Bifoldable (Equation sig) where
  bifoldMap f g (lhs :==: rhs) = go f g lhs <> go f g rhs
    where
      go :: Monoid m => (a -> m) -> (b -> m) -> SOAS sig a b -> m
      go _ k (Pure x) = k x
      go h k (Free (InL op)) = bifoldMap (go h (foldMap k)) (go h k) op
      go h k (Free (InR (MetaVarF m args))) = h m <> foldMap (go h k) args

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
  => (metavar -> metavar') -> MetaSubst sig metavar metavar' var -> SOAS sig metavar var -> SOAS sig metavar' var
applyMetaSubst rename substs = \case
  Pure x -> Pure x
  Free (InR (MetaVarF m args)) ->
    case lookup m (getMetaSubsts substs) of
      Nothing -> Free (InR (MetaVarF (rename m) (map (applyMetaSubst rename substs) args)))
      Just body -> body >>= f (map (applyMetaSubst rename substs) args)
  Free (InL op) -> Free (InL (bimap (applyMetaSubst rename (fmap S substs)) (applyMetaSubst rename substs) op))
  where
    f args (BoundVar i) = args !! i
    f _args (FreeVar x) = Pure x

-- >>> applyMetaSubstEquation exSubst beta
-- Free (InL (AppF (Free (InL (LamF (Free (InL (LamF (Free (InL (AppF (Pure (S Z)) (Free (InL (AppF (Pure (S Z)) (Pure Z))))))))))))) (Pure "f"))) :==: Free (InL (LamF (Free (InL (AppF (Pure (S "f")) (Free (InL (AppF (Pure (S "f")) (Pure Z)))))))))
applyMetaSubstEquation :: (Eq metavar, Bifunctor sig)
  => (metavar -> metavar') -> MetaSubst sig metavar metavar' var -> Equation sig metavar var -> Equation sig metavar' var
applyMetaSubstEquation rename substs (x :==: y) = x' :==: y'
  where
    x' = applyMetaSubst rename substs x
    y' = applyMetaSubst rename substs y

applyMetaSubstConstraint :: (Eq metavar, Bifunctor sig)
  => (metavar -> metavar')
  -> MetaSubst sig metavar metavar' (IncMany var)
  -> Constraint sig metavar var
  -> Constraint sig metavar' var
applyMetaSubstConstraint rename subst Constraint{..} = Constraint
  { constraintEq = applyMetaSubstEquation rename subst constraintEq
  , .. }

-- * Zip-match

class ZipMatch sig where
  zipMatch
    :: sig scope term -> sig scope' term' -> Maybe (sig (scope, scope') (term, term'))

instance (ZipMatch f, ZipMatch g) => ZipMatch (Sum f g) where
  zipMatch (InL x) (InL y) = InL <$> zipMatch x y
  zipMatch (InR x) (InR y) = InR <$> zipMatch x y
  zipMatch _ _ = Nothing

instance Eq metavar => ZipMatch (MetaF metavar) where
  zipMatch (MetaVarF x xs) (MetaVarF y ys)
    | x == y = Just (MetaVarF x (zip xs ys))
    | otherwise = Nothing

instance ZipMatch LambdaF where
  zipMatch (AppF fun1 arg1) (AppF fun2 arg2)
    = Just (AppF (fun1, fun2) (arg1, arg2))
  zipMatch (LamF body1) (LamF body2)
    = Just (LamF (body1, body2))
  zipMatch _ _ = Nothing

-- * Matching

class (ZipMatch sig, Bitraversable sig, forall scope term. (Eq scope, Eq term) => Eq (sig scope term)) => Matchable sig
instance (ZipMatch sig, Bitraversable sig, forall scope term. (Eq scope, Eq term) => Eq (sig scope term)) => Matchable sig

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
  :: (Matchable sig, Eq metavar, Eq var)
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

addVarArgs :: Bifunctor sig => [var] -> SOAS sig metavar var -> SOAS sig metavar var
addVarArgs vars = \case
  Pure x -> Pure x
  Free (InL op) ->
    Free (InL (bimap (addVarArgs (map S vars)) (addVarArgs vars) op))
  Free (InR (MetaVarF m args)) ->
    Free (InR (MetaVarF m (map Pure vars ++ map (addVarArgs vars) args)))

addVarArgsEquation :: Bifunctor sig => [var] -> Equation sig metavar var -> Equation sig metavar var
addVarArgsEquation vars (lhs :==: rhs) = lhs' :==: rhs'
  where
    lhs' = addVarArgs vars lhs
    rhs' = addVarArgs vars rhs

-- * Computing with rules

applyRule
  :: (Matchable sig, Eq metavar, Eq var)
  => Equation sig metavar var
  -> SOAS sig metavar' var
  -> [SOAS sig metavar' var]
applyRule (lhs :==: rhs) term = do
  subst <- match lhs term
  return (applyMetaSubst (error "impossible happened!") subst rhs)

applyRuleSomewhere
  :: (Matchable sig, Eq metavar, Eq var)
  => Equation sig metavar var
  -> SOAS sig metavar' var
  -> [SOAS sig metavar' var]
applyRuleSomewhere (lhs :==: rhs) term = do
  subst <- match lhs' term
  Just n <- [sum . fmap countBoundVar <$> lookup Z (getMetaSubsts subst)]
  guard (n == 1) -- we use only applications with exactly one rule application (redex)
  -- guard (n > 0)  -- we could instead ask for at least one rule application (redex)
  return (applyMetaSubst (error "impossible happened!") subst rhs')
  where
    countBoundVar BoundVar{} = 1
    countBoundVar _ = 0
    lhs' = M Z [transFS k lhs]
    rhs' = M Z [transFS k rhs]
    k (InL l) = InL l
    k (InR (MetaVarF m args)) = InR (MetaVarF (S m) args)

whnfFromRules
  :: (Matchable sig, Eq metavar, Eq var)
  => [Equation sig metavar var]
  -> SOAS sig metavar' var
  -> [SOAS sig metavar' var]
whnfFromRules rules term
  | null terms' = [term]
  | otherwise = concatMap (whnfFromRules rules) terms'
  where
    terms' =
      [ term'
      | rule <- rules
      , term' <- applyRule rule term
      ]

whnfFromRulesConstraint
  :: (Matchable sig, Eq metavar, Eq var)
  => [Equation sig metavar var]
  -> Constraint sig metavar' var
  -> [Constraint sig metavar' var]
whnfFromRulesConstraint rules Constraint{..} =
  [ Constraint{ constraintEq = lhs' :==: rhs', ..}
  | let lhs :==: rhs = constraintEq
  , lhs' <- whnfFromRules rules' lhs
  , rhs' <- whnfFromRules rules' rhs
  ]
  where
    rules' =
      [ addVarArgsEquation (BoundVar <$> [0 .. constraintScope - 1]) (fmap FreeVar rule)
      | rule <- rules ]

whnfChainFromRules
  :: (Matchable sig, Eq metavar, Eq var)
  => [Equation sig metavar var]
  -> SOAS sig metavar' var
  -> [[SOAS sig metavar' var]]
whnfChainFromRules rules term
  | null terms' = pure [term]
  | otherwise = do
      term' <- terms'
      chain <- whnfChainFromRules rules term'
      return (term : chain)
  where
    terms' =
      [ term'
      | rule <- rules
      , term' <- applyRuleSomewhere rule term
      ]

-- * E-unification

data Constraint sig metavar var = Constraint
  { constraintEq :: Equation sig metavar (IncMany var)
  , constraintScope :: Int
  } deriving (Functor)

instance Bifunctor sig => Bifunctor (Constraint sig) where
  bimap f g Constraint{..} = Constraint{constraintEq = bimap f (fmap g) constraintEq, ..}

instance Bifoldable sig => Bifoldable (Constraint sig) where
  bifoldMap f g Constraint{..} = bifoldMap f (foldMap g) constraintEq

deriving instance (forall scope term. (Eq scope, Eq term) => Eq (sig scope term), Eq var, Eq metavar) => Eq (Constraint sig metavar var)
deriving instance (forall scope term. (Show scope, Show term) => Show (sig scope term), Show var, Show metavar) => Show (Constraint sig metavar var)

data Constraint' sig metavar var
  = SOAS sig metavar var :=?=: SOAS sig metavar var
  | ForAll (Constraint' sig metavar (Inc var))

type UnificationProblem sig metavar var
  = [Constraint sig metavar var]

type TransitionRule sig metavar var
  = (Matchable sig, Eq metavar, Eq var)
  => Constraint sig metavar var
  -> [(MetaSubst sig metavar metavar var, [Constraint sig metavar var])]

delete :: TransitionRule sig metavar var
delete Constraint{constraintEq = lhs :==: rhs}
  | lhs == rhs = [(mempty, [])]
delete _ = []

decompose :: TransitionRule sig metavar var
decompose Constraint{constraintEq = Pure x :==: Pure y}
  | x == y = [(mempty, [])]
decompose Constraint{constraintEq = Free lhs :==: Free rhs, ..} =
  case zipMatch lhs rhs of
    Nothing -> []
    Just t -> [(mempty, bifoldMap mkConstraintScope mkConstraint t)]
  where
    mkConstraint (l, r) =
      [Constraint{constraintEq = l :==: r, ..}]
    mkConstraintScope (l, r) =
      [Constraint{constraintEq = l' :==: r', constraintScope = 1 + constraintScope}]
      where
        l' = fmap k l
        r' = fmap k r
        -- turn local variable into a new constraint forall variable
        k Z = BoundVar constraintScope
        k (S x) = x
decompose _ = []

projectImitate :: TransitionRule sig metavar var
projectImitate Constraint{constraintEq = M m args :==: rhs} =
  [ (MetaSubst [(m, substBody')] <> subst', [])
  | (substBody, subst) <- matchMetaVar args [] rhs
  , substBody' <- traverse (traverse onlyFreeVar) substBody
  , subst' <- traverse onlyFreeVar subst
  ]
projectImitate _ = []

refreshAllMetaVars :: (Bifunctor sig, Bifoldable sig, Eq metavar) => [metavar] -> [metavar] -> SOAS sig metavar var -> SOAS sig metavar var
refreshAllMetaVars scopeMeta freshMetaVars term = transFS k term
  where
    k (InR (MetaVarF m args)) = InR (MetaVarF (rename m) args)
    k (InL op) = InL op

    renamings = zip termMetaVars freshMetaVars'
    rename m = case lookup m renamings of
      Nothing -> error "impossible happened"
      Just m' -> m'
    freshMetaVars' = filter (`notElem` scopeMeta) freshMetaVars
    termMetaVars = nub (go term)
      where
        go :: Bifoldable sig => SOAS sig metavar var -> [metavar]
        go Pure{} = []
        go (Free (InL op)) = bifoldMap go go op
        go (Free (InR (MetaVarF m args))) = m : foldMap go args

refreshAllMetaVarsEquation :: (Bifunctor sig, Bifoldable sig, Eq metavar) => [metavar] -> [metavar] -> Equation sig metavar var -> Equation sig metavar var
refreshAllMetaVarsEquation scopeMeta freshMetaVars (lhs :==: rhs) = lhs' :==: rhs'
  where
    lhs' = transFS k lhs
    rhs' = transFS k rhs

    k (InR (MetaVarF m args)) = InR (MetaVarF (rename m) args)
    k (InL op) = InL op

    renamings = zip eqMetaVars freshMetaVars'
    rename m = case lookup m renamings of
      Nothing -> error "impossible happened"
      Just m' -> m'
    freshMetaVars' = filter (`notElem` scopeMeta) freshMetaVars
    eqMetaVars = nub (foldMap go [lhs, rhs])
      where
        go :: Bifoldable sig => SOAS sig metavar var -> [metavar]
        go Pure{} = []
        go (Free (InL op)) = bifoldMap go go op
        go (Free (InR (MetaVarF m args))) = m : foldMap go args

matchingRoots :: ZipMatch sig => SOAS sig metavar var -> SOAS sig metavar var' -> Bool
matchingRoots (Free (InL l)) (Free (InL r))
  | Just _ <- zipMatch l r = True
matchingRoots _ _ = False

mutate :: [metavar] -> [metavar] -> [Equation sig metavar var] -> TransitionRule sig metavar var
mutate scopeMeta freshMetaVars rules Constraint{constraintEq = lhs :==: rhs, ..} =
  [ (mempty,
    [ Constraint{constraintEq = lhs :==: ruleLHS, ..}
    , Constraint{constraintEq = ruleRHS :==: rhs, ..} ])
  | rule@(lhsOrig :==: _) <- rules
  , any (matchingRoots lhsOrig) [lhs, rhs]
  , let refreshedRule = refreshAllMetaVarsEquation scopeMeta freshMetaVars rule
  , let instantiatedRule = addVarArgsEquation [BoundVar i | i <- [0 .. constraintScope - 1]] (FreeVar <$> refreshedRule)
  , let ruleLHS :==: ruleRHS = instantiatedRule
  ]
-- mutate _ _ _ _ = []

stuck :: TransitionRule sig metavar var
stuck constraint = [(mempty, [constraint])]

onlyFreeVar :: IncMany var -> [var]
onlyFreeVar (FreeVar x) = [x]
onlyFreeVar BoundVar{} = []

choose :: [a] -> [(a, [a])]
choose xs =
  [ (y, before ++ after)
  | y:after <- tails xs
  | before <- inits xs
  ]

defaultPreunify
  :: (Matchable sig, Eq var)
  => Int
  -> [Equation sig String var]
  -> UnificationProblem sig String var
  -> [(MetaSubst sig String String var, [Constraint sig String var])]
defaultPreunify maxDepth rules constraints = nub $
  [ (MetaSubst (filter (isOrigMeta . fst) subst), unsolved)
  | (MetaSubst subst, unsolved) <- preunify maxDepth defaultFreshMetaVars rules constraints
  ]
  where
    isOrigMeta = (`elem` origMetas)
    origMetas = foldMap (bifoldMap pure (const [])) constraints

preunify
  :: (Matchable sig, Eq metavar, Eq var)
  => Int
  -> [metavar]
  -> [Equation sig metavar var]
  -> UnificationProblem sig metavar var
  -> [(MetaSubst sig metavar metavar var, [Constraint sig metavar var])]
preunify _ _ _ [] = [(mempty, [])]
preunify 0 _ _ _ = []
preunify maxDepth freshMetaVars rules constraints =
  [ (subst <> finalSubst, unsolvedConstraints)
  | (constraint, otherConstraints) <- choose constraints
  , (subst, newConstraints) <- (decompose <> projectImitate <> mutate scopeMeta freshMetaVars rules) constraint
  , (finalSubst, unsolvedConstraints) <-
      preunify (maxDepth - 1) (freshMetaVars \\ scopeMeta) rules $
        newConstraints ++ map (applyMetaSubstConstraint id (fmap FreeVar subst)) otherConstraints
  ]
  where
    scopeMeta = foldMap (bifoldMap pure (const [])) constraints

defaultFreshMetaVars :: [String]
defaultFreshMetaVars = [ "m" <> show n | n <- [0..]]

-- mutate :: (Matchable sig, Eq var, Eq metavar)
--   => [Equation sig metavar Void] -> Constraint sig metavar var -> [(MetaSubst sig metavar metavar var, [Constraint sig metavar var])]
-- mutate (lhs :==: rhs) = do
--   rule <- rules
--   rhs' <- applyRuleSomewhere rule lhs

-- transition
--   :: (Matchable sig, Eq var, Eq metavar)
--   => Constraint sig metavar var
--   -> [(MetaSubst sig metavar metavar var, [Constraint sig metavar var])]
-- transition = \case
--   -- (delete)
--   lhs :==: rhs
--     | lhs == rhs -> [(mempty, [])]
--   -- (decompose)
--   Free (InL opL) :==: Free (InL opR)
--     | Just opLR <- zipMatch opL opR -> do
--         _ opLR
--   _ -> []

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

pattern Var :: var -> FS sig var
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
      Free (InL (AppF fun arg)) -> "(" ++ go varName freshVars fun ++ ") " ++ "(" ++ go varName freshVars arg ++ ")"
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

identity :: SOAS LambdaF metavar var
identity = LamE (Var Z)

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

example10 :: UnificationProblem LambdaF String var
example10 = [ Constraint
  { constraintEq = M "M" [g, f] :==: AppE g y
  , constraintScope = 2
  } ]
  where
    g = Var (BoundVar 0)
    y = Var (BoundVar 1)
    f = LamE (AppE x (fmap S y))
      where
        x = Var Z

solution10 :: MetaSubst LambdaF String metavar var
solution10 = MetaSubst [ ("M", AppE z2 z1) ]
  where
    z1 = Var (BoundVar 0)
    z2 = Var (BoundVar 1)

checkExample10 :: Bool
checkExample10 = and
  [ lhs == (rhs :: SOAS LambdaF String (IncMany String))
  | constraint <- example10
  , let constraint' = applyMetaSubstConstraint id solution10 constraint
  , lhs :==: rhs <- constraintEq <$> whnfFromRulesConstraint [beta] constraint'
  ]
