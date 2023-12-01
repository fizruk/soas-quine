{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
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
{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use &&" #-}
{-# HLINT ignore "Use ++" #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
module SOAS.Quine where

import Data.Bifunctor ( Bifunctor(first, bimap, second) )
import Data.Bifoldable ( Bifoldable(bifoldMap, bifold) )

import Control.Monad ( (>=>), guard )
import Control.Monad.State hiding (state)
import Free.Scoped
    ( traverseFS, type (:+:), FS(..), Inc(..), Sum(InL, InR), transFS )
import Free.Scoped.TH ( makePatternsAll )
import Data.Bifunctor.TH
    ( deriveBifoldable, deriveBifunctor, deriveBitraversable )
import Data.Void ( Void, absurd )
import Data.Bitraversable ( Bitraversable(..) )
import Data.Maybe (mapMaybe, maybeToList)
import Data.List (intercalate, tails, inits, nub, (\\), sortOn, intersect)
import qualified Debug.Trace
import Data.Foldable (Foldable(toList))
import Data.Monoid (All(..))
import qualified Data.Map as Map

trace :: String -> a -> a
-- trace = Debug.Trace.trace
trace _ = id

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
  deriving (Functor, Foldable)

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
    f args (BoundVar i)
      | i < length args = args !! i
      | otherwise = error $ "index too large (i = " <> show i <> ", length args = " <> show (length args) <> ")"
    f _args (FreeVar x) = Pure x

applyMetaSubstSubst :: (Eq b, Bifunctor sig)
  => (b -> c) -> MetaSubst sig b c var -> MetaSubst sig a b var -> MetaSubst sig a c var
applyMetaSubstSubst rename subst (MetaSubst substs) = MetaSubst
  [ (m, applyMetaSubst rename (fmap FreeVar subst) body)
  | (m, body) <- substs
  ]

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

checkSubst :: (Eq metavar, Eq metavar', Eq var, Matchable sig) => MetaSubst sig metavar metavar' var -> Maybe (MetaSubst sig metavar metavar' var)
checkSubst (MetaSubst []) = return (MetaSubst [])
checkSubst (MetaSubst ((m, body) : substs)) = do
  MetaSubst substs' <- checkSubst (MetaSubst substs)
  case lookup m substs' of
    Just body' | body == body' -> return (MetaSubst substs')
    Nothing -> return (MetaSubst ((m, body) : substs'))
    _ -> Nothing

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
  :: (Matchable sig, Eq metavar, Eq metavar', Eq var)
  => [SOAS sig metavar var]
  -> [var]
  -> SOAS sig metavar' var
  -> [(SOAS sig metavar' (IncMany var), MetaSubst sig metavar metavar' var)]
matchMetaVar args boundVars rhs = projections ++ projectionsBoundVars ++ imitationsInL ++ imitationsInR
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

    imitationsInL =
      [ (Free (InL (first (fmap k) body)), subst)
      | Free (InL opR) <- [rhs]     -- M[A + N[B], C] =?= Π (x : A + B), C x
                                    -- M[X,Y] := Π (x : X), Y x
      , opR' :: sig (SOAS sig metavar' (IncMany (Inc var)), MetaSubst sig metavar metavar' (Inc var))
                    (SOAS sig metavar' (IncMany var), MetaSubst sig metavar metavar' var)
          <- bitraverse (matchMetaVar (fmap (fmap S) args) (Z : fmap S boundVars)) (matchMetaVar args boundVars) opR
      -- opR' = Π (x : (Bound 1, [N[B] := B])), (AppE (S (Bound 2)) Z, [])
      , let body = bimap fst fst opR'
      , op' <- bitraverse (maybeToList . closedSubst . snd) (pure . snd) opR'
      , Just subst <- [checkSubst (bifold op')]
      ]
    imitationsInR =
      [ (Free (InR (MetaVarF m margs')), subst)
      | Free (InR (MetaVarF m margs)) <- [rhs]
      , margsAndSubsts <- traverse (matchMetaVar args boundVars) margs
      , let margs' = map fst margsAndSubsts
      , Just subst <- [checkSubst (foldMap snd margsAndSubsts)]
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
  :: (Matchable sig, Eq metavar, Eq metavar', Eq var)
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
  :: (Matchable sig, Eq metavar, Eq metavar', Eq var)
  => Equation sig metavar var
  -> SOAS sig metavar' var
  -> [SOAS sig metavar' var]
applyRule (lhs :==: rhs) term = do
  subst <- match lhs term
  return (applyMetaSubst (error "impossible happened!") subst rhs)

applyRuleSomewhere
  :: (Matchable sig, Eq metavar, Eq metavar', Eq var)
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
  :: (Matchable sig, Eq metavar, Eq metavar', Eq var)
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
  :: (Matchable sig, Eq metavar, Eq metavar', Eq var)
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
  :: (Matchable sig, Eq metavar, Eq metavar', Eq var)
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

metavarsOf :: Bifoldable sig => SOAS sig metavar var -> [metavar]
metavarsOf Pure{} = []
metavarsOf (Free (InL op)) = bifoldMap metavarsOf metavarsOf op
metavarsOf (Free (InR (MetaVarF m args))) =
  m : foldMap metavarsOf args

varsOf ::  Bifoldable sig => SOAS sig metavar var -> [var]
varsOf = toList

projectImitate'
  :: (Matchable sig, Eq metavar, Eq var)
  => [metavar]
  -> [metavar]
  -> (metavar, [SOAS sig metavar (IncMany var)])
  -> SOAS sig metavar (IncMany var)
  -> Int
  -> [(MetaSubst sig metavar metavar var, [Constraint sig metavar var])]
projectImitate' scopeMeta freshMetaVars (m, args) rhs constraintScope
  | and
    [ all (`notElem` metavarsOf rhs) (metavarsOf lhs)
    , distinct (metavarsOf lhs)
    , all (`elem` varsOf lhs) (varsOf rhs)
    ] =
      [ (MetaSubst [(m, substBody')] <> subst', [])
      | (substBody, subst) <- matchMetaVar args [] rhs
      , substBody' <- traverse (traverse onlyFreeVar) substBody
      , subst' <- traverse onlyFreeVar subst
      ]
  | otherwise = project Constraint{..} <> imitate scopeMeta freshMetaVars Constraint{..}
  where
    distinct xs = xs == nub xs
    lhs = M m args
    constraintEq = lhs :==: rhs

projectImitate :: [metavar] -> [metavar] -> TransitionRule sig metavar var
projectImitate scopeMeta freshMetaVars Constraint{constraintEq = lhs@(M m args) :==: rhs@(M m' args'), ..} =
  mconcat
   [ projectImitate' scopeMeta freshMetaVars (m, args) rhs constraintScope
   , projectImitate' scopeMeta freshMetaVars (m', args') lhs constraintScope ]
projectImitate scopeMeta freshMetaVars Constraint{constraintEq = M m args :==: rhs, ..} =
  projectImitate' scopeMeta freshMetaVars (m, args) rhs constraintScope
projectImitate scopeMeta freshMetaVars Constraint{constraintEq = lhs :==: M m args, ..} =
  projectImitate' scopeMeta freshMetaVars (m, args) lhs constraintScope
projectImitate _ _ _ = []

eliminateMetaVar :: TransitionRule sig metavar var
eliminateMetaVar Constraint{constraintEq = M{} :==: M{}, ..} = []
eliminateMetaVar Constraint{constraintEq = lhs@(M m args) :==: rhs, ..}
  | and
    [ all isVar args
    -- , distinct args
    , m `notElem` metavarsOf rhs
    , all (`elem` varsOf lhs) (varsOf rhs) ] =
      [ (MetaSubst [(m, substBody')] <> subst', [])
      | (substBody, subst) <- matchMetaVar args [] rhs
      , substBody' <- traverse (traverse onlyFreeVar) substBody
      , subst' <- traverse onlyFreeVar subst
      ]
  where
    isVar Pure{} = True
    isVar _ = False
    -- isConst = null . metavarsOf
    distinct xs = xs == nub xs
eliminateMetaVar Constraint{constraintEq = lhs :==: rhs@(M m args), ..} =
  eliminateMetaVar Constraint{constraintEq = rhs :==: lhs, ..}
eliminateMetaVar _ = []


-- forall k. (λ x. k M6[x, k]) M3[k] =?= M6[M3[k],k]
imitate :: [metavar] -> [metavar] -> TransitionRule sig metavar var
imitate scopeMeta freshMetaVars Constraint{constraintEq = M m args :==: Free (InL rhs), ..} = do
  -- ∀ z1, ..., zN.  M[a1, ..., aM] =?= F(t1, x.t2)
  -- M[x1, ..., xM] := F(M1[x1, ..., xM], x.M2[x, x1, ..., xM])
  let args' = [ Pure (BoundVar i) | i <- [0 .. length args - 1] ]
      fresh _ = do
        x <- gets head
        modify tail
        return (M x args')
      freshScope _ = do
        x <- gets head
        modify tail
        return (M x (Pure Z : map (fmap S) args'))
      m' = flip evalState (freshMetaVars \\ scopeMeta) $
        bitraverse freshScope fresh rhs
      subst = MetaSubst [(m, Free (InL m'))]
      lhs = applyMetaSubst id subst (M m args)
      rhs' = applyMetaSubst id subst (Free (InL rhs))
  return (subst, [Constraint{constraintEq = lhs :==: rhs', ..}])
imitate _ _ _ = []

project :: TransitionRule sig metavar var
project Constraint{constraintEq = M m args :==: rhs, ..} =
  [ (subst, [Constraint{constraintEq = arg' :==: rhs', ..}])
  | (i, arg) <- zip [0..] args
  , let subst = MetaSubst [(m, Pure (BoundVar i))]
  , let arg' = applyMetaSubst id subst arg
  , let rhs' = applyMetaSubst id subst rhs
  ]
project _ = []

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

mutate' :: Ord metavar => [Equation sig metavar var] -> [metavar] -> [metavar] -> TransitionRule sig metavar var
mutate' rules scopeMeta freshMetaVars Constraint{constraintEq = lhs :==: rhs, ..} = mconcat
  [ mutateWith rule' scopeMeta freshMetaVars c
  | rule <- rules
  , rule' <- [rule, sym rule]
  , c <- [ Constraint{constraintEq = lhs :==: rhs, ..}
         , Constraint{constraintEq = rhs :==: lhs, ..} ]
  ]
  where
    sym (x :==: y) = y :==: x

mutateWith :: (Ord metavar, Bifunctor sig) => Equation sig metavar var -> [metavar] -> [metavar] -> TransitionRule sig metavar var
mutateWith rule scopeMeta freshMetaVars Constraint{constraintEq = lhs :==: rhs, ..} = do
  let refreshedRule = refreshAllMetaVarsEquation scopeMeta freshMetaVars rule
  let instantiatedRule = addVarArgsEquation [BoundVar i | i <- [0 .. constraintScope - 1]] (FreeVar <$> refreshedRule)
  let ruleLHS :==: ruleRHS = instantiatedRule
  Free InL{} <- [ruleLHS]
  (allowedVars, decomposedLHS) <- matchAxiomPart ruleLHS lhs
  let allowedVars' = Map.toList (Map.fromListWith intersect allowedVars)
  let newConstraints = decomposedLHS ++ [ Constraint{constraintEq = ruleRHS :==: rhs, ..} ]
  return (mempty, map (keepAllowedVars allowedVars') newConstraints)
  where
    keepAllowedVars :: (Eq metavar, Bifunctor sig) => [(metavar, [Int])] -> Constraint sig metavar var -> Constraint sig metavar var
    keepAllowedVars vars Constraint{constraintEq = lhs' :==: rhs', ..} =
      Constraint{constraintEq = keepAllowedVars' vars lhs' :==: keepAllowedVars' vars rhs', ..}

    keepAllowedVars' :: (Eq metavar, Bifunctor sig) => [(metavar, [Int])] -> SOAS sig metavar var -> SOAS sig metavar var
    keepAllowedVars' _ t@Pure{} = t
    keepAllowedVars' vars (Free (InL op)) = Free (InL (bimap (keepAllowedVars' vars) (keepAllowedVars' vars) op))
    keepAllowedVars' vars (Free (InR (MetaVarF m args))) =
      Free (InR (MetaVarF m (map snd $ filter isAllowed (zip [0..] (map (keepAllowedVars' vars) args)))))
      where
        isAllowed (j, Pure{})
          | j < constraintScope
          , Just vars' <- lookup m vars
          = j `elem` vars'
        isAllowed _ = True

    matchAxiomPart
      :: (ZipMatch sig, Bitraversable sig)
      => SOAS sig metavar (IncMany var)
      -> SOAS sig metavar (IncMany var)
      -> [([(metavar, [Int])], [Constraint sig metavar var])]
    matchAxiomPart (Free (InL l)) (Free (InL r)) = do
      Just lr <- [zipMatch l r]
      lr' <- bitraverse (map (second (map extendConstraint)) . uncurry matchAxiomPart' . bimap (fmap k) (fmap k)) (uncurry matchAxiomPart') lr
      return (bifold lr')
      where
        matchAxiomPart' (Free InL{}) Pure{} = []
        matchAxiomPart' l' r' =
          return ([ (ml, foldMap toBoundIndex (varsOf r')) | ml <- metavarsOf l'], [Constraint (l' :==: r') constraintScope])
    matchAxiomPart l@(Free InL{}) r@(Free InR{}) =
      return ([ (ml, foldMap toBoundIndex (varsOf r)) | ml <- metavarsOf l], [Constraint (l :==: r) constraintScope])
    matchAxiomPart (Free InL{}) Pure{} = []
    matchAxiomPart l r = return ([], [Constraint (l :==: r) constraintScope])

    k :: Inc (IncMany a) -> IncMany (Inc a)
    k Z = FreeVar Z
    k (S (BoundVar i)) = BoundVar i
    k (S (FreeVar x)) = FreeVar (S x)

    toBoundIndex (BoundVar i) = [i]
    toBoundIndex _ = []

extendConstraint :: Bifunctor sig => Constraint sig metavar (Inc var) -> Constraint sig metavar var
extendConstraint Constraint{..} = Constraint
  { constraintEq = fmap k constraintEq
  , constraintScope = 1 + constraintScope}
  where
    k (FreeVar Z) = BoundVar constraintScope
    k (FreeVar (S x)) = FreeVar x
    k (BoundVar i) = BoundVar i

matchingRoots :: (Bifoldable sig, ZipMatch sig) => SOAS sig metavar var -> SOAS sig metavar var' -> Bool
matchingRoots (Free (InL l)) (Free (InL r))
  | Just lr <- zipMatch l r = getAll (bifoldMap (All . uncurry matchingRoots) (All . uncurry matchingRoots) lr)
matchingRoots (Free InL{}) (Free InR{}) = True
matchingRoots _ _ = False

mutate :: [Equation sig metavar var] -> [metavar] -> [metavar] -> TransitionRule sig metavar var
mutate rules scopeMeta freshMetaVars Constraint{constraintEq = lhs :==: rhs, ..} = do
  rule@(lhsOrig :==: rhsOrig) <- rules
  let refreshedRule = refreshAllMetaVarsEquation scopeMeta freshMetaVars rule
  let instantiatedRule = addVarArgsEquation [BoundVar i | i <- [0 .. constraintScope - 1]] (FreeVar <$> refreshedRule)
  let ruleLHS :==: ruleRHS = instantiatedRule
  concat
    [ do
        guard (matchingRoots lhsOrig lhs || matchingRoots rhsOrig rhs)
        return (mempty,
          [ Constraint{constraintEq = lhs :==: ruleLHS, ..}
          , Constraint{constraintEq = ruleRHS :==: rhs, ..} ])
    , do
        guard (matchingRoots lhsOrig rhs || matchingRoots rhsOrig lhs)
        return (mempty,
          [ Constraint{constraintEq = rhs :==: ruleLHS, ..}
          , Constraint{constraintEq = ruleRHS :==: lhs, ..} ])
    ]

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

orElse :: [a] -> [a] -> [a]
orElse [] ys = ys
orElse xs _ = xs

searchWith
  :: (Monoid m, Eq m, Show a, Show m)
  => [String]                           -- hints for rule application
  -> (Int, [(String, Int)])             -- limits for the search
  -> state                              -- internal state
  -> (m -> a -> a)                      -- update function
  -> [[(String, state -> a -> [(Int, (state, (m, [a])))])]] -- transition rules, in priority groups
  -> [a]                                -- initial constraints
  -> [(m, [a])]                         -- result
searchWith = go 0
  where
    go depth hints (maxDepth, limits) state update rules xs
      | null xs = [(mempty, [])]
      | maxDepth <= depth = []
      | otherwise = do
          -- identify rules that cannot be used anymore
          let deadRules = [ name | (name, 0) <- limits]
          -- remove "dead" rules
          let liveRuleGroups = map (filter ((`notElem` deadRules) . fst)) rules

          branches <-
            -- branch only using rules for the first priority group with any transitions
            take 1 $ dropWhile (all null)
              [ sortOn (length . take 3)  -- prioritise non-branching rules
                  [ [ (name, x, y, xs')
                    | (name, rule) <- liveRules
                    , y <- rule state x -- `orElse` trace (replicate depth ' ' <> "- FAIL (" <> name <> ") for " <> show x) []
                    ]
                  | (x, xs') <- choose xs ]
              | liveRules <- liveRuleGroups ]

          -- should this be enabled?
          -- guard $ not (any null branches)

          branch <- branches
          (name, x, (_priority, (state', (m, ys))), xs') <-
            sortOn (\(_, _, (priority, _), _) -> priority)
              branch

          -- follow hints, if provided
          hints' <- case hints of
            [] -> return []
            hint : hints' -> do
              guard (name == hint)
              return hints'

          -- trace search path
          trace (replicate depth ' ' <> "- (" <> name <> ")") $
            trace (replicate depth ' ' <> "  " <> show x) $
            (if m == mempty then id else trace (replicate depth ' ' <> "  " <> show m <> ")")) $ do
              (if null ys then id else trace (replicate depth ' ' <> "  " <> show ys <> ")")) $ do
                -- solve the rest
                let limits' = updateAt name (subtract 1) limits
                (m', zs) <- go (depth + 1) hints' (maxDepth, limits') state' update liveRuleGroups (ys ++ map (update m) xs')
                return (m <> m', zs)

updateAt :: Eq k => k -> (v -> v) -> [(k, v)] -> [(k, v)]
updateAt _ _ [] = []
updateAt k f ((k', v) : kvs)
  | k == k' = (k', f v) : kvs
  | otherwise = (k', v) : updateAt k f kvs

defaultPreunify
  :: (Matchable sig, Eq var
  , forall scope term. (Show scope, Show term) => Show (sig scope term)
  , Show var)
  => (Int, Int)
  -> [Equation sig String var]
  -> UnificationProblem sig String var
  -> [(MetaSubst sig String String var, [Constraint sig String var])]
defaultPreunify (maxDepth, maxMutate) rules constraints = nub $
  [ (MetaSubst (filter (isOrigMeta . fst) subst), unsolved)
  | (MetaSubst subst, unsolved) <- preunify [] (maxDepth, maxMutate) origMetas defaultFreshMetaVars rules constraints
  ]
  where
    isOrigMeta = (`elem` origMetas)
    origMetas = foldMap (bifoldMap pure (const [])) constraints

defaultGuidedPreunify
  :: (Matchable sig, Eq var
  , forall scope term. (Show scope, Show term) => Show (sig scope term)
  , Show var)
  => [String]
  -> (Int, Int)
  -> [Equation sig String var]
  -> UnificationProblem sig String var
  -> [(MetaSubst sig String String var, [Constraint sig String var])]
defaultGuidedPreunify guide (maxDepth, maxMutate) rules constraints = nub $
  [ (MetaSubst (filter (isOrigMeta . fst) subst), unsolved)
  | (MetaSubst subst, unsolved) <- preunify guide (maxDepth, maxMutate) origMetas defaultFreshMetaVars rules constraints
  ]
  where
    isOrigMeta = (`elem` origMetas)
    origMetas = foldMap (bifoldMap pure (const [])) constraints

preunify
  :: (Matchable sig, Ord metavar, Eq var
  , forall scope term. (Show scope, Show term) => Show (sig scope term)
  , Show var, Show metavar)
  => [String]
  -> (Int, Int)
  -> [metavar]
  -> [metavar]
  -> [Equation sig metavar var]
  -> UnificationProblem sig metavar var
  -> [(MetaSubst sig metavar metavar var, [Constraint sig metavar var])]
preunify hints (maxDepth, maxMutate) scopeMeta freshMetaVars axioms constraints = do
  (MetaSubst substs, unsolved) <- searchWith hints
    (maxDepth, [("mutate", maxMutate)])
    (targetMetas, scopeMeta, freshMetaVars)
    (applyMetaSubstConstraint id . fmap FreeVar)
    rules'
    constraints
  let substs' = foldr (\ m s -> applyMetaSubstSubst id s (MetaSubst [m]) <> s) mempty substs
  return (substs', unsolved)
  where
    targetMetas = foldMap (bifoldMap pure (const [])) constraints

    rules' =
      [ -- try (delete) when possible
        [ ("delete", stateless delete) ]
        -- then (eliminate*) when possible
      , [ ("eliminate*", stateless eliminateMetaVar) ]
        -- else, try (decompose), (project), (imitate), and (mutate)
      , [ ("decompose", stateless decompose)
        -- , ("project/imitate", auto projectImitate)
        -- , ("eliminate*", stateless eliminateMetaVar)
        , ("imitate", auto imitate)
        , ("project", stateless project)
        , ("mutate", auto (mutate' axioms))
        ]
      ]

    stateless
      :: (a -> [(m, [a])])
      -> state
      -> a
      -> [(Int, (state, (m, [a])))]
    stateless f state x =
      [ (-100, (state, y)) | y <- f x ]

auto
  :: (Matchable sig, Eq metavar, Eq var)
  => ([metavar] -> [metavar] -> Constraint sig metavar var -> [(MetaSubst sig metavar metavar var, [Constraint sig metavar var])])
  -> ([metavar], [metavar], [metavar])
  -> Constraint sig metavar var
  -> [(Int, (([metavar], [metavar], [metavar]), (MetaSubst sig metavar metavar var, [Constraint sig metavar var])))]
auto f (targets, scope, fresh) x =
  [ (priority, (state', (subst, newConstraints)))
  | (subst, newConstraints) <- f scope fresh x
  , let new = foldMap (metavarsOf . snd) (getMetaSubsts subst) <> foldMap (bifoldMap pure (const [])) newConstraints
  , let isTargetSubst = (`elem` targets) . fst
  , let targetSubsts = filter isTargetSubst (getMetaSubsts subst)
  , let priority
          | subst == mempty = -50
          | otherwise = negate (length targetSubsts)
  , let newTargets = foldMap (metavarsOf . snd) targetSubsts
  , let targets' = nub (targets <> newTargets)
  , let state' = (targets', nub (new <> scope), fresh \\ new)
  ]

    -- tryDecompose :: (Eq metavar, Eq var, Matchable sig) => Constraint sig metavar var -> [Constraint sig metavar var]
    -- tryDecompose c@Constraint{ constraintEq = Free InL{} :==: Free InL{} } = concatMap snd (decompose c)
    -- tryDecompose c = [c]

-- preunify _ _ _ _ _ [] = [(mempty, [])]
-- preunify _ (n, _) _ _ _ _cs | n < 0 = [] -- [(mempty, cs)]
-- preunify guide (maxDepth, maxMutate) scopeMeta freshMetaVars rules constraints = do
--   (constraint, otherConstraints) <- choose constraints
--   case delete constraint of
--     _:_ -> trace (replicate (30 - maxDepth) ' ' <> "- (delete) " <> ppConstraint constraint) $ do
--       newGuide <- case guide of
--         [] -> return []
--         action : actions -> do
--           guard ("delete" == action)
--           return actions
--       preunify newGuide (maxDepth - 1, maxMutate) scopeMeta (freshMetaVars \\ scopeMeta) rules otherConstraints
--     [] -> do
--       (name, trans) <-
--         [ ("decompose",       decompose)
--         , ("project/imitate", projectImitate scopeMeta freshMetaVars)
--         , ("mutate",          mutate scopeMeta freshMetaVars rules)]
--       newGuide <- case guide of
--         [] -> return []
--         action : actions -> do
--           guard (name == action)
--           return actions
--       let (newMaxDepth, newMaxMutate)
--             | name == "mutate" = (maxDepth - 1, maxMutate - 1)
--             | otherwise = (maxDepth - 1, maxMutate)
--       guard $ (name /= "mutate") || maxMutate > 0
--       (subst, newConstraints) <- trans constraint
--       let newScopeMeta = foldMap (metavarsOf . snd) (getMetaSubsts subst) <> foldMap (bifoldMap pure (const [])) newConstraints
--       let constraints' = newConstraints ++ map (applyMetaSubstConstraint id (fmap FreeVar subst)) otherConstraints
--       let scopeMeta' = nub (scopeMeta <> newScopeMeta)
--       (finalSubst, unsolvedConstraints) <-
--         trace (replicate (30 - maxDepth) ' ' <> "- [" <> show (maxDepth, maxMutate) <> "] (" <> name <> ")") $
--         trace (replicate (30 - maxDepth) ' ' <> "  " <> show constraint) $
--         (if null newConstraints then id else trace (replicate (30 - maxDepth) ' ' <> "  NEW: " <> show newConstraints)) $
--         (if subst == mempty then id else trace (replicate (30 - maxDepth) ' ' <> "  " <> show subst)) $ do
--           when (not (distinct (map fst (getMetaSubsts subst)))) $
--             error $ "impossible:\n" <> unlines
--               [ "subst = " <> show subst
--               , "newConstraints = " <> show newConstraints
--               , "scopeMeta = " <> show scopeMeta
--               ]
--           preunify newGuide (newMaxDepth, newMaxMutate) scopeMeta' (freshMetaVars \\ scopeMeta') rules constraints'
--       return (applyMetaSubstSubst id finalSubst subst <> finalSubst, unsolvedConstraints)
--       where
--         distinct xs = xs == nub xs

ppConstraint :: (Show var, Show metavar, forall scope term. (Show scope, Show term) => Show (sig scope term)) => Constraint sig metavar var -> String
ppConstraint Constraint{constraintEq = (lhs :==: rhs), ..} = "∀" <> show constraintScope <> ". " <> show lhs <> "  =?=  " <> show rhs

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

instance {-# OVERLAPPING #-} Show var => Show (Equation LambdaF String var) where
  show (lhs :==: rhs) = show lhs <> " :==: " <> show rhs

instance {-# OVERLAPPING #-} Show var => Show (Constraint LambdaF String var) where
  show (Constraint (lhs :==: rhs) n) = "∀" <> show n <> ". " <> show lhs <> " :=?=: " <> show rhs

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

-- λ f. (λ x. f (x x)) (λ x. f (x x))
--
-- DEMO:
-- (λ f. (λ x. f (x x)) (λ x. f (x x))) F
-- = ...
-- = F ((λ f. (λ x. f (x x)) (λ x. f (x x))) F)
-- = F ((λ x. F (x x)) (λ x. F (x x)))
--
-- >>> whnfFromRules [addVarArgsEquation [Z] beta] (AppE untypedFix (Var Z)) :: [SOAS LambdaF String (Inc String)]
-- [(Z) ((λ x1 . (Z) ((x1) (x1))) (λ x1 . (Z) ((x1) (x1))))]
untypedFix :: SOAS LambdaF metavar var
untypedFix = LamE (AppE tt tt)
  where
    tt = LamE (AppE f (AppE x x))
    f = Var (S Z)
    x = Var Z

-- (\ z. M[z]) N[] = M[N[]]
beta :: Equation LambdaF String var
beta = AppE (LamE (M "M" [Var Z])) (M "N" []) :==: M "M" [M "N" []]

-- (\ z. M[z]) N[] = M[N[]]
eta :: Equation LambdaF String var
eta = LamE (AppE (M "M" []) (Var Z)) :==: M "M" []

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

solveId :: (Eq var, Show var) => [SOAS LambdaF String (IncMany var)]
solveId =
  [ body
  | (MetaSubst subst, _unsolved) <- defaultPreunify (100, 3) [beta]
      [Constraint{ constraintEq = e, constraintScope = 1}]
  , Just body <- [lookup "ID" subst]
  ]
  where
    -- forall x. ID[] x == x
    -- (mutate) — new meta variables m0 and m1
    -- forall x. ID[] x = (λ z. m0[x,z]) m1[x]
    -- forall x. m0[x,m1[x]] = x
    -- (decompose)
    -- forall x. ID[] = (λ z. m0[x,z])
    -- forall x. x = m1[x]
    -- forall x. m0[x,m1[x]] = x
    -- (project/imitate) m0[x1,x2] := x1 [FAIL]
    -- (project/imitate) m0[x1,x2] := x2; m1[x1] := x1
    -- forall x. ID[] = (λ z. z)
    -- forall x. x = x
    -- (project/imitate) ID[] := (λ z. z)
    -- forall x. x = x
    -- (delete)
    e = AppE (M "ID" []) (Var (BoundVar 0)) :==: Var (BoundVar 0)

solveConst :: (Eq var, Show var) => [SOAS LambdaF String (IncMany var)]
solveConst =
  [ body
  | (MetaSubst subst, _unsolved) <- defaultPreunify (100, 3) [beta]
      [Constraint{ constraintEq = e, constraintScope = 2}]
  , Just body <- [lookup "CONST" subst]
  ]
  where
    e = AppE (AppE mCONST x) y :==: x
    mCONST = M "CONST" []
    x = Var (BoundVar 0)
    y = Var (BoundVar 1)

-- TOO SLOW, no answer in reasonable time
solveFix :: (Eq var, Show var) => [SOAS LambdaF String (IncMany var)]
solveFix =
  [ body
  -- | (MetaSubst subst, _unsolved) <- defaultPreunify (25, 3) [beta]
  --     [Constraint{ constraintEq = e, constraintScope = 1}]
  | (MetaSubst subst, _unsolved) <- defaultPreunify (22, 3) [beta]
      [ Constraint{ constraintEq = e, constraintScope = 1} ]
  , Just body <- [lookup "FIX" subst]
  ]
  where
    -- FIX[] := λ f. M1[f]
    --       := λ f. M2[f] M3[f]
    --       := λ f. (λ x. M4[x, f]) M3[f]
    --       := λ f. (λ x. M5[x, f] M6[x, f]) M3[f]
    --       := λ f. (λ x. f M6[x, f]) M3[f]
    --       := λ f. (λ x. f M6[x, f]) M3[f]

    --
    -- forall k. FIX[] k =?= k (FIX[] k)
    -- + (mutate + decompose) FIX[] := λ f. M1[f]
    -- forall k. M1[k] =?= k ((λ f. M1[f]) k)
    -- + (imitate) M1[k] := M2[k] M3[k]
    -- forall k. M2[k] M3[k] =?= k ((λ f. M2[f] M3[f]) k)
    -- + (mutate + decompose) M2[x1] := λ x. M4[x,x1]
    -- forall k. M4[M3[k],k] =?= k ((λ f. (λ x. M4[x, f]) M3[f]) k)
    -- + (imitate) M4[x1,x2] := M5[x1,x2] M6[x1,x2]
    -- forall k. M5[M3[k],k] M6[M3[k],k] =?= k ((λ f. (λ x. M5[x, f] M6[x, f]) M3[f]) k)
    -- + (decompose)
    -- forall k. M5[M3[k],k] =?= k
    -- forall k. M6[M3[k],k] =?= (λ f. (λ x. M5[x, f] M6[x, f]) M3[f]) k
    -- + (project/imitate) M5[x1,x2] := x2
    -- forall k. M6[M3[k],k] =?= (λ f. (λ x. f M6[x, f]) M3[f]) k
    -- + (mutate RHS)
    -- forall k. (λ f. (λ x. f M6[x, f]) M3[f]) k =?= (λ x. B1[x, k]) B2[k]
    -- forall k. B1[B2[k],k] =?= M6[M3[k],k]
    -- + (decompose)
    -- forall k. λ f. (λ x. f M6[x, f]) M3[f] =?= (λ x. B1[x, k]
    -- forall k. k =?= B2[k]
    -- forall k. B1[B2[k],k] =?= M6[M3[k],k]
    -- + (decompose)
    -- forall k f. (λ x. f M6[x, f]) M3[f] =?= B1[f, k]
    -- forall k. k =?= B2[k]
    -- forall k. B1[B2[k],k] =?= M6[M3[k],k]
    -- + (project/imitate) B1[x1,x2] := (λ x. x1 M6[x, x1]) M3[x1]
    -- forall k. k =?= B2[k]
    -- forall k. (λ x. B2[k] M6[x, B2[k]]) M3[B2[k]] =?= M6[M3[k],k]
    -- + (project/imitate) B2[x1] := x1
    -- forall k. (λ x. k M6[x, k]) M3[k] =?= M6[M3[k],k]                          -- fails
    -- + (imitate) M6[x1, x2] := M7[x1,x2] M8[x1,x2]
    -- forall k. (λ x. k (M7[x, k] M8[x, k])) M3[k] =?= M7[M3[k],k] M8[M3[k],k]   -- works
    -- + (decompose)
    -- forall k. (λ x. k (M7[x, k] M8[x, k])) =?= M7[M3[k],k]
    -- forall k. M3[k] =?= M8[M3[k],k]
    -- + (project) M7[x1,x2] := x1
    -- forall k. (λ x. k (x M8[x, k])) =?= M3[k]
    -- forall k. M3[k] =?= M8[M3[k],k]
    -- + (project/imitate) M3[x1] := (λ x. x1 (x M8[x, x1]))
    -- forall k. λ x. k (x M8[x, k]) =?= M8[λ x. k (x M8[x, k]),k]
    -- + (project) M8[x1,x2] := x1
    -- forall k. λ x. k (x x) =?= λ x. k (x x)
    -- + (delete)

    -- forall k. FIX[] k =?= k (FIX[] k)
    e = AppE mFIX f :==: AppE f (AppE mFIX f)
    mFIX = M "FIX" []
    f = Var (BoundVar 0)

    -- forall k. M7[M3[k],k] M8[M3[k],k] =?= (λ x. k (M7[x, k] M8[x, k])) M3[k]
    -- e = AppE (LamE (AppE (fmap S k) (AppE (M "M7" [x, fmap S k]) (M "M8" [x, fmap S k])))) (M "M3" [k])
    --       :==: AppE (M "M7" [M "M3" [k], k]) (M "M8" [M "M3" [k], k])
    -- k = Var (BoundVar 0)
    -- x = Var Z

    -- forall k. M6[M3[k],k] =?= (λ f. (λ x. f M6[x, f]) M3[f]) k
    -- e = M "M6" [M "M3" [k], k] :==: AppE (LamE (AppE (LamE (AppE (fmap S f) (M "M6" [x, fmap S f]))) (M "M3" [f]))) k
    -- f = Var Z
    -- x = Var Z
    -- k = Var (BoundVar 0)

    -- -- forall k. (λ f. (λ x. f M6[x, f]) M3[f]) k =?= (λ x. B1[x, k]) B2[k]
    -- -- forall k. B1[B2[k],k] =?= M6[M3[k],k]
    -- e1 = AppE (LamE (AppE (LamE (AppE f (M "M6" [x, fmap S f]))) (M "M3" [f]))) k
    --       :==: AppE (LamE (M "B1" [x, fmap S k])) (M "B2" [k])
    -- e2 = M "B1" [M "B2" [k], k] :==: M "M6" [M "M3" [k], k]

    -- -- forall k. (λ x. k (x M8[x, k])) =?= M3[k]
    -- e' = LamE (AppE (fmap S k) (AppE x (M "M8" [x, fmap S k]))) :==: M "M3" [k]

testProject :: [(MetaSubst LambdaF String String String, [Constraint LambdaF String String])]
testProject = defaultPreunify (10, 0) [] [c]
  where
    -- forall x y. M[x, y x] =?= x M[y, x]
    -- + (imitate) M[x1, x2] := M1[x1,x2] M2[x1,x2]
    -- forall x y. M1[x, y x] M2[x, y x] =?= x (M1[y, x] M2[y, x])
    -- + (decompose)
    -- forall x y. M1[x, y x] =?= x
    -- forall x y. M2[x, y x] =?= M1[y, x] M2[y, x]
    -- + (project/imitate) M1[x1,x2] := x1
    -- forall x y. M2[x, y x] =?= y M2[y, x]
    -- + (project) M2[x1,x2] := x2
    -- forall x y. y x =?= y x
    -- + (delete)

    --
    -- M[x1, x2] := x1 x2
    c = Constraint (lhs :==: rhs) 2
    lhs = M "M" [x, AppE y x]
    rhs = AppE x (M "M" [y, x])
    x = Var (BoundVar 0)
    y = Var (BoundVar 1)
