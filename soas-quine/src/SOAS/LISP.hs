{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE RecordWildCards            #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use &&" #-}
{-# HLINT ignore "Use ++" #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
module SOAS.LISP where

import           Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor,
                                    deriveBitraversable)
import           Data.List         (intercalate)
import           Free.Scoped
import           Free.Scoped.TH    (makePatternsAll)

import           SOAS.Quine

data LispF scope term
  = NilF
  | ConsF term term
  | LambdaF scope
  | EvalF term
  | SymbolF String
  deriving (Eq, Show, Functor, Foldable, Traversable)
deriveBifunctor ''LispF
deriveBifoldable ''LispF
deriveBitraversable ''LispF
makePatternsAll ''LispF

instance {-# OVERLAPPING #-} Show var => Show (LispE String var) where
  show = ppLispE defaultVars . fmap show
    where
      defaultVars = [ "x" <> show n | n <- [1..] ]

instance {-# OVERLAPPING #-} Show var => Show (Equation LispF String var) where
  show (lhs :==: rhs) = show lhs <> " :==: " <> show rhs

ppLispE :: [String] -> LispE String String -> String
ppLispE = go id
  where
    ppArgs :: (var -> String) -> [String] -> LispE String var -> String
    ppArgs varName freshVars = \case
      Free (InL (ConsF arg (Free (InL NilF)))) ->
        " " ++ go varName freshVars arg
      Free (InL (ConsF arg args@(Free (InL ConsF{})))) ->
        " " ++ go varName freshVars arg ++ ppArgs varName freshVars args
      Free (InL (ConsF arg args)) ->
        " " ++ go varName freshVars arg ++ ppArgs varName freshVars args
      Free (InL NilF) -> ""
      arg -> " . " ++ go varName freshVars arg

    go :: (var -> String) -> [String] -> LispE String var -> String
    go varName freshVars = \case
      Pure x -> varName x
      Free (InR (MetaVarF m args)) -> m ++ "[" ++ intercalate "," (map (go varName freshVars) args) ++  "]"
      Free (InL NilF) -> "()"
      Free (InL (ConsF fun args)) ->
        "(" ++ go varName freshVars fun ++ ppArgs varName freshVars args ++ ")"
      Free (InL (LambdaF body)) -> withScope $ \ z zs varName' ->
        "(lambda (" ++ z ++ ") " ++ go varName' zs body ++ ")"
      Free (InL (EvalF e)) -> "(eval " ++ go varName freshVars e ++ ")"
      Free (InL (SymbolF sym)) -> sym
      where
        withScope f = case freshVars of
          [] -> error "not enough fresh variables"
          z:zs ->
            let varName' Z     = z
                varName' (S x) = varName x
            in f z zs varName'

type Lisp = FS LispF
type LispE metavar var = SOAS LispF metavar var
instance ZipMatch LispF where
  zipMatch NilF NilF
    = Just NilF
  zipMatch (ConsF h1 t1) (ConsF h2 t2)
    = Just (ConsF (h1, h2) (t1, t2))
  zipMatch (LambdaF body1) (LambdaF body2)
    = Just (LambdaF (body1, body2))
  zipMatch (EvalF term1) (EvalF term2)
    = Just (EvalF (term1, term2))
  zipMatch (SymbolF s1) (SymbolF s2)
    | s1 == s2 = Just (SymbolF s1)
    | otherwise = Nothing
  zipMatch _ _ = Nothing

{-
RULES:
eval nil ≡ nil                                                 (0)
eval (cons (symbol ("quote"), cons(M[], nil))) ≡ M[]           (i)
eval (cons (lambda (x. B[x]), cons(A[], nil))) ≡ eval(B[A[]])  (ii)
eval (cons (symbol ("list"), nil)) ≡ nil                       (iii.0) -- `list` evaluates its arguments
eval (cons (symbol ("list"), cons(A[], nil)))
  ≡ cons(eval(A[]), nil)                                       (iii.1)
eval (cons (symbol ("list"), cons(A[], cons(B[], nil))))
  ≡ cons(eval(A[]), cons(eval(B[]), nil))                      (iii.2)
-}
lispEvalRules :: [Equation LispF String var]
lispEvalRules =
  [  --EvalE NilE :==: NilE
    -- EvalE (ConsE (SymbolE "quote") (ConsE (M "M" []) NilE)) :==: M "M" []
  -- , EvalE (ConsE (SymbolE "list") NilE) :==: NilE
  -- , EvalE (ConsE (SymbolE "list") (ConsE (M "A" []) NilE)) :==: ConsE (M "A" []) NilE
   EvalE (ConsE (SymbolE "list") (ConsE (M "A" []) (ConsE (M "B" []) NilE))) :==: ConsE (M "A" []) (ConsE (M "B" []) NilE)
  , EvalE (ConsE (LambdaE (M "B" [Var Z])) (ConsE (M "A" []) NilE)) :==: EvalE (M "B" [M "A" []])
  -- , EvalE (ConsE (ConsE (M "A" []) (M "B" [])) (M "C" [])) :==: EvalE (ConsE (EvalE (ConsE (M "A" []) (M "B" []))) (M "C" []))
  ]

solveQuine :: (Eq var, Show var) => [SOAS LispF String (IncMany var)]
solveQuine =
  [ body
  | (MetaSubst subst, _unsolved) <- defaultPreunify (15, 3) lispEvalRules
      [Constraint{ constraintEq = e, constraintScope = 0}]
  , Just body <- [lookup "QUINE" subst]
  ]
  where
    -- QUINE := (λ x. M1[x]) : M2[] : nil

    -- eval QUINE[] =?= QUINE
    -- + () QUINE[] := (λ x. M1[x]) : M2[] : nil
    -- eval ((λ x. M1[x]) : M2[] : nil) =?= (λ x. M1[x]) : M2[] : nil
    -- + ()
    -- eval (M1[M2[]]) =?= (λ x. M1[x]) : M2[] : nil
    -- + () M1[x1] := "list" : M3[x1] : M4[x1] : nil
    -- eval ("list" : M3[M2[]] : M4[M2[]] : nil) =?= (λ x. "list" : M3[x] : M4[x] : nil) : M2[] : nil
    -- + ()
    -- eval ("list" : M3[M2[]] : M4[M2[]] : nil) =?= (λ x. "list" : M3[x] : M4[x] : nil) : M2[] : nil
    -- + ()
    -- eval M3[M2[]] : eval M4[M2[]] : nil =?= (λ x. "list" : M3[x] : M4[x] : nil) : M2[] : nil
    -- + (decompose + delete nil)
    -- eval M3[M2[]] =?= λ x. ("list" : M3[x] : M4[x] : nil)
    -- eval M4[M2[]] =?= M2[]
    -- (project) M3[x1] := x1
    -- eval M2[] =?= λ x. ("list" : x : M4[x] : nil)
    -- eval M4[M2[]] =?= M2[]
    -- + () M4[x1] := "list" : M5[x1] : M6[x1] : nil
    -- eval M2[] =?= λ x. ("list" : x : ("list" : M5[x] : M6[x] : nil) : nil)
    -- eval ("list" : M5[M2[]] : M6[M2[]] : nil) =?= M2[]
    -- + ()
    -- eval M2[] =?= λ x. ("list" : x : ("list" : M5[x] : M6[x] : nil) : nil)
    -- eval M5[M2[]] : eval M6[M2[]] : nil =?= M2[]
    -- + (project) M6[x1] := x1
    -- eval M2[] =?= λ x. ("list" : x : ("list" : M5[x] : x : nil) : nil)
    -- eval M5[M2[]] : eval M2[] : nil =?= M2[]
    -- + () M2[] := quote M7[]
    -- eval (quote M7[]) =?= λ x. ("list" : x : ("list" : M5[x] : x : nil) : nil)
    -- eval M5[quote M7[]] : eval (quote M7[]) : nil =?= quote M7[]
    -- + ()
    -- M7[] =?= λ x. ("list" : x : ("list" : M5[x] : x : nil) : nil)
    -- eval M5[quote M7[]] : eval (quote M7[]) : nil =?= quote M7[]
    -- + ()
    -- M7[] =?= λ x. ("list" : x : ("list" : M5[x] : x : nil) : nil)
    -- eval M5[quote M7[]] : M7[] : nil =?= quote M7[]
    -- + (decompose + delete nil)
    -- M7[] =?= λ x. ("list" : x : ("list" : M5[x] : x : nil) : nil)
    -- eval M5[quote M7[]] =?= "quote"
    -- M7[] =?= M7[]
    -- + (delete M7[])
    -- M7[] =?= λ x. ("list" : x : ("list" : M5[x] : x : nil) : nil)
    -- eval M5[quote M7[]] =?= "quote"
    -- + () M5[x1] := "quote" : M8[x1] : nil
    -- M7[] =?= λ x. ("list" : x : ("list" : ("quote" : M8[x] : nil) : x : nil) : nil)
    -- eval ("quote" : M8[quote M7[]] : nil) =?= "quote"
    -- + ()
    -- M7[] =?= λ x. ("list" : x : ("list" : ("quote" : M8[x] : nil) : x : nil) : nil)
    -- M8[quote M7[]] =?= "quote"
    -- + ()
    -- M7[] =?= λ x. ("list" : x : ("list" : ("quote" : "quote" : nil) : x : nil) : nil)

    e = EvalE q :==: q
    q = M "QUINE" []

solveList2 :: (Eq var, Show var) => [SOAS LispF String (IncMany var)]
solveList2 =
  [ body
  | (MetaSubst subst, _unsolved) <- defaultPreunify (15, 4) lispEvalRules
      [Constraint{ constraintEq = e, constraintScope = 2}]
  , Just body <- [lookup "LIST" subst]
  ]
  where
    e = EvalE (ConsE (ConsE f m1) m2) :==: ConsE m1 (ConsE m2 NilE)
    f = M "LIST" []
    m1 = Var (BoundVar 0)
    m2 = Var (BoundVar 1)

solveDup :: (Eq var, Show var) => [SOAS LispF String (IncMany var)]
solveDup =
  [ body
  | (MetaSubst subst, _unsolved) <- defaultPreunify (15, 2) lispEvalRules
      [Constraint{ constraintEq = e, constraintScope = 1}]
  , Just body <- [lookup "DUP" subst]
  ]
  where
    e = EvalE (ConsE f (ConsE x NilE)) :==: ConsE x (ConsE x NilE)
    f = M "DUP" []
    x = Var (BoundVar 0)
