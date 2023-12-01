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
module SOAS.LISP where

import Free.Scoped
import Free.Scoped.TH ( makePatternsAll )
import Data.Bifunctor.TH
    ( deriveBifoldable, deriveBifunctor, deriveBitraversable )

import SOAS.Quine

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
  [ EvalE NilE :==: NilE
  , EvalE (ConsE (SymbolE "quote") (ConsE (M "M" []) NilE)) :==: M "M" []
  , EvalE (ConsE (LambdaE (M "B" [Var Z])) (ConsE (M "A" []) NilE)) :==: EvalE (M "B" [M "A" []])
  , EvalE (ConsE (SymbolE "list") NilE) :==: NilE
  , EvalE (ConsE (SymbolE "list") (ConsE (M "A" []) NilE)) :==: ConsE (M "A" []) NilE
  , EvalE (ConsE (SymbolE "list") (ConsE (M "A" []) (ConsE (M "B" []) NilE))) :==: ConsE (M "A" []) (ConsE (M "B" []) NilE)
  ]

solveQuine :: (Eq var, Show var) => [SOAS LispF String (IncMany var)]
solveQuine =
  [ body
  | (MetaSubst subst, _unsolved) <- defaultPreunify (9, 3) lispEvalRules
      [Constraint{ constraintEq = e, constraintScope = 2}]
  , Just body <- [lookup "CONST" subst]
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
