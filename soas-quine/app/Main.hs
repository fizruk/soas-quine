{-# LANGUAGE TypeApplications #-}
module Main (main) where

import           SOAS.LISP  as LISP
import           SOAS.Quine

main :: IO ()
main = do
  -- putStrLn "[ λ-calculus ] ∀ f. FIX f ≡ f (FIX f)"
  -- mapM_ print $ take 1 (solveFix @Int)
  putStrLn "[ LISP ] ∀ x. eval((DUP x)) ≡ (x x)"
  mapM_ print $ take 1 (LISP.solveDup @Int)
  -- putStrLn "[ LISP ] ∀ m1 m2. eval(((LIST m1) m2)) ≡ (m1 m2)"
  -- mapM_ print $ take 5 (LISP.solveList2 @Int)
  -- putStrLn "[ LISP ] eval(QUINE) ≡ QUINE"
  -- mapM_ print $ take 1 (LISP.solveQuine @Int)
