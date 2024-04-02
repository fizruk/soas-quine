{-# LANGUAGE TypeApplications #-}
module Main (main) where

import           SOAS.LISP  as LISP
import           SOAS.Quine

main :: IO ()
main = do
  putStrLn "[ λ-calculus ] ∀ f. FIX f ≡ f (FIX f)"
  mapM_ print $ take 1 (solveFix @Int)
  putStrLn "[ LISP ] eval(QUINE) ≡ QUINE"
  mapM_ print $ take 5 (LISP.solveQuine @Int)
