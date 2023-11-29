{-# LANGUAGE TypeApplications #-}
module Main (main) where

import SOAS.Quine

main :: IO ()
main = mapM_ print $
  take 1 (solveFix @Int)
