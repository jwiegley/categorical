{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}

module Main where

import Categorical
import ConCat.AltCat (ccc)
import ConCat.Syntactic (render)
-- import Control.Monad.Free

default (Int)

equation :: Num a => a -> a -> a
equation x y = x - 3 + 7 * y

main :: IO ()
main = do
    putStrLn "Hello, Haskell!"

    print $ render (ccc (uncurry (equation @Int)))
    print $ gather (ccc (uncurry (equation @Int)))
    print (ccc (uncurry (equation @Int)) :: Cat (Int, Int) Int)

    -- let expr = constarr @Expr (ccc (uncurry (equation @Int))) (10, 20)
    -- print expr
    -- print $ iter phi expr

    putStrLn "Goodbye, Haskell!"
  -- where
  --   phi (Neg a)   = - a
  --   phi (Add a b) = a + b
  --   phi (Sub a b) = a - b
  --   phi (Mul a b) = a * b
