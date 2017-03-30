{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}

module Main where

import Categorical
import ConCat.AltCat (ccc)
import ConCat.Syntactic (render)
import Control.Arrow (Kleisli(..))
import Control.Monad
import Data.Proxy
-- import Control.Monad.Free

default (Int)

equation :: Num a => a -> a -> a
equation x y = x - 3 + 7 * y

tele :: (Monad m, Teletype m Char) => () -> m ()
tele _ = do
    x <- get (Proxy :: Proxy Char)
    put x
    put x

main :: IO ()
main = do
    putStrLn "Hello, Haskell!"

    print $ render (ccc (uncurry (equation @Int)))
    print $ gather (ccc (uncurry (equation @Int)))
    print (ccc (uncurry (equation @Int)) :: Cat (Int, Int) Int)
    print (eval (ccc (uncurry (equation @Int)) :: Cat (Int, Int) Int) (10, 20))

    join $ runKleisli (ccc (tele @IO) :: Kleisli IO () (IO ())) ()

    -- let expr = constarr @Expr (ccc (uncurry (equation @Int))) (10, 20)
    -- print expr
    -- print $ iter phi expr

    putStrLn "Goodbye, Haskell!"
  -- where
  --   phi (Neg a)   = - a
  --   phi (Add a b) = a + b
  --   phi (Sub a b) = a - b
  --   phi (Mul a b) = a * b
