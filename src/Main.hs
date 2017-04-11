{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=2800 #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module Main where

import ConCat.AltCat (ccc)
import ConCat.Syntactic (render)
-- import Control.Arrow (Kleisli(..))
import Control.Monad
-- import Control.Monad.Free

import Categorical

equation :: Num a => a -> a -> a
equation x y = x - 3 + 7 * y

-- type Teletype = Free TeletypeF

-- tele :: Kleisli Teletype () ()
-- tele = Kleisli $ \() -> Free $ Get $ \c -> Free $ Put c (Free $ Put c (Pure ()))

main :: IO ()
main = do
    putStrLn "Hello, Haskell!"

    print $ render (ccc (uncurry (equation @Int)))
    print $ gather (ccc (uncurry (equation @Int)))
    print (ccc (uncurry (equation @Int)) :: Cat (Int, Int) Int)
    print (eval (ccc (uncurry (equation @Int)) :: Cat (Int, Int) Int) (10, 20))

    -- print $ (ccc tele :: Cat () (Teletype ()))

    putStrLn "Goodbye, Haskell!"
