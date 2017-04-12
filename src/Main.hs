{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=2800 #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

module Main where

import Categorical
import ConCat.AltCat (ccc)
import ConCat.Category
import ConCat.Syntactic (render)
import Prelude hiding ((.), id, curry, uncurry)

equation :: Num a => a -> a -> a
equation x y = x - 3 + 7 * y
{-# INLINE equation #-}

main :: IO ()
main = do
    putStrLn "Hello, Haskell!"

    print $ ccc @(->) @(Int, Int) @Int (uncurry (equation @Int)) (10, 20)

    print $ render (ccc (uncurry (equation @Int)))
    print $ gather (ccc (uncurry (equation @Int)))

    print $ ccc @Cat (uncurry (equation @Int))
    print $ eval (ccc @Cat (uncurry (equation @Int))) (10, 20)

    putStrLn "Goodbye, Haskell!"
