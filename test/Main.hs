{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=1000 #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}

module Main where

import qualified Categorical.AST as AST
import           Categorical.Gather
import           Categorical.Types
import           ConCat.AltCat (ccc)
import           ConCat.Category
import           ConCat.Syntactic (render)
import           Control.Arrow (Kleisli(..))
import           Control.Monad.State
import           Data.Functor.Identity
import           Data.Monoid
import           Functions
import           Prelude hiding ((.), id, curry, uncurry, const)
import           Z3.Category
import           Z3.Monad

default (Int)

program :: (Int, Int, Int) -> Int
program (x, y, z) =
    let v2    :: V 'V2 Int = load  x in
    let v1    :: V 'V1 Int = load  y in
    let v3    :: V 'V3 Int = load  z in
    let v2'   :: V 'V2 Int = curry add  (xfer v1)  v2 in
    let v1'   :: V 'V1 Int = load  2 in
    let v2''  :: V 'V2 Int = curry add  (xfer v1') v2' in
    let v2''' :: V 'V2 Int = curry add  (xfer v3)  v2'' in
    ret v2'''
{-# INLINE program #-}

main :: IO ()
main = do
    putStrLn "Hello, Haskell!"

    print $ ccc @(->) (uncurry (equation @Int)) (10, 20)

    print $ render (ccc (uncurry (equation @Int)))
    print $ gather (ccc (uncurry (equation @Int)))

    print $ ccc @AST.Cat (uncurry (equation @Int))
    print $ AST.eval (ccc @AST.Cat (uncurry (equation @Int))) (10, 20)

    putStrLn "Goodbye, Haskell!"

    print $ ccc program (10, 20, 30)

    print $ runNonDet (ccc @(NonDet Int) program) 0 (10, 20, 30)

    -- Ask Z3 to find a suitable program for us using not only existential
    -- degrees of freedom, but interactions between these degrees of freedom
    -- and whatever metadata resulted from earlier choices.
    putStrLn "step 1..."
    case ccc @(NonDet Int) program of
        NonDet f -> do
            putStrLn "step 2..."
            let k x y z s = f s (x, y, z)
                g = k 10 20 30
            putStrLn "step 3..."
            mres <- runZ3Show (ccc @Z3Cat g)
            putStrLn "step 4..."
            case mres of
                Nothing -> putStrLn "No solution!"
                Just p  -> do
                    putStrLn "step 5..."
                    print $ g p
