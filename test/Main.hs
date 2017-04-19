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
{-# OPTIONS_GHC -Wno-orphan-instances #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=28000 #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}

module Main where

import           Categorical
import           Categorical.Types
import           ConCat.AltCat
import           ConCat.Syntactic (render)
import           Control.Arrow (Kleisli(..), arr)
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Maybe
import           Functions
import           Prelude hiding ((.), id, curry, uncurry, const)
import           Z3.Category
import           Z3.Monad hiding (eval)

program :: Int -> Int -> Int -> Int
program x y z =
    let v2    :: V 'V2 Int = load  x in
    let v1    :: V 'V1 Int = load  y in
    let v3    :: V 'V3 Int = load  z in
    let v2'   :: V 'V2 Int = curry add  (xfer v1)  v2 in
    let v1'   :: V 'V1 Int = load  2 in
    let v2''  :: V 'V2 Int = curry add  (xfer v1') v2' in
    let v2''' :: V 'V2 Int = curry add  (xfer v3)  v2'' in
    ret v2'''
{-# INLINE program #-}

instance EvalE Latency where evalE = evalPrim evalInt fromInteger
instance GenE Latency  where genE = genPrim mkFreshIntVar

main :: IO ()
main = do
    putStrLn "Hello, Haskell!"

    print $ ccc @(->) (uncurry (equation @Int)) (10, 20)

    print $ render (ccc (uncurry (equation @Int)))
    print $ gather (ccc (uncurry (equation @Int)))

    print $ ccc @Cat (uncurry (equation @Int))
    print $ eval (ccc @Cat (uncurry (equation @Int))) (10, 20)

    putStrLn "Goodbye, Haskell!"

    print $ curry (curry (ccc (uncurry (uncurry program)))) 10 20 30

    print $ runState (runKleisli (ccc (uncurry (uncurry program)))
                                 ((10, 20), 30)) (Sum 0)

    print (runWriter (runKleisli (ccc (uncurry (uncurry program)))
                                 ((10, 20), 30)) :: (Int, Sum Int))

    -- Ask Z3 to find a suitable program for us using not only existential
    -- degrees of freedom, but interactions between these degrees of freedom
    -- and whatever metadata resulted from earlier choices.
    case ccc @(Kleisli (State Latency)) (uncurry (uncurry program)) of
        Kleisli f -> do
            let k s x y z = runState (f ((x, y), z)) s
            mres <- runZ3Show (ccc @Z3Cat k)
            case mres of
                Nothing -> putStrLn "No solution!"
                Just p  -> print $ k p 10 20 30
