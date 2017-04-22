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
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Main where

import qualified Categorical.AST as AST
import           Categorical.Gather
import           Categorical.Types
import           ConCat.AltCat (ccc)
import           ConCat.Category
-- jww (2017-04-22): Switching to AltCat instances result in a plugin error
-- import           ConCat.AltCat
import           ConCat.Syntactic (render)
import           Control.Arrow (Kleisli(..))
import           Control.Monad.State
import           Control.Monad.Writer
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

resolve :: NonDet k a b
        -> ((a `k` b) -> Bool)
        -> IO (Maybe (a `k` b))
resolve (NonDet g) f = fmap g <$> runZ3 (ccc @Z3Cat (\p -> f (g p)))
{-# INLINE resolve #-}

triviallyTrue :: a -> Bool
triviallyTrue _ = True
{-# INLINE triviallyTrue #-}

main :: IO ()
main = do
    putStrLn "Hello, Haskell!"

    print $ ccc @(->) (uncurry (equation @Int)) (10, 20)

    print $ render (ccc (uncurry (equation @Int)))
    print $ gather (ccc (uncurry (equation @Int)))

    print $ ccc @AST.Cat (uncurry (equation @Int))
    print $ AST.eval (ccc @AST.Cat (uncurry (equation @Int))) (10, 20)

    putStrLn "Goodbye, Haskell!"

    putStrLn "Run the program directly..."
    print $ ccc program (10, 20, 30)

    -- jww (2017-04-22): Uncommenting this gets a residual error
    -- putStrLn "Solve for a trivially satisfied constraint..."
    -- Just k <- resolve (ccc @(NonDet (->)) program) triviallyTrue
    -- print $ k (10, 20, 30)

    -- jww (2017-04-22): Uncommenting this causes a hang in GHC
    -- putStrLn "Solve for a latency bound..."
    -- Just k <- resolve (ccc @(NonDet (Kleisli (Writer (Sum Int)))) program) $ \p ->
    --     getSum (execWriter (runKleisli p (10, 20, 30))) < 50
    -- print $ runKleisli k (10, 20, 30)
