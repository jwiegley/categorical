{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Categorical.Gather where

import ConCat.Category
import ConCat.Rep
import Data.Monoid
import Prelude hiding (id, (.), curry, uncurry, const)

newtype Gather a b = Gather { runGather :: Int }

gather :: Gather a b -> Int
gather = runGather

instance Category Gather where
    id = Gather 0
    Gather f . Gather g = Gather (f + g)

instance ProductCat Gather where
    exl = Gather 0
    exr = Gather 0
    Gather f &&& Gather g = Gather (max f g)

instance  ClosedCat Gather where
    curry   (Gather f) = Gather f
    uncurry (Gather f) = Gather f

instance Num a => NumCat Gather a where
    negateC = Gather 0
    addC    = Gather 0
    subC    = Gather 0
    mulC    = Gather 0
    powIC   = Gather 0

instance ConstCat Gather Int where
    const = Gather

instance (HasRep a, r ~ Rep a) => RepCat Gather a r where
    reprC = Gather 0
    abstC = Gather 0
