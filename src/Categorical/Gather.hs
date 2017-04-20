{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Categorical.Gather where

import ConCat.Category
import Data.Monoid
import Data.Set
import Prelude hiding (id, (.), curry, uncurry, const)

newtype Gather a b = Gather { runGather :: Set Int }

gather :: Gather a b -> Set Int
gather = runGather

instance Category Gather where
    id = Gather empty
    Gather f . Gather g = Gather (f <> g)

instance ProductCat Gather where
    exl = Gather empty
    exr = Gather empty
    Gather f &&& Gather g = Gather (f <> g)

instance Num a => NumCat Gather a where
    negateC = Gather empty
    addC    = Gather empty
    subC    = Gather empty
    mulC    = Gather empty
    powIC   = Gather empty

instance ConstCat Gather Int where
    const = Gather . singleton
