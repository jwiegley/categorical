{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

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

{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Categorical.NonDet where

import ConCat.AltCat (ccc)
import ConCat.Category
import ConCat.Rep
import ConCat.Syntactic (Syn, app0)
import Control.Monad.State
-- import "newtype" Control.Newtype (Newtype(..))
import Data.Coerce
import Z3.Category
import Prelude hiding ((.), id, curry, uncurry, const)

data NonDet k a b where
    NonDet :: (EvalE p, GenE p) => (p -> a `k` b) -> NonDet k a b

runNonDet :: NonDet k a b -> (forall p. (p -> a `k` b) -> a `k` b) -> a `k` b
runNonDet (NonDet f) k = k f

deriving instance Functor (k a) => Functor (NonDet k a)

instance Category k => Category (NonDet k) where
    type Ok (NonDet k) = Ok k
    id = NonDet (\() -> id)
    NonDet f . NonDet g = NonDet $ \(p1, p2) -> f p1 . g p2

instance ProductCat k => ProductCat (NonDet k) where
    exl = NonDet (\() -> exl)
    exr = NonDet (\() -> exr)
    NonDet f &&& NonDet g = NonDet $ \(p1, p2) -> f p1 &&& g p2

instance  TerminalCat k => TerminalCat (NonDet k) where
    it = NonDet (\() -> it)

instance  ConstCat k b => ConstCat (NonDet k) b where
    const b = NonDet (\() -> const b)

instance  BottomCat k a b => BottomCat (NonDet k) a b where
    bottomC = NonDet (\() -> bottomC)

instance  UnknownCat k a b => UnknownCat (NonDet k) a b where
    unknownC = NonDet (\() -> unknownC)

instance  ClosedCat k => ClosedCat (NonDet k) where
    curry   (NonDet f) = NonDet $ \p -> curry (f p)
    uncurry (NonDet f) = NonDet $ \p -> uncurry (f p)

instance  CoproductCat k => CoproductCat (NonDet k) where
    inl = NonDet (\() -> inl)
    inr = NonDet (\() -> inr)
    NonDet f ||| NonDet g = NonDet $ \(p1, p2) -> f p1 ||| g p2

instance (EqCat k a, Eq a) => EqCat (NonDet k) a where
    equal    = NonDet (\() -> equal)
    notEqual = NonDet (\() -> notEqual)

instance (OrdCat k a, Ord a) => OrdCat (NonDet k) a where
    lessThan           = NonDet (\() -> lessThan)
    greaterThan        = NonDet (\() -> greaterThan)
    lessThanOrEqual    = NonDet (\() -> lessThanOrEqual)
    greaterThanOrEqual = NonDet (\() -> greaterThanOrEqual)

instance (FractionalCat k a, Fractional a) => FractionalCat (NonDet k) a where
    recipC  = NonDet (\() -> recipC)
    divideC = NonDet (\() -> divideC)

instance (RealFracCat k a b, RealFrac a, Integral b) => RealFracCat (NonDet k) a b where
    floorC = NonDet (\() -> floorC)
    ceilingC = NonDet (\() -> ceilingC)

instance (FloatingCat k a, Floating a) => FloatingCat (NonDet k) a where
    expC = NonDet (\() -> expC)
    cosC = NonDet (\() -> cosC)
    sinC = NonDet (\() -> sinC)

instance (FromIntegralCat k a b, Integral a, Num b) => FromIntegralCat (NonDet k) a b where
    fromIntegralC = NonDet (\() -> fromIntegralC)

instance (DistribCat k) => DistribCat (NonDet k) where
    distl = NonDet (\() -> distl)
    distr = NonDet (\() -> distr)

instance RepCat k a r => RepCat (NonDet k) a r where
    reprC = NonDet (\() -> reprC)
    abstC = NonDet (\() -> abstC)

instance (EnumCat k a, Enum a) => EnumCat (NonDet k) a where
    succC = NonDet (\() -> succC)
    predC = NonDet (\() -> predC)

instance BoolCat k => BoolCat (NonDet k) where
    notC = NonDet (\() -> notC)
    andC = NonDet (\() -> andC)
    orC  = NonDet (\() -> orC)
    xorC = NonDet (\() -> xorC)

instance  IfCat k a => IfCat (NonDet k) a where
    ifC = NonDet (\() -> ifC)

instance (NumCat k a, Num a) => NumCat (NonDet k) a where
    negateC = NonDet (\() -> negateC)
    addC    = NonDet (\() -> addC)
    subC    = NonDet (\() -> subC)
    mulC    = NonDet (\() -> mulC)
    powIC   = NonDet (\() -> powIC)

solution :: (EvalE p, GenE p) => (p -> Bool) -> IO (Maybe p)
solution f = runZ3 (ccc @Z3Cat f)
{-# INLINE solution #-}

resolve :: NonDet k a b -> ((a `k` b) -> Bool) -> IO (Maybe (a `k` b))
resolve (NonDet g) f = fmap g <$> solution (f . g)
{-# INLINE resolve #-}
