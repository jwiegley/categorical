{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PackageImports #-}
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

{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Categorical.Types where

import ConCat.Category
import ConCat.Rep
import Control.Monad.State
import "newtype" Control.Newtype (Newtype(..))
import Data.Coerce
import Z3.Category
import Prelude hiding ((.), id, curry, uncurry, const)

data Position
    = V1
    | V2
    | V3
    deriving (Eq, Ord, Enum, Show, Read)

-- type V (l :: Position) v = v
newtype V (l :: Position) v = V v

instance Newtype (V l v) v where
    pack = V
    unpack (V v) = v

-- instance CoerceCat (->) (V l1 v) (V l2 v) where
--     coerceC = coerce

-- instance CoerceCat (NonDet p) (V l1 v) (V l2 v) where
--     coerceC = N $ \p a -> (coerce a, p)

-- instance CoerceCat (->) (V l v) v where
--     coerceC (V v) = v

-- instance CoerceCat (->) v (V l v) where
--     coerceC = V

-- instance CoerceCat (NonDet p) (V l v) v where
--     coerceC = NonDet $ \p (V v) -> (v, p)

-- instance CoerceCat (NonDet p) v (V l v) where
--     coerceC = NonDet $ \p v -> (V v, p)

class Ok k v => ProgramCat k v where
    xfer :: forall s t.           V s v `k` V t v
    load ::                    Int `k` V t v
    mov  :: Prod k (V s v) (V s v) `k` V s v
    add  :: Prod k (V s v) (V s v) `k` V s v
    ret  ::                  V s v `k` v

-- instance ProgramCat (->) Int where
--     xfer            = coerce
--     load            = id
--     mov (_x, y) = y
--     add (x, y)  = x + y
--     ret x       = x

instance ProgramCat (->) Int where
    xfer            = coerce
    load            = pack
    mov (V _x, V y) = V y
    add (V x, V y)  = V (x + y)
    ret             = unpack

data NonDet k a b where
    NonDet :: (EvalE p, GenE p, Show p) => (p -> a `k` b) -> NonDet k a b

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

instance ProgramCat k Int => ProgramCat (NonDet k) Int where
    xfer = NonDet (\(l :: Int) -> (if l < 10 then xfer else xfer))
    add  = NonDet (\(l :: Int) -> (if l < 10 then add  else add))
    mov  = NonDet (\(l :: Int) -> (if l < 10 then mov  else mov))
    load = NonDet (\(l :: Int) -> (if l < 10 then load else load))
    ret  = NonDet (\(l :: Int) -> (if l < 10 then ret  else ret))
