{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=2800 #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}

module Categorical.Types where

import ConCat.Category
import Control.Arrow (Kleisli(..))
import Control.Monad.State
import "newtype" Control.Newtype (Newtype(..))
import Data.Coerce
import Prelude hiding ((.), id, curry, uncurry, const)
import Z3.Category

data Position
    = V1
    | V2
    | V3
    deriving (Eq, Ord, Enum, Show, Read)

newtype V (l :: Position) v = V v
    deriving (Eq, Ord, Show, Read)

instance Newtype (V l v) v where
  pack = V
  unpack (V v) = v

instance CoerceCat (->) (V l v) v where
  coerceC (V v) = v

instance CoerceCat (->) v (V l v) where
  coerceC = V

instance CoerceCat (Kleisli (State s)) (V l v) v where
  coerceC = Kleisli $ \(V v) -> return v

instance CoerceCat (Kleisli (State s)) v (V l v) where
  coerceC = Kleisli $ \v -> return (V v)

class Ok k v => ProgramCat k v where
    xfer :: forall s t.           V s v `k` V t v
    load ::                    Int `k` V t v
    mov  :: Prod k (V s v) (V s v) `k` V s v
    add  :: Prod k (V s v) (V s v) `k` V s v
    ret  ::                  V s v `k` v

instance ProgramCat (->) Int where
    xfer            = coerce
    load            = V
    mov (V _x, V y) = V y
    add (V x, V y)  = V (x + y)
    ret (V x)       = x

type Latency = Int

instance Ok (Kleisli (State Latency)) Int => ProgramCat (Kleisli (State Latency)) Int where
    xfer = Kleisli $ \a -> coerce a <$ modify (+ 5)
    load = Kleisli $ \a -> load a   <$ modify (+ 10)
    mov  = Kleisli $ \a -> mov a    <$ modify (+ 30)
    add  = Kleisli $ \a -> add a    <$ modify (+ 50)
    ret  = Kleisli $ \a -> ret a    <$ modify (+ 1)

{-
data NonDet k a b where
    NonDet :: (EvalE p, GenE p) => (p -> k a b) -> NonDet k a b

deriving instance Show (NonDet k a b)

instance Category k => Category (NonDet k) where
    type Ok (NonDet k) = Ok k
    id = NonDet (\() -> id)
    NonDet f . NonDet g = NonDet (\(p1, p2) -> f p1 . g p2)

instance (OpCon (Prod k) (Ok' k), ProductCat k) => ProductCat (NonDet k) where
    exl = NonDet (\() -> exl)
    exr = NonDet (\() -> exr)
    NonDet f &&& NonDet g = NonDet (\(p1, p2) -> f p1 &&& g p2)

instance TerminalCat k => TerminalCat (NonDet k) where
    it = NonDet (\() -> it)

instance ConstCat k b => ConstCat (NonDet k) b where
    const b = NonDet (\() -> const b)

instance BottomCat k a b => BottomCat (NonDet k) a b where
    bottomC = NonDet (\() -> bottomC)

instance UnknownCat k a b => UnknownCat (NonDet k) a b where
    unknownC = NonDet (\() -> unknownC)

instance ClosedCat k => ClosedCat (NonDet k) where
    curry   (NonDet f) = NonDet (curry . f)
    uncurry (NonDet f) = NonDet (uncurry . f)

-- instance CoproductCat (NonDet k) where
--     inl = NonDet Left
--     inr = NonDet Right
--     NonDet f ||| NonDet g = NonDet (f ||| g)

instance (EqCat k a, Eq a) => EqCat (NonDet k) a where
    equal    = NonDet (\((), ()) -> equal)
    notEqual = NonDet (\((), ()) -> notEqual)

instance (OrdCat k a, Ord a) => OrdCat (NonDet k) a where
    lessThan           = NonDet (\() -> lessThan)
    greaterThan        = NonDet (\() -> greaterThan)
    lessThanOrEqual    = NonDet (\() -> lessThanOrEqual)
    greaterThanOrEqual = NonDet (\() -> greaterThanOrEqual)

-- instance Fractional a => FractionalCat (NonDet k) a where
--     recipC = NonDet recip
--     divideC = NonDet (uncurry (/))

-- instance (RealFrac a, Integral b) => RealFracCat (NonDet k) a b where
--     floorC = NonDet floor
--     ceilingC = NonDet ceiling

-- instance Floating a => FloatingCat (NonDet k) a where
--     expC = NonDet exp
--     cosC = NonDet cos
--     sinC = NonDet sin

-- instance (Integral a, Num b) => FromIntegralCat (NonDet k) a b where
--     fromIntegralC = NonDet fromIntegral

-- instance DistribCat (NonDet k) where
--     distl = NonDet $ \(x, e) -> case e of
--         Left y  -> Left (x, y)
--         Right z -> Right (x, z)
--     distr = NonDet $ \(e, x) -> case e of
--         Left y  -> Left (y, x)
--         Right z -> Right (z, x)

-- instance (HasRep a, r ~ Rep a) => RepCat (NonDet k) a r where
--     reprC = NonDet repr
--     abstC = NonDet abst

-- instance (Enum a, Show a) => EnumCat (NonDet k) a where
--     succC = NonDet succ
--     predC = NonDet pred

instance BoolCat k => BoolCat (NonDet k) where
    notC = NonDet (\() -> notC)
    andC = NonDet (\() -> andC)
    orC  = NonDet (\() -> orC)
    xorC = NonDet (\() -> xorC)

instance IfCat k a => IfCat (NonDet k) a where
    ifC = NonDet (\() -> ifC)

instance (NumCat k a, Num a) => NumCat (NonDet k) a where
    negateC = NonDet (\() -> negateC)
    addC    = NonDet (\() -> addC)
    subC    = NonDet (\() -> subC)
    mulC    = NonDet (\() -> mulC)
    powIC   = NonDet (\() -> powIC)

instance ProgramCat k Int => ProgramCat (NonDet k) Int where
    xfer = NonDet (\b -> if b then xfer else xfer)
    load = NonDet (\b -> if b then load else load)
    mov  = NonDet (\b -> if b then mov else mov)
    add  = NonDet (\b -> if b then add else add)
    ret  = NonDet (\b -> if b then ret else ret)
-}
