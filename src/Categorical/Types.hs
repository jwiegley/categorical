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

import           ConCat.Category
import           ConCat.Rep
import           Control.Arrow (Kleisli(..))
import           Control.Monad.State
import "newtype" Control.Newtype (Newtype(..))
import           Data.Coerce
import           Data.Functor.Identity
import           Data.Monoid
import           Prelude hiding ((.), id, curry, uncurry, const)
import           Z3.Category

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

instance CoerceCat (NonDet p) (V l v) v where
    coerceC = NonDet $ \p (V v) -> (v, p)

instance CoerceCat (NonDet p) v (V l v) where
    coerceC = NonDet $ \p v -> (V v, p)

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

data NonDet p a b where
    NonDet :: (p -> a -> (b, p)) -> NonDet p a b
    deriving Functor

pattern N :: (p -> a -> (b, p)) -> NonDet p a b
pattern N f = NonDet f

instance Category (NonDet p) where
    id = N (\p x -> (x, p))
    N f . N g = N (\p x -> let (y, p') = g p x in f p' y)

instance Num p => ProductCat (NonDet p) where
    exl = N (\p x -> (exl x, p))
    exr = N (\p x -> (exr x, p))
    N f &&& N g = N $ \p x ->
        let (f', fp) = f p x
            (g', gp) = g p x in
        ((f', g'), fp + gp)

instance TerminalCat (NonDet p) where
    it = N (\p x -> (it x, p))

instance ConstCat (NonDet p) b where
    const b = N (\p _ -> (b, p))

instance BottomCat (NonDet p) a b where
    bottomC = N (\p x -> (bottomC x, p))

instance UnknownCat (NonDet p) a b where
    unknownC = N (\p x -> (unknownC x, p))

instance Num p => ClosedCat (NonDet p) where
    -- curry   (NonDet (Kleisli f)) = N $ \x -> pure $ \y -> f (x, y)
    curry   (NonDet f) = error "curry NYI"
    uncurry (NonDet f) = N $ \p (x, y) -> let (f', p') = f p x in (f' y, p')

instance CoproductCat (NonDet p) where
    inl = N (\p x -> (inl x, p))
    inr = N (\p x -> (inr x, p))
    N f ||| N g = error "(|||) NYI"

instance (Num p, Eq a) => EqCat (NonDet p) a where
    equal    = N (\p x -> (equal x, p))
    notEqual = N (\p x -> (notEqual x, p))

instance (Num p, Ord a) => OrdCat (NonDet p) a where
    lessThan           = N (\p x -> (lessThan x, p))
    greaterThan        = N (\p x -> (greaterThan x, p))
    lessThanOrEqual    = N (\p x -> (lessThanOrEqual x, p))
    greaterThanOrEqual = N (\p x -> (greaterThanOrEqual x, p))

-- instance Fractional a => FractionalCat (NonDet p) a where
--     recipC = N recip
--     divideC = N (uncurry (/))

-- instance (RealFrac a, Integral b) => RealFracCat (NonDet p) a b where
--     floorC = N floor
--     ceilingC = N ceiling

-- instance Floating a => FloatingCat (NonDet p) a where
--     expC = N exp
--     cosC = N cos
--     sinC = N sin

-- instance (Integral a, Num b) => FromIntegralCat (NonDet p) a b where
--     fromIntegralC = N fromIntegral

-- instance DistribCat (NonDet p) where
--     distl = N $ \(x, e) -> case e of
--         Left y  -> Left (x, y)
--         Right z -> Right (x, z)
--     distr = N $ \(e, x) -> case e of
--         Left y  -> Left (y, x)
--         Right z -> Right (z, x)

instance (HasRep a, r ~ Rep a) => RepCat (NonDet p) a r where
    reprC = N (\p x -> (repr x, p))
    abstC = N (\p x -> (abst x, p))

instance (Enum a, Show a) => EnumCat (NonDet p) a where
    succC = N (\p x -> (succ x, p))
    predC = N (\p x -> (pred x, p))

instance Num p => BoolCat (NonDet p) where
    notC = N (\p x -> (notC x, p))
    andC = N (\p x -> (andC x, p))
    orC  = N (\p x -> (orC x, p))
    xorC = N (\p x -> (xorC x, p))

instance Num p => IfCat (NonDet p) a where
    ifC = N (\p x -> (ifC x, p))

instance Num a => NumCat (NonDet p) a where
    negateC = N (\p x -> (negateC x, p))
    addC    = N (\p x -> (addC x, p))
    subC    = N (\p x -> (subC x, p))
    mulC    = N (\p x -> (mulC x, p))
    powIC   = N (\p x -> (powIC x, p))

instance ProgramCat (NonDet Int) Int where
    xfer = N (\l x -> (if l < 10 then xfer x else xfer x, l + 5))
    add  = N (\l x -> (if l < 10 then add  x else add  x, l + 50))
    mov  = N (\l x -> (if l < 10 then mov  x else mov  x, l + 30))
    load = N (\l x -> (if l < 10 then load x else load x, l + 10))
    ret  = N (\l x -> (if l < 10 then ret  x else ret  x, l + 1))
