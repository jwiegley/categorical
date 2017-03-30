{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=2800 #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Categorical where

import ConCat.AltCat (ccc)
import ConCat.Category
import Control.Arrow (Kleisli(..), arr)
import Control.Monad
import Control.Monad.Free
import Control.Monad.Writer
import Data.Set
import Debug.Trace
import Prelude hiding (id, (.), curry, uncurry, const)

data ExprF r
    = Neg r
    | Add r r
    | Sub r r
    | Mul r r
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Expr = Free ExprF

newtype ConstArr f a b = ConstArr { getConstArr :: f a -> f b }

instance Category (ConstArr Expr) where
    id = ConstArr id
    ConstArr f . ConstArr g = ConstArr (f . g)

instance TerminalCat (ConstArr Expr) where
    it = ConstArr (arr void)

instance BottomCat (ConstArr Expr) a b where
    bottomC = ConstArr (arr undefined)

-- instance UnknownCat (ConstArr Expr) a b where
-- instance EqCat (ConstArr Expr) a where
-- instance OrdCat (ConstArr Expr) a where
-- instance Num a => FractionalCat (ConstArr Expr) a where
-- instance RealFracCat (ConstArr Expr) a b where
-- instance FloatingCat (ConstArr Expr) a where
-- instance FromIntegralCat (ConstArr Expr) a b where

-- instance DistribCat (ConstArr Expr) where
--     distl = ConstArr distl
--     distr = ConstArr distr

-- instance CoerceCat (ConstArr Expr) a b where
--     coerceC = ConstArr coerceC

instance Num a => EnumCat (ConstArr Expr) a where

instance BoolCat (ConstArr Expr) where
    notC = ConstArr (fmap notC)
    andC = ConstArr (fmap andC)
    orC  = ConstArr (fmap orC)
    xorC = ConstArr (fmap xorC)

instance IfCat (ConstArr Expr) a where
    ifC = ConstArr (fmap ifC)

instance ProductCat (ConstArr Expr) where
    exl = ConstArr (fmap exl)
    exr = ConstArr (fmap exr)
    ConstArr f &&& ConstArr g = ConstArr (\x -> liftM2 (,) (f x) (g x))

instance CoproductCat (ConstArr Expr) where
    inl = ConstArr (fmap inl)
    inr = ConstArr (fmap inr)
    ConstArr f ||| ConstArr g = ConstArr (\p -> p >>= \p' -> case p' of
                                                  Left x -> f (return x)
                                                  Right x -> g (return x))

instance ConstCat (ConstArr Expr) a where
    const b = ConstArr (const (pure b))

instance ClosedCat (ConstArr Expr) where
    apply = ConstArr (fmap apply)
    curry (ConstArr f) =
        error "What should curry be?"
        -- ConstArr $ \a -> return (\b -> f ((,) <$> a <*> b))

instance NumCat (ConstArr Expr) a where
    negateC = ConstArr (Free . Neg)
    addC    = ConstArr (\p -> p >>= \(x, y) -> Free (Add (Pure x) (Pure y)))
    subC    = ConstArr (\p -> p >>= \(x, y) -> Free (Sub (Pure x) (Pure y)))
    mulC    = ConstArr (\p -> p >>= \(x, y) -> Free (Mul (Pure x) (Pure y)))
    powIC   = error "powIC not supported"

-- newtype Gather a b = Gather { runGather :: Kleisli (Writer (Set Int)) a b }

newtype Gather a b = Gather { runGather :: Kleisli (Writer (Set Int)) a b }

instance Category Gather where
    id = Gather id
    Gather f . Gather g = Gather (f . g)

instance ProductCat Gather where
    exl = Gather exl
    exr = Gather exr
    Gather f &&& Gather g = Gather (f &&& g)

instance Num a => NumCat Gather a where
  negateC = Gather negateC
  addC    = Gather addC
  subC    = Gather subC
  mulC    = Gather mulC
  powIC   = Gather powIC

instance ConstCat Gather Int where
    const b = Gather $ Kleisli $ const $ b <$ tell (singleton b)

equation :: Num a => a -> a -> a
equation x y = x + y - y

test' :: IO ()
test' = do
    -- print $ flip getConstArr (return (10, 20))
    --       $ (ccc (uncurry (equation @Int)) :: ConstArr Expr (Int, Int) Int)
    print $ runWriter
          $ flip runKleisli (10, 20)
          $ runGather
          $ (ccc (uncurry (equation @Int)) :: Gather (Int, Int) Int)
  where
    phi (Neg a)   = - a
    phi (Add a b) = a + b
    phi (Sub a b) = a - b
    phi (Mul a b) = a * b
{-# NOINLINE test' #-}
