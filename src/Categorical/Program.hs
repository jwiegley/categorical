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

module Categorical.Program where

import ConCat.Category
import ConCat.Rep
import ConCat.Syntactic (Syn, app0)
import Control.Monad.State
-- import "newtype" Control.Newtype (Newtype(..))
import Data.Coerce
import Z3.Category
import Categorical.NonDet
import Prelude hiding ((.), id, curry, uncurry, const)

data Position
    = V1
    | V2
    | V3
    deriving (Eq, Ord, Enum, Show, Read)

type V (l :: Position) v = v
-- newtype V (l :: Position) v = V v

-- instance Newtype (V l v) v where
--     pack = V
--     unpack (V v) = v

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

instance ProgramCat (->) Int where
    xfer            = coerce
    -- {-# NOINLINE xfer #-}
    load            = id
    -- {-# NOINLINE load #-}
    mov (_x, y) = y
    -- {-# NOINLINE mov #-}
    add (x, y)  = x + y
    -- {-# NOINLINE add #-}
    ret x       = x
    -- {-# NOINLINE ret #-}

instance ProgramCat Syn a where
  xfer = app0 "xfer"
  load = app0 "load"
  mov  = app0 "mov"
  add  = app0 "add"
  ret  = app0 "ret"
  {-# INLINE xfer #-}
  {-# INLINE load #-}
  {-# INLINE mov #-}
  {-# INLINE add #-}
  {-# INLINE ret #-}

-- instance ProgramCat (->) Int where
--     xfer            = coerce
--     load            = pack
--     mov (V _x, V y) = V y
--     add (V x, V y)  = V (x + y)
--     ret             = unpack

instance ProgramCat k Int => ProgramCat (NonDet k) Int where
    xfer = NonDet (\(l :: Int) -> (if l < 10 then xfer else xfer))
    add  = NonDet (\(l :: Int) -> (if l < 10 then add  else add))
    mov  = NonDet (\(l :: Int) -> (if l < 10 then mov  else mov))
    load = NonDet (\(l :: Int) -> (if l < 10 then load else load))
    ret  = NonDet (\(l :: Int) -> (if l < 10 then ret  else ret))

predicate :: (((Int, Int), Int) -> Int) -> Bool
predicate k = k ((10, 20), 30) < 100
{-# INLINE predicate #-}
