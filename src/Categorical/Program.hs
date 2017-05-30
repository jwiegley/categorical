{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
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
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Categorical.Program where

-- #define COERCE_BUG 0

import Categorical.Gather
import Categorical.NonDet
import ConCat.Category
import ConCat.Syntactic (Syn, app0)
import Data.Coerce
import Prelude hiding ((.), id, curry, uncurry, const)

data Position
    = V1
    | V2
    | V3
    deriving (Eq, Ord, Enum, Show, Read)

#ifdef COERCE_BUG
newtype V (l :: Position) v = V v
#else
type V (l :: Position) v = v
#endif

class Ok k v => ProgramCat k v where
    xfer :: forall s t.           V s v `k` V t v
    load ::                    Int `k` V t v
    mov  :: Prod k (V s v) (V s v) `k` V s v
    add  :: Prod k (V s v) (V s v) `k` V s v
    ret  ::                  V s v `k` v

#ifdef COERCE_BUG
instance ProgramCat (->) Int where
    xfer            = coerce
    load            = pack
    mov (V _x, V y) = V y
    add (V x, V y)  = V (x + y)
    ret             = unpack
#else
instance ProgramCat (->) Int where
    xfer        = coerce
    {-# NOINLINE xfer #-}
    load        = id
    {-# NOINLINE load #-}
    mov (_x, y) = y
    {-# NOINLINE mov #-}
    add (x, y)  = x + y
    {-# NOINLINE add #-}
    ret x       = x
    {-# NOINLINE ret #-}
#endif

instance ProgramCat Syn Int where
  xfer = app0 "xfer"
  {-# NOINLINE xfer #-}
  load = app0 "load"
  {-# NOINLINE load #-}
  mov  = app0 "mov"
  {-# NOINLINE mov #-}
  add  = app0 "add"
  {-# NOINLINE add #-}
  ret  = app0 "ret"
  {-# NOINLINE ret #-}

instance ProgramCat k Int => ProgramCat (NonDet k) Int where
    xfer = NonDet (\(l :: Int) -> (if l < 10 then xfer else xfer))
    add  = NonDet (\(l :: Int) -> (if l < 10 then add  else add))
    mov  = NonDet (\(l :: Int) -> (if l < 10 then mov  else mov))
    load = NonDet (\(l :: Int) -> (if l < 10 then load else load))
    ret  = NonDet (\(l :: Int) -> (if l < 10 then ret  else ret))

instance ProgramCat Gather Int where
    xfer = Gather 5
    add  = Gather 10
    mov  = Gather 10
    load = Gather 5
    ret  = Gather 1
