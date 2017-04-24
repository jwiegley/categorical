{-# LANGUAGE RankNTypes #-}

module Categorical.Ringer where

import Data.Semiring

newtype Ringer w a = Ringer { runRinger :: Semiring w => (a, w) }
