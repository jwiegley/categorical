{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=2800 #-}

module Conal where

import Categorical
import ConCat.AltCat (ccc)
import ConCat.Category
import ConCat.Rep
import Prelude hiding ((.), id, curry, uncurry)

data PreambleCorrelatorInput = PreambleCorrelatorInput deriving Show
data PostambleCorrelatorInput = PostambleCorrelatorInput deriving Show
data SampleBufferInput = SampleBufferInput deriving Show

instance HasRep PreambleCorrelatorInput where
    type Rep PreambleCorrelatorInput = ()
    repr _ = ()
    abst () = PreambleCorrelatorInput

instance HasRep PostambleCorrelatorInput where
    type Rep PostambleCorrelatorInput = ()
    repr _ = ()
    abst () = PostambleCorrelatorInput

instance HasRep SampleBufferInput where
    type Rep SampleBufferInput = ()
    repr _ = ()
    abst () = SampleBufferInput

data DividerOutput = DividerOutput deriving Show
data SampleBufferOutput = SampleBufferOutput deriving Show

instance HasRep DividerOutput where
    type Rep DividerOutput = ()
    repr _ = ()
    abst () = DividerOutput

instance HasRep SampleBufferOutput where
    type Rep SampleBufferOutput = ()
    repr _ = ()
    abst () = SampleBufferOutput

lanTiming :: PreambleCorrelatorInput
          -> PostambleCorrelatorInput
          -> SampleBufferInput
          -> (DividerOutput, SampleBufferOutput)
lanTiming _ _ _ = (DividerOutput, SampleBufferOutput)

data NCOMultiplyOutput = NCOMultiplyOutput deriving Show

instance HasRep NCOMultiplyOutput where
    type Rep NCOMultiplyOutput = ()
    repr _ = ()
    abst () = NCOMultiplyOutput

freqAdjust :: DividerOutput -> SampleBufferOutput -> NCOMultiplyOutput
freqAdjust _ _ = NCOMultiplyOutput

data GRSampleBufferOutput = GRSampleBufferOutput deriving Show

instance HasRep GRSampleBufferOutput where
    type Rep GRSampleBufferOutput = ()
    repr _ = ()
    abst () = GRSampleBufferOutput

guardRemoval :: NCOMultiplyOutput -> GRSampleBufferOutput
guardRemoval _ = GRSampleBufferOutput

data FFTOutput = FFTOutput deriving Show

instance HasRep FFTOutput where
    type Rep FFTOutput = ()
    repr _ = ()
    abst () = FFTOutput

fft :: GRSampleBufferOutput -> FFTOutput
fft _ = FFTOutput

data MultiplerOutput = MultiplerOutput deriving Show

instance HasRep MultiplerOutput where
    type Rep MultiplerOutput = ()
    repr _ = ()
    abst () = MultiplerOutput

equalizer :: FFTOutput -> MultiplerOutput
equalizer _ = MultiplerOutput

data LanSlicerOutput = LanSlicerOutput deriving Show

instance HasRep LanSlicerOutput where
    type Rep LanSlicerOutput = ()
    repr _ = ()
    abst () = LanSlicerOutput

lanSlicer :: MultiplerOutput -> LanSlicerOutput
lanSlicer _ = LanSlicerOutput

component :: PreambleCorrelatorInput
          -> PostambleCorrelatorInput
          -> SampleBufferInput
          -> LanSlicerOutput
component = curry3
          $ lanSlicer
          . equalizer
          . fft
          . guardRemoval
          . uncurry freqAdjust
          . uncurry3 lanTiming

curry3 :: ((a, b, c) -> d) -> a -> b -> c -> d
curry3 f x y z = f (x, y, z)

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z

main :: IO ()
main = print $ (ccc (uncurry3 component)
                :: Cat (PreambleCorrelatorInput,
                        PostambleCorrelatorInput,
                        SampleBufferInput)
                       LanSlicerOutput)
