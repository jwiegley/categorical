{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=2800 #-}

module Conal where

import Categorical
import ConCat.AltCat (ccc)
import ConCat.Category
import Prelude hiding ((.), id, curry, uncurry)

data PreambleCorrelatorInput = PreambleCorrelatorInput
data PostambleCorrelatorInput = PostambleCorrelatorInput
data SampleBufferInput = SampleBufferInput

data DividerOutput = DividerOutput
data SampleBufferOutput = SampleBufferOutput

lanTiming :: PreambleCorrelatorInput
          -> PostambleCorrelatorInput
          -> SampleBufferInput
          -> (DividerOutput, SampleBufferOutput)
lanTiming = error "lanTiming opaque"

data NCOMultiplyOutput = NCOMultiplyOutput

freqAdjust :: DividerOutput -> SampleBufferOutput -> NCOMultiplyOutput
freqAdjust = error "freqAdjust opaque"

data GRSampleBufferOutput = GRSampleBufferOutput

guardRemoval :: NCOMultiplyOutput -> GRSampleBufferOutput
guardRemoval = error "guardRemoval opaque"

data FFTOutput = FFTOutput

fft :: GRSampleBufferOutput -> FFTOutput
fft = error "fft opaque"

data MultiplerOutput = MultiplerOutput

equalizer :: FFTOutput -> MultiplerOutput
equalizer = error "equalizer opaque"

data LanSlicerOutput = LanSlicerOutput

lanSlicer :: MultiplerOutput -> LanSlicerOutput
lanSlicer = error "lanSlicer opaque"

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
