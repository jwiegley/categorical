{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UnicodeSyntax #-}

module Categorical where

import Prelude hiding (id, (.), curry, uncurry, const)

import Control.Arrow (Kleisli(..))
import Data.Coerce
import Data.Monoid
import Data.Proxy
import Data.Set
import Data.Tuple (swap)

import ConCat.Category

{------------------------------------------------------------------------}

type (~>) = Cat
type (×) = Prod Cat
type (+) = Coprod Cat

data Cat a b where
    -- Category
    Id      :: a ~> a
    Compose :: b ~> c -> a ~> b -> a ~> c

    -- TerminalCat
    It :: a ~> ()

    -- BottomCat
    Bottom :: a ~> b

    -- UnknownCat
    Unknown :: a ~> b

    -- CoerceCat
    Coerce :: Coercible a b => a ~> b

    -- EqCat
    Equal    :: Eq a => a × a ~> BoolOf Cat
    NotEqual :: Eq a => a × a ~> BoolOf Cat

    -- OrdCat
    LessThan           :: Ord a => a × a ~> BoolOf Cat
    GreaterThan        :: Ord a => a × a ~> BoolOf Cat
    LessThanOrEqual    :: Ord a => a × a ~> BoolOf Cat
    GreaterThanOrEqaul :: Ord a => a × a ~> BoolOf Cat

    -- DistribCat
    Distl :: (a × (u + v)) ~> ((a × u) + (a × v))
    Distr :: ((u + v) × b) ~> ((u × b) + (v × b))

    -- BoolCat
    Not :: BoolOf Cat ~> BoolOf Cat
    And :: BoolOf Cat × BoolOf Cat ~> BoolOf Cat
    Or  :: BoolOf Cat × BoolOf Cat ~> BoolOf Cat
    Xor :: BoolOf Cat × BoolOf Cat ~> BoolOf Cat

    -- IfCat
    If :: BoolOf k × (a × a) ~> a

    -- ProductCat
    Exl   :: (a × b) ~> a
    Exr   :: (a × b) ~> b
    Dup   :: a ~> (a × a)
    SwapP :: (a × b) ~> (b × a)
    Cross :: (a ~> c) -> (b ~> d) -> (a × b) ~> (c × d)
    Fork  :: (a ~> c) -> (a ~> d) -> a ~> (c × d)

    -- CoproductCat
    Inl    :: a ~> (a + b)
    Inr    :: b ~> (a + b)
    Jam    :: (a + a) ~> a
    SwapS  :: (a + b) ~> (b + a)
    Across :: (c ~> a) -> (d ~> b) -> (c + d) ~> (a + b)
    Split  :: (c ~> a) -> (d ~> a) -> (c + d) ~> a

    -- ConstCat
    Const :: Show b => b -> a ~> b

    -- ClosedCat
    Apply   :: (Exp Cat a b × a) ~> b
    Curry   :: ((a × b) ~> c) -> (a ~> Exp Cat b c)
    Uncurry :: (a ~> Exp Cat b c) -> ((a × b) ~> c)

    -- ENumCat
    Succ :: Enum a => a ~> a
    Pred :: Enum a => a ~> a

    -- NumCat
    Negate :: Num a => a ~> a
    Add    :: Num a => a × a ~> a
    Sub    :: Num a => a × a ~> a
    Mul    :: Num a => a × a ~> a
    PowI   :: Num a => a × Int ~> a

    -- FractionalCat
    Recip  :: Fractional a => a ~> a
    Divide :: Fractional a => (a × a) ~> a

    -- RealFracCat
    Floor   :: (RealFrac a, Integral b) => a ~> b
    Ceiling :: (RealFrac a, Integral b) => a ~> b

    -- FloatingCat
    Exp :: Floating a => a ~> a
    Cos :: Floating a => a ~> a
    Sin :: Floating a => a ~> a

    -- FromIntegralCat
    FromIntegral :: (Integral a, Num b) => a ~> b

instance Show (Cat a b) where
    show = \case
        Id                 -> "Id"
        Compose f g        -> "(" ++ show f ++ " ∘ " ++ show g ++ ")"
        It                 -> "It"
        Bottom             -> "Bottom"
        Unknown            -> "Unknown"
        Equal              -> "Equal"
        NotEqual           -> "NotEqual"
        LessThan           -> "LessThan"
        GreaterThan        -> "GreaterThan"
        LessThanOrEqual    -> "LessThanOrEqual"
        GreaterThanOrEqaul -> "GreaterThanOrEqaul"
        Distl              -> "Distl"
        Distr              -> "Distr"
        Coerce             -> "Coerce"
        Not                -> "Not"
        And                -> "And"
        Or                 -> "Or"
        Xor                -> "Xor"
        If                 -> "If"
        Exl                -> "Exl"
        Exr                -> "Exr"
        Dup                -> "Dup"
        SwapP              -> "SwapP"
        Cross f g          -> "(" ++ show f ++ " *** " ++ show g ++ ")"
        Fork f g           -> "(" ++ show f ++ " &&& " ++ show g ++ ")"
        Inl                -> "Inl"
        Inr                -> "Inr"
        Jam                -> "Jam"
        SwapS              -> "Swaps"
        Across f g         -> "(" ++ show f ++ " +++ " ++ show g ++ ")"
        Split f g          -> "(" ++ show f ++ " ||| " ++ show g ++ ")"
        Const b            -> "Const " ++ show b
        Apply              -> "Apply"
        Curry f            -> "(Curry " ++ show f ++ ")"
        Uncurry f          -> "(Uncurry " ++ show f ++ ")"
        Succ               -> "Succ"
        Pred               -> "Pred"
        Negate             -> "Negate"
        Add                -> "Add"
        Sub                -> "Sub"
        Mul                -> "Mul"
        PowI               -> "PowI"
        Recip              -> "Recip"
        Divide             -> "Divide"
        Floor              -> "Floor"
        Ceiling            -> "Ceiling"
        Exp                -> "Exp"
        Cos                -> "Cos"
        Sin                -> "Sin"
        FromIntegral       -> "FromIntegral"

eval :: a ~> b -> a -> b
eval = \case
    Id                 -> id
    Compose f g        -> eval f . eval g
    It                 -> const ()
    Bottom             -> undefined
    Unknown            -> error "unknown!"
    Equal              -> uncurry (==)
    NotEqual           -> uncurry (/=)
    LessThan           -> uncurry (<)
    GreaterThan        -> uncurry (>)
    LessThanOrEqual    -> uncurry (<=)
    GreaterThanOrEqaul -> uncurry (>=)
    Distl              -> \(a, p) -> case p of Left x -> Left (a, x)
                                               Right x -> Right (a, x)
    Distr              -> \(p, b) -> case p of Left x -> Left (x, b)
                                               Right x -> Right (x, b)
    Coerce             -> coerce
    Not                -> not
    And                -> uncurry (&&)
    Or                 -> uncurry (||)
    Xor                -> uncurry (/=)
    If                 -> \(x, (y, z)) -> if x then y else z
    Exl                -> fst
    Exr                -> snd
    Dup                -> \x -> (x, x)
    SwapP              -> swap
    Cross f g          -> eval f *** eval g
    Fork f g           -> eval f &&& eval g
    Inl                -> Left
    Inr                -> Right
    Jam                -> either id id
    SwapS              -> \case Left x -> Right x
                                Right x -> Left x
    Across f g         -> eval f +++ eval g
    Split f g          -> eval f ||| eval g
    Const b            -> const b
    Apply              -> uncurry ($)
    Curry f            -> curry (eval f)
    Uncurry f          -> uncurry (eval f)
    Succ               -> succ
    Pred               -> pred
    Negate             -> negate
    Add                -> uncurry (+)
    Sub                -> uncurry (-)
    Mul                -> uncurry (*)
    PowI               -> uncurry (^)
    Recip              -> recip
    Divide             -> uncurry (/)
    Floor              -> floor
    Ceiling            -> ceiling
    Exp                -> exp
    Cos                -> cos
    Sin                -> sin
    FromIntegral       -> fromIntegral

instance Category Cat where
    id  = Id
    (.) = Compose

instance TerminalCat Cat where
    it = It

instance BottomCat Cat a b where
    bottomC = Bottom

instance UnknownCat Cat a b where
    unknownC = Unknown

instance Eq a => EqCat Cat a where
    equal    = Equal
    notEqual = NotEqual

instance Ord a => OrdCat Cat a where
    lessThan           = LessThan
    greaterThan        = GreaterThan
    lessThanOrEqual    = LessThanOrEqual
    greaterThanOrEqual = GreaterThanOrEqaul

instance Fractional a => FractionalCat Cat a where
    recipC = Recip
    divideC = Divide

instance (RealFrac a, Integral b) => RealFracCat Cat a b where
    floorC = Floor
    ceilingC = Ceiling

instance Floating a => FloatingCat Cat a where
    expC = Exp
    cosC = Cos
    sinC = Sin

instance (Integral a, Num b) => FromIntegralCat Cat a b where
    fromIntegralC = FromIntegral

instance DistribCat Cat where
    distl = Distl
    distr = Distr

instance Coercible a b => CoerceCat Cat a b where
    coerceC = Coerce

instance (Enum a, Show a) => EnumCat Cat a where
    succC = Succ
    predC = Pred

instance BoolCat Cat where
    notC = Not
    andC = And
    orC  = Or
    xorC = Xor

instance IfCat Cat a where
    ifC = If

instance ProductCat Cat where
    exl   = Exl
    exr   = Exr
    dup   = Dup
    swapP = SwapP
    (***) = Cross
    (&&&) = Fork

instance CoproductCat Cat where
    inl   = Inl
    inr   = Inr
    jam   = Jam
    swapS = SwapS
    (+++) = Across
    (|||) = Split

instance Show a => ConstCat Cat a where
    const = Const

instance ClosedCat Cat where
    apply = Apply
    curry = Curry
    uncurry = Uncurry

instance Num a => NumCat Cat a where
    negateC = Negate
    addC    = Add
    subC    = Sub
    mulC    = Mul
    powIC   = PowI

{------------------------------------------------------------------------}

newtype Gather a b = Gather { runGather :: Set Int }

gather :: Gather a b -> Set Int
gather = runGather

instance Category Gather where
    id = Gather empty
    Gather f . Gather g = Gather (f <> g)

instance ProductCat Gather where
    exl = Gather empty
    exr = Gather empty
    Gather f &&& Gather g = Gather (f <> g)

instance Num a => NumCat Gather a where
    negateC = Gather empty
    addC    = Gather empty
    subC    = Gather empty
    mulC    = Gather empty
    powIC   = Gather empty

instance ConstCat Gather Int where
    const = Gather . singleton

{------------------------------------------------------------------------}

data TeletypeF r = Get (Char -> r) | Put Char r

instance Show r => Show (TeletypeF r) where
    show (Get k) = "Get " ++ show (k '?')
    show (Put c r) = "Put " ++ show c ++ " " ++ show r

-- class Ok k a => TeletypeCat k a where
--     getC :: () `k` a
--     putC :: a `k` ()

-- class Teletype a where
--     get :: Proxy a -> a
--     put :: a -> ()

-- instance TeletypeCat (->) Char where
--     getC = error "getC doesn't work in plain Haskell"
--     putC = error "putC doesn't work in plain Haskell"

-- instance TeletypeCat (Kleisli IO) Char where
--     getC = Kleisli (\() -> getChar)
--     putC = Kleisli putChar
