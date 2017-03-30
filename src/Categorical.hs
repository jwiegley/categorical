{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Categorical where

import Prelude hiding (id, (.), curry, uncurry, const)

import Data.Monoid
import Data.Set

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
    Coerce :: a ~> b

    -- EqCat
    Equal    :: a × a ~> BoolOf Cat
    NotEqual :: a × a ~> BoolOf Cat

    -- OrdCat
    LessThan           :: a × a ~> BoolOf Cat
    GreaterThan        :: a × a ~> BoolOf Cat
    LessThanOrEqual    :: a × a ~> BoolOf Cat
    GreaterThanOrEqaul :: a × a ~> BoolOf Cat

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
    Curry   :: ((a × b) ~> c)     -> (a ~> Exp Cat b c)
    Uncurry :: (a ~> Exp Cat b c) -> ((a × b) ~> c)

    -- ENumCat
    Succ :: a ~> a
    Pred :: a ~> a

    -- NumCat
    Negate :: a ~> a
    Add    :: a × a ~> a
    Sub    :: a × a ~> a
    Mul    :: a × a ~> a
    PowI   :: a × Int ~> b

    -- FractionalCat
    Recip  :: a ~> a
    Divide :: (a × a) ~> a

    -- RealFracCat
    Floor   :: a ~> b
    Ceiling :: a ~> b

    -- FloatingCat
    Exp :: a ~> a
    Cos :: a ~> a
    Sin :: a ~> a

    -- FromIntegralCat
    FromIntegral :: a ~> b

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

instance Category Cat where
    id  = Id
    (.) = Compose

instance TerminalCat Cat where
    it = It

instance BottomCat Cat a b where
    bottomC = Bottom

instance UnknownCat Cat a b where
    unknownC = Unknown

instance EqCat Cat a where
    equal    = Equal
    notEqual = NotEqual

instance OrdCat Cat a where
    lessThan           = LessThan
    greaterThan        = GreaterThan
    lessThanOrEqual    = LessThanOrEqual
    greaterThanOrEqual = GreaterThanOrEqaul

instance Num a => FractionalCat Cat a where
    recipC = Recip
    divideC = Divide

instance RealFracCat Cat a b where
    floorC = Floor
    ceilingC = Ceiling

instance FloatingCat Cat a where
    expC = Exp
    cosC = Cos
    sinC = Sin

instance FromIntegralCat Cat a b where
    fromIntegralC = FromIntegral

instance DistribCat Cat where
    distl = Distl
    distr = Distr

instance CoerceCat Cat a b where
    coerceC = Coerce

instance (Num a, Show a) => EnumCat Cat a where
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

instance NumCat Cat a where
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
