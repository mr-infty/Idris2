module Data.IEEE754
--module IEEE754

import Builtin
import Prelude.Basics
import Prelude.Interfaces
import Prelude.EqOrd
import Prelude.Ops
import Prelude.Num
import Prelude.Show
import Prelude.Types
import Data.Fin
import Data.So
import Data.Vect
import Data.DPair

%default total

-- TODO: Move this somewhere else
public export
IsProp : Type -> Type
IsProp ty = (x : ty) -> (y : ty) -> x = y

public export
Prop : Type
Prop = Subset Type IsProp

public export
Cast Prop Type where
  cast = fst

public export
interface FamilyOfProps (f : Type -> Type) where
  valuedInProp : (a : Type) -> IsProp (f a)

----------------------------
-- Exceptions (Section 7) --
----------------------------



-- Some notes to myself:
--
-- 1. It would be **extremely** handy if there was a way to convert floats to ints and back (faithfully).
--    For example, this would allow a nearly trivial implementation of nextUp, and it would make it completely
--    trivial to compare them for equality.
-- 2. It would be very convenient if there was a way to convert a floating-point data representation to a
--    floating-point datum. The standard somehow implies that this is possible (i.e. encode and decode),
--    however it's not explicitly part of the standard itself.

-------------------------------------------------------------
-- Float data representations (IEEE Specification Level 3) --
-------------------------------------------------------------

public export
data Radix = Two | Ten

public export
radixToNat : Radix -> Nat
radixToNat Two = 2
radixToNat Ten = 10

public export
Digit : {rdx : Radix} -> Type
Digit {rdx} = Fin (radixToNat rdx)

-- TODO: Move DecChar and HexChar somewhere else; this should only be stuff related to FDR
public export
DecChar : Type
DecChar = Subset Char ((=== True) . isDigit) --(c : Char ** isDigit c = True)

public export
HexChar : Type
HexChar = Subset Char ((=== True). isHexDigit) --(c : Char ** isHexDigit c = True)

public export
record FloatFormat where
  constructor MkFloatFormat
  radix : Radix
  prec : Nat
  emax : Integer
  emin : Integer -- equals 1-emax for basic formats

--TODO: Fix this
public export
record EncodingParameters where
  constructor MkEncodingParams
  bias : Integer
  expWidth : Nat
  trailing : Nat
  storageWidth : Nat

--------------------------------------------
-- Basic Floaing-Point Format (Table 3.2) --
--------------------------------------------

public export
binary32 : FloatFormat
binary32 = MkFloatFormat Two 24 127 (1 - 127)

public export
binary64 : FloatFormat
binary64 = MkFloatFormat Two 53 1023 (1 - 1023)

public export
binary128 : FloatFormat
binary128 = MkFloatFormat Two 113 16383 (1 - 16383)

public export
decimal64 : FloatFormat
decimal64 = MkFloatFormat Ten 16 384 (1 - 384)

public export
decimal128 : FloatFormat
decimal128 = MkFloatFormat Ten 34 6144 (1 - 6144)

----------------------------------------------
-- Interchange formats (Tables 3.5 and 3.6) --
----------------------------------------------

public export
binary : (k : Nat) ->
         {auto atLeast128 : So (k >= 128)} ->
         {auto multipleOf32 : (m : Nat ** k = 32 * m)} ->
         FloatFormat
binary k @{pf} @{(m ** pf')} = ?binary_hole

public export
decimal : (k : Nat) ->
          {auto atLeast32 : So (k >= 32)} ->
          {auto multipleOf32 : (m : Nat ** (k = 32 * m))} ->
          FloatFormat
decimal k @{pf} @{(m ** pf')} = ?decimal_hole




public export
data Sign = Positive | Negative

public export
record Infinity where
  constructor MkInf
  sgn : Sign

public export
record NaN where
  constructor MkNaN
  signaling : Bool

public export
ExponentInRange : {fmt : FloatFormat} -> (exp : Integer) -> Type
ExponentInRange {fmt} exp = (emin fmt <= exp = True, exp <= emax fmt = True)

public export
Exponent : FloatFormat -> Type
Exponent fmt = Subset Integer (ExponentInRange {fmt=fmt}) --(exp : Integer ** ExponentInRange {fmt=fmt} exp)

public export
Significand : FloatFormat -> Type
Significand fmt = Vect (prec fmt) (Digit {rdx=radix fmt})

public export
significandToInteger : {fmt : FloatFormat} -> Significand fmt -> Integer
significandToInteger {fmt} m = digitsToInt (natToInteger $ radixToNat $ radix fmt)
                                           (map (natToInteger . finToNat) (reverse m)) where
  digitsToInt : Integer -> Vect n Integer -> Integer
  digitsToInt base [] = 0
  digitsToInt base (x :: xs) = x + base * (digitsToInt base xs)

public export
data FloatDataRep : (fmt : FloatFormat) -> Type where
  MkFDR : {fmt : FloatFormat} -> Sign -> Exponent fmt -> Significand fmt -> FloatDataRep fmt
  MkFDRFromInf : {fmt : FloatFormat} -> Infinity -> FloatDataRep fmt
  MkFDRFromNaN : {fmt : FloatFormat} -> NaN -> FloatDataRep fmt

---------------------------
-- `IEEE` type interface --
---------------------------

public export
data FloatClass = SignalingNaN
                | QuietNaN
                | NegativeInfinity
                | NegativeNormal
                | NegativeSubnormal
                | NegativeZero
                | PositiveZero
                | PositiveSubnormal
                | PositiveNormal
                | PositiveInfinity

public export
Show FloatClass where
  show SignalingNaN = "signalingNaN"
  show QuietNaN = "quietNaN"
  show NegativeInfinity = "negativeInfinity"
  show NegativeNormal = "negativeNormal"
  show NegativeSubnormal = "negativeSubnormal"
  show NegativeZero = "negativeZero"
  show PositiveZero = "positiveZero"
  show PositiveSubnormal = "positiveSubnormal"
  show PositiveNormal = "positiveNormal"
  show PositiveInfinity = "positiveInfinity"

---------------------------------
-- IEEE attributes (section 4) --
---------------------------------

public export
data RoundingMode = NearestTiesToEven
                  | NearestTiesAwayFromZero
                  | TowardZero
                  | TowardPositive
                  | TowardNegative

Show RoundingMode where
  show NearestTiesToEven = "Round to nearest, ties to even"
  show NearestTiesAwayFromZero = "Round to nearest, ties away from zero"
  show TowardZero = "Round toward zero"
  show TowardPositive = "Round toward positive infinity"
  show TowardNegative = "Round toward negative infinity"

-----------------------------------
-- IEEE Conversion specification --
-----------------------------------

-- TODO: Fix this.
public export
data PrecisionSpec = SetPrec Nat
                   | PreserveQuantum

-- TODO: Fix this.
public export
record ConversionSpec where
  constructor MkConvSpec
  prec : PrecisionSpec
  --radixChr : Char

-- The IEEE interface is parametrized over a *family* of types instead of a
-- single type in order to support inhomogeneous operations.

||| The `IEEE` interface defines operations on numbers which are IEEE-754 floating-point numbers.
public export
interface FamilyOfProps supported => IEEE (supported : Type -> Type) where
  ||| The format of the floating-point type.
  fmt : (0 a : Type) ->
        supported a =>
        FloatFormat

  ||| The format of the values returned by `logB`.
  |||
  ||| Note: The type `logBty i` *must* be able to represent the integers
  ||| from `-2*(emax (fmt i) + prec (fmt i))` to `2*(emax (fmt i) + prec (fmt i))`
  ||| faithfully.
  logBty : (0 a : Type) ->
           supported a =>
           Type

  ------------------------------
  -- 5.3.1 General operations --
  ------------------------------

  ||| Rounds a floating-point number according to a given rounding mode.
  ||| Does not signal inexactness of rounding.
  |||
  ||| Note: Zero operands are rounded to zero results of the same sign, and likewise
  ||| infinite operands are rounded to infinite results of the same sign.
  roundToIntegral : RoundingMode ->
                    supported a =>
                    a -> a

  -- TODO: Add exceptions...
  -- TODO: What does "numerically different" really mean?
  ||| Rounds a floating-point number according to the current rounding mode.
  ||| Signals an inexact exception if the result is numerically different from the operand.
  |||
  ||| Note: Zero operands are rounded to zero results of the same sign, and likewise
  ||| infinite operands are rounded to infinite results of the same sign.
  roundToIntegralExact : {auto rdm : RoundingMode} ->
                         supported a =>
                         a -> a

  -- TODO: Which order relation is implied here?
  ||| The least floating-point number bigger than the given one.
  |||
  ||| In particluar, `nextUp x` equals
  |||
  |||    - `-0` if `x` is the biggest number less than `-0`,
  |||    - the least number bigger than `+0` if `x` is `-0` or `+0`,
  |||    - `+inf` if `x` is `+inf`,
  |||    - the smallest finite number if `x` is `-inf`, and
  |||    - a NaN if `x` is a NaN.
  nextUp : supported a =>
           a -> a

  -- TODO: Should this be kept part of the interface or made an auxillary function?
  ||| The biggest floating-point number smaller than the given one.
  |||
  ||| In particluar, `nextDown x` equals
  |||
  |||    - `+0` if `x` is the smallest number bigger than `+0`,
  |||    - the biggest number smaller than `-0` if `x` is `-0` or `+0`,
  |||    - `-inf` if `x` is `-inf`,
  |||    - the biggest finite number if `x` is `+inf`, and
  |||    - a NaN if `x` is a NaN.
  |||
  ||| Note: `nextDown x` equals `negate (nextUp (negate x))`.
  nextDown : supported a =>
             a -> a
  nextDown x = negate {supported=supported} (nextUp {supported=supported} (negate {supported=supported} x))

  ||| `remainder x y` is the remainder `r` after dividing `x` by `y`.
  |||
  ||| If `y` is nonzero and both `x` and `y` are finite, the remainder `r`
  ||| is finite and satisfies the equation
  |||
  |||     x = n*y + r,
  |||
  ||| viewed as an identity of rational numbers, where `n` is the integer
  ||| obtained from `x/y` by rounding using ties-to-even mode.
  |||
  ||| In particular, the floating-point number is uniquely determined by
  ||| the above equation unless `r` is zero. In that case, `r` is taken
  ||| to have the same sign as `x`.
  remainder : supported a =>
              a -> a -> a

  ------------------------------
  -- 5.3.2 Decimal operations --
  ------------------------------
  quantize : {auto rdm : RoundingMode} ->
             supported a =>
             a -> a -> a
  quantum : supported a =>
            a -> a

  ---------------------------------
  -- 5.3.3 logBFormat operations --
  ---------------------------------
  scaleB : {auto rdm : RoundingMode} ->
           supported a =>
           a -> logBty a -> a
  logB : supported a =>
         a -> logBty a

  ---------------------------------
  -- 5.4.1 Arithmetic operations --
  ---------------------------------
  addition : {auto rmd : RoundingMode} ->
             supported a =>
             supported a' =>
             supported b =>
             (radix (fmt a) = radix (fmt b)) =>
             (radix (fmt a') = radix (fmt b)) =>
             a -> a' -> b
  subtraction : {auto rmd : RoundingMode} ->
                supported a =>
                supported a' =>
                supported b =>
                (radix (fmt a) = radix (fmt b)) =>
                (radix (fmt a') = radix (fmt b)) =>
                a -> a' -> b
  multiplication : {auto rmd : RoundingMode} ->
                   supported a =>
                   supported a' =>
                   supported b =>
                   (radix (fmt a) = radix (fmt b)) =>
                   (radix (fmt a') = radix (fmt b)) =>
                   a -> a' -> b
  division : {auto rmd : RoundingMode} ->
             supported a =>
             supported a' =>
             supported b =>
             (radix (fmt a) = radix (fmt b)) =>
             (radix (fmt a') = radix (fmt b)) =>
             a -> a' -> b
  squareRoot : {auto rmd : RoundingMode} ->
               supported a =>
               supported b =>
               (radix (fmt a) = radix (fmt b)) =>
               a -> b
  fusedMultiplyAdd : {auto rmd : RoundingMode} ->
                     supported a =>
                     supported a' =>
                     supported a'' =>
                     supported b =>
                     (radix (fmt a) = radix (fmt a')) =>
                     (radix (fmt a') = radix (fmt b)) =>
                     (radix (fmt a'') = radix (fmt b)) =>
                     a -> a' -> a'' -> b
  convertFromInt : {auto rdm : RoundingMode} ->
                   supported a =>
                   Integer -> a
  convertToInteger : RoundingMode ->
                     supported a =>
                     a -> Integer
  convertToIntegerExact : RoundingMode ->
                          supported a =>
                          a -> Integer

  ------------------------------------------------------------------------
  -- 5.4.2 Conversion operations for floating-point formats and decimal --
  -- character sequences                                                --
  ------------------------------------------------------------------------
  convertFormat : {auto rdm : RoundingMode} ->
                  supported a =>
                  supported b =>
                  a -> b
  convertFromDecimalCharacter : {auto rmd : RoundingMode} ->
                                supported a =>
                                List DecChar -> a
  convertToDecimalCharacter : {auto rmd : RoundingMode} ->
                              ConversionSpec ->
                              supported a =>
                              a -> List DecChar

  ----------------------------------------------------
  -- 5.4.3 Conversion operations for binary formats --
  ----------------------------------------------------
  convertFromHexCharacter : {auto rmd : RoundingMode} ->
                            supported a =>
                            radix (fmt a) = Two =>
                            List HexChar -> a
  convertToHexCharacter : {auto rmd : RoundingMode} ->
                          ConversionSpec ->
                          supported a =>
                          radix (fmt a) = Two =>
                          a -> List HexChar

  -------------------------------
  -- 5.5.1 Sign bit operations --
  -------------------------------

  -- copy
  --TODO: These operations are only necessary required for arithmetic interchange formats.
  negate : supported a =>
           a -> a
  abs : supported a =>
        a -> a
  copySign : supported a =>
             a -> a -> a

  ------------------------------------------
  -- 5.5.2 Decimal re-encoding operations --
  ------------------------------------------

  -- TODO
  -- encodeDecimal
  -- decodeDecimal
  -- encodeBinary
  -- decodeBinary

  ------------------------
  -- 5.6.1 Comparisions --
  ------------------------
  compareQuiet : --{auto i,j : supportedType} ->
                 supported a =>
                 supported a' =>
                 (radix (fmt a) = radix (fmt a')) =>
                 a -> a' -> Maybe Ordering
  compareSignaling : --{auto i,j : supportedType} ->
                     supported a =>
                     supported a' =>
                     (radix (fmt a) = radix (fmt a')) =>
                     a -> a' -> Maybe Ordering
  ----------------------------------
  -- 5.7.1 Conformance predicates --
  ----------------------------------
  is754version1985 : Bool
  is754version2008 : Bool
  is754version2019 : Bool

  ------------------------------
  -- 5.7.2 General operations --
  ------------------------------
  ||| The class a floating-point number falls into.
  floatClass : supported a =>
               a -> FloatClass
  floatClass x = if isSignaling {supported=supported} x then SignalingNaN
                 else if isNaN {supported=supported} x then QuietNaN
                      else if isSignMinus {supported=supported} x
                           then if isInfinite {supported=supported} x then NegativeInfinity
                                else if isZero {supported=supported} x then NegativeZero
                                     else if isNormal {supported=supported} x then NegativeNormal
                                          else NegativeSubnormal
                           else if isInfinite {supported=supported} x then PositiveInfinity
                                else if isZero {supported=supported} x then PositiveZero
                                     else if isNormal {supported=supported} x then PositiveNormal
                                          else PositiveSubnormal

  ||| Returns true if the floating-point number has a negative sign.
  isSignMinus : supported a =>
                a -> Bool
  isSignMinus x = case floatClass {supported=supported} x of
                       NegativeInfinity => True
                       NegativeNormal => True
                       NegativeSubnormal => True
                       NegativeZero => True
                       _ => False

  ||| Returns true if the floating-point number is normal.
  isNormal : supported a =>
             a -> Bool
  isNormal x = case floatClass {supported=supported} x of
                    NegativeNormal => True
                    PositiveNormal => True
                    _ => False

  ||| Returns true if the floating-point number is finite.
  isFinite : supported a =>
             a -> Bool
  isFinite x = isZero {supported=supported} x || isSubnormal {supported=supported} x || isNormal {supported=supported} x

  ||| Returns true if the floating-point number is zero.
  isZero : supported a =>
           a -> Bool
  isZero x = case floatClass {supported=supported} x of
                  NegativeZero => True
                  PositiveZero => True
                  _ => False

  ||| Returns true if the floating-point number is subnormal.
  isSubnormal : supported a =>
                a -> Bool
  isSubnormal x = case floatClass {supported=supported} x of
                       NegativeSubnormal => True
                       PositiveSubnormal => True
                       _ => False

  -- WARNING: isInfinite x /= not (isFinite x) in general.
  ||| Returns true if the floating-point number is infinite.
  isInfinite : supported a =>
               a -> Bool
  isInfinite x = case floatClass {supported=supported} x of
                      NegativeInfinity => True
                      PositiveInfinity => True
                      _ => False

  -- WARNING: The set of NaN consists of more than one element.
  ||| Returns true if the floating-point number is a NaN.
  isNaN : supported a =>
          a -> Bool
  isNaN x = case floatClass {supported=supported} x of
                 SignalingNaN => True
                 QuietNaN => True
                 _ => False

  ||| Returns true if the floating-point number is a signaling NaN.
  isSignaling : supported a =>
                a -> Bool
  isSignaling x = case floatClass {supported=supported} x of
                       SignalingNaN => True
                       _ => False
  isCanonical : supported a =>
                a -> Bool
  radixOf : supported a =>
            a -> Radix
  --TODO: (Re-)Move this.
  radixOfCorrect : supported a =>
                   (x : a) -> (radixOf x = radix (fmt {a=a}))
  totalOrder : supported a =>
               a -> a -> Bool
  totalOrderMag : supported a =>
                  a -> a -> Bool
  totalOrderMag x y = totalOrder {supported=supported} (abs {supported=supported} x) (IEEE754.abs {supported=supported} y)

  -----------------------------
  -- 5.7.3 Decimal operation --
  -----------------------------
  sameQuantum : supported a =>
                (radix (fmt a) = Ten) =>
                a -> a -> Bool

  ------------------------------------------
  -- 5.7.4 Operations on subsets of flags --
  ------------------------------------------
  -- lowerFlags
  -- raiseFlags
  -- testFlags
  -- testSavedFlags
  -- restoreFlags
  -- saveAllFlags

public export
interface IEEE supported => IEEE_Rec supported where
  --------------------------------------------
  -- 9.2 Additional mathematical operations --
  --------------------------------------------
  exp : {auto rdm : RoundingMode} ->
        supported a =>
        a -> a
  expm1 : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  exp2 : {auto rdm : RoundingMode} ->
         supported a =>
         a -> a
  exp2m1 : {auto rdm : RoundingMode} ->
           supported a =>
           a -> a
  exp10 : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  exp10m1 : {auto rdm : RoundingMode} ->
            supported a =>
            a -> a
  log : {auto rdm : RoundingMode} ->
        supported a =>
        a -> a
  log2 : {auto rdm : RoundingMode} ->
         supported a =>
         a -> a
  log10 : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  logp1 : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  log2p1 : {auto rdm : RoundingMode} ->
           supported a =>
           a -> a
  log10p1 : {auto rdm : RoundingMode} ->
            supported a =>
            a -> a
  hypot : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  rsqrt : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  compound : {auto rdm : RoundingMode} ->
             supported a =>
             a -> Integer -> a
  rootn : {auto rdm : RoundingMode} ->
          supported a =>
          a -> Integer -> a
  pown : {auto rdm : RoundingMode} ->
         supported a =>
         a -> Integer -> a
  pow : {auto rdm : RoundingMode} ->
        supported a =>
        a -> a -> a
  powr : {auto rdm : RoundingMode} ->
         supported a =>
         a -> a -> a
  sin : {auto rdm : RoundingMode} ->
        supported a =>
        a -> a
  cos : {auto rdm : RoundingMode} ->
        supported a =>
        a -> a
  tan : {auto rdm : RoundingMode} ->
        supported a =>
        a -> a
  sinPi : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  cosPi : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  tanPi : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  asin : {auto rdm : RoundingMode} ->
         supported a =>
         a -> a
  acos : {auto rdm : RoundingMode} ->
         supported a =>
         a -> a
  atan : {auto rdm : RoundingMode} ->
         supported a =>
         a -> a
  atan2 : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a -> a
  asinPi : {auto rdm : RoundingMode} ->
           supported a =>
           a -> a
  acosPi : {auto rdm : RoundingMode} ->
           supported a =>
           a -> a
  atanPi : {auto rdm : RoundingMode} ->
           supported a =>
           a -> a
  atan2Pi : {auto rdm : RoundingMode} ->
            supported a =>
            a -> a -> a
  sinh : {auto rdm : RoundingMode} ->
         supported a =>
         a -> a
  cosh : {auto rdm : RoundingMode} ->
         supported a =>
         a -> a
  tanh : {auto rdm : RoundingMode} ->
         supported a =>
         a -> a
  asinh : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  acosh : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  atanh : {auto rdm : RoundingMode} ->
          supported a =>
          a -> a
  ------------------------------
  -- 9.4 Reduction operations --
  ------------------------------
  sum : supported a =>
        Vect n a -> a
  dot : supported a =>
        Vect n a ->
        Vect n a ->
        a
  sumSquare : supported a =>
              Vect n a -> a
  sumAbs : supported a =>
           Vect n a -> a
  scaledProd : supported a =>
               Vect n a -> (a, Integer)
  scaledProdSum : supported a =>
                  Vect n a ->
                  Vect n a ->
                  (a, Integer)
  scaledProdDiff : supported a =>
                   Vect n a ->
                   Vect n a ->
                   (a, Integer)
  -----------------------------------------
  -- 9.5 Augmented arithmetic operations --
  -----------------------------------------
  augmentedAddition : supported a =>
                      (radix (fmt {supported=supported} a) = Two) =>
                      a -> a -> (a,a)
  augmentedSubtraction : supported a =>
                         (radix (fmt {supported=supported} a) = Two) =>
                         a -> a -> (a,a)
  augmentedMultiplication : supported a =>
                            (radix (fmt {supported=supported} a) = Two) =>
                            a -> a -> (a,a)

  ----------------------------------------
  -- 9.6 Minimum and maximum operations --
  ----------------------------------------
  minimum : supported a =>
            a -> a -> a
  minimumNumber : supported a =>
                  a -> a -> a
  maximum : supported a =>
            a -> a -> a
  maximumNumber : supported a =>
                  a -> a -> a
  minimumMagnitude : supported a =>
                     a -> a -> a
  minimumMagnitudeNumber : supported a =>
                           a -> a -> a
  maximumMagnitude : supported a =>
                     a -> a -> a
  maximumMagnitudeNumber : supported a =>
                           a -> a -> a

  --------------------------------
  -- 9.7 NaN payload operations --
  --------------------------------
  getPayload : supported a =>
               a -> a
  setPayload : supported a =>
               a -> a
  setPayloadSignaling : supported a =>
                        a -> a

----------------------------------------------
-- Useful constants                         --
--                                          --
-- N.B.: The values of these 'constants'    --
--       depends on the runtim environment! --
----------------------------------------------
public export
positiveZero : {supported : _} ->
               IEEE supported =>
               supported a =>
               a
positiveZero {supported} = convertFromInt {supported=supported} 0

public export
negativeZero : {supported : _} ->
               IEEE supported =>
               supported a =>
               a
negativeZero {supported} = negate {supported=supported} (convertFromInt {supported=supported} 0)

public export
positiveInfinity : {supported : _} ->
                   {a : _} ->
                   IEEE supported =>
                   supported a =>
                   a
positiveInfinity {supported} {a} = division {supported=supported}
                                            (convertFromInt {supported=supported} {a=a} 1)
                                            (positiveZero {supported=supported} {a=a})

public export
negativeInfinity : {supported : _} ->
                   {a : _} ->
                   IEEE supported =>
                   supported a =>
                   a
negativeInfinity {supported} {a} = division {supported=supported}
                                            (convertFromInt {supported=supported} {a=a} 1)
                                            (negativeZero {supported=supported} {a=a})

-----------------------
-- Useful predicates --
-----------------------

--TODO: This is not a prop, because convertFromInt is not an embedding.
public export
isIntegral : {supported : _} ->
             IEEE supported =>
             supported a =>
             a -> Type
isIntegral {supported} x = (n : Integer ** x = convertFromInt {supported=supported} n)

------------------------------------------------------------------
-- Implementation of the `IEEE interface` for the `Double` type --
------------------------------------------------------------------

%foreign "scheme:ieee_roundTiesToEven"
prim__roundTiesToEven_Double : Double -> Double

%foreign "scheme:ieee_roundTiesAwayFromZero"
prim__roundTiesAwayFromZero_Double : Double -> Double

%foreign "scheme:ieee_roundToZero"
prim__roundToZero_Double : Double -> Double

%foreign "scheme:ieee_roundToPos"
prim__roundToPos_Double : Double -> Double

%foreign "scheme:ieee_roundToNeg"
prim__roundToNeg_Double : Double -> Double

%foreign "scheme:ieee_nextUp"
prim__nextUp_Double : Double -> Double

%foreign "scheme:ieee_negate"
prim__ieee_negate_Double : Double -> Double

%foreign "scheme:ieee_isSignMinus"
prim__isSignMinus_Double : Double -> Int

%foreign "scheme:ieee_isNormal"
prim__isNormal_Double : Double -> Int

%foreign "scheme:ieee_isFinite"
prim__isFinite_Double : Double -> Int

%foreign "scheme:ieee_isZero"
prim__isZero_Double : Double -> Int

%foreign "scheme:ieee_isSubnormal"
prim__isSubnormal_Double : Double -> Int

%foreign "scheme:ieee_isInfinite"
prim__isInfinite_Double : Double -> Int

%foreign "scheme:ieee_isNaN"
prim__isNaN_Double : Double -> Int

%foreign "scheme:ieee_isSignaling"
prim__isSignaling_Double : Double -> Int

public export
data Supported_IEEE : Type -> Type where
  DoubleSupported : Supported_IEEE Double

Supported_IEEE_is_prop : {0 a : _} ->
                          (x : Supported_IEEE a) -> (y : Supported_IEEE a) -> x = y
Supported_IEEE_is_prop DoubleSupported DoubleSupported = Refl

public export
FamilyOfProps Supported_IEEE where
  valuedInProp a = Supported_IEEE_is_prop

public export
[DefaultIEEE] IEEE Supported_IEEE where
  fmt _ @{DoubleSupported} = binary64 -- TODO: Is it really the same for *all* backends?
  logBty _ @{DoubleSupported} = Integer -- TODO: Is it the same for all backends? Is Integer large enough?
  roundToIntegral NearestTiesToEven @{DoubleSupported} = prim__roundTiesToEven_Double
  roundToIntegral NearestTiesAwayFromZero @{DoubleSupported} = prim__roundTiesAwayFromZero_Double
  roundToIntegral TowardZero @{DoubleSupported} = prim__roundToZero_Double
  roundToIntegral TowardPositive @{DoubleSupported} = prim__roundToPos_Double
  roundToIntegral TowardNegative @{DoubleSupported} = prim__roundToNeg_Double
  roundToIntegralExact = roundToIntegral @{DefaultIEEE} rdm
  nextUp @{DoubleSupported} = prim__nextUp_Double
  remainder @{DoubleSupported} = ?remainder_hole
  quantize @{rdm} @{DoubleSupported} = ?quantize_hole
  quantum @{DoubleSupported} = ?quantum_hole
  scaleB @{rdm} @{DoubleSupported} = ?scaleB_hole
  logB @{DoubleSupported} = ?logB_hole
  addition @{rdm} @{DoubleSupported} @{DoubleSupported} @{DoubleSupported} = ?addition_hole
  subtraction @{rdm} @{DoubleSupported} @{DoubleSupported} @{DoubleSupported} = ?subtraction_hole
  multiplication @{rdm} @{DoubleSupported} @{DoubleSupported} @{DoubleSupported} = ?multiplication_hole
  division @{rdm} @{DoubleSupported} @{DoubleSupported} @{DoubleSupported} = ?division_hole
  squareRoot @{rdm} @{DoubleSupported} @{DoubleSupported} = ?squareRoot_hole
  fusedMultiplyAdd @{rdm} @{DoubleSupported} @{DoubleSupported} @{DoubleSupported} @{DoubleSupported} = ?fusedMultiplyAdd_hole
  convertFromInt @{rdm} @{DoubleSupported} = ?convertFromInt_hole
  convertToInteger rdm @{DoubleSupported} = ?convertToInteger_hole
  convertToIntegerExact rdm @{DoubleSupported} = ?convertToIntegerExact_hole
  convertFormat @{rdm} @{DoubleSupported} @{DoubleSupported} = ?convertFormat_hole
  convertFromDecimalCharacter @{rdm} @{DoubleSupported} = ?convertFromDecimalCharacter_hole
  convertToDecimalCharacter @{rdm} cspec @{DoubleSupported} = ?convertToDecimalCharacter_hole cspec
  convertFromHexCharacter @{rdm} @{DoubleSupported} = ?convertFromHexCharacter_hole
  convertToHexCharacter @{rdm} cspec @{DoubleSupported} = ?convertToHexCharacter_hole cspec
  negate @{DoubleSupported} = prim__ieee_negate_Double
  abs @{DoubleSupported} = ?abs_hole
  copySign @{DoubleSupported} = ?copySign_hole

  isSignMinus @{DoubleSupported} = intToBool . prim__isSignMinus_Double
  isNormal @{DoubleSupported} = intToBool . prim__isNormal_Double
  isFinite @{DoubleSupported} = intToBool . prim__isFinite_Double
  isZero @{DoubleSupported} = intToBool . prim__isZero_Double
  isSubnormal @{DoubleSupported} = intToBool . prim__isSubnormal_Double
  isInfinite @{DoubleSupported} = intToBool . prim__isInfinite_Double
  isNaN @{DoubleSupported} = intToBool . prim__isNaN_Double
  isSignaling @{DoubleSupported} = intToBool . prim__isSignaling_Double
