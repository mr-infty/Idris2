module Data.IEEE754

import Data.So

%default total

-- Types used to encode floating point numbers
||| The type of floating point number signs.
data Sign = Negative | Positive

||| The type of floating point number mantissas.
data Mantissa : Type where
  MkMantissa : (x : Int) ->
               So (0 <= x) =>
               So (x <= 9007199254740991) => -- x <= 2**53 - 1
               Mantissa


||| The type of floating point number exponents.
data Exponent : Type where
  MkExponent : (x : Int) ->
               So (-1074 <= x) => -- (1 - 1023) - (53 - 1) <= x
               So (x <= 971) =>   -- x <= 1023 - (53 - 1)
               Exponent

-- Constants related to the format and encoding of floating point numbers
||| The precision, i.e. number of significand digits of floating point numbers.
precision : Int
precision = 53

||| The biggest valid mantissa.
maxMantissa : Mantissa
maxMantissa = MkMantissa 9007199254740991

||| The biggest valid exponent.
maxExponent : Exponent
maxExponent = MkExponent 971

||| The smallest valid exponent.
minExponent : Exponent
minExponent = MkExponent (negate 1074)

||| Constructs a (finite) floating point number from a sign, a mantissa (significand) and an exponent.
encodeFloat : Sign -> Mantissa -> Exponent -> Double

-- Predicates and Constants
||| Evaluates to `True` if and only if the argument is a NaN.
public export
isNaN : Double -> Bool

||| Evaluates to `True` if and only if the argument is infinite. Disagrees with `not . isInfinite` in general.
public export
isInfinite : Double -> Bool

||| Evaluates to `True` if and only if the argument is finite. Disagrees with `not (isInfinite x)` in general.
public export
isFinite : Double -> Bool

||| Evaluates to `True` if and only if the argument is zero, i.e. equals to `-0.0` or `0.0`.
public export
isZero : Double -> Bool

||| Evaluates to `True` if and only if the argument is normal, i.e. non-zero, finite and of magnitude greater than or equal to `smallestPositiveNormalNumber`.
public export
isNormal : Double -> Bool

||| Evaluates to `True` if and only if the argument is subnormal, i.e. non-zero, finite and of magnitude less than `smallestPositiveNormalNumber`.
public export
isSubnormal : Double -> Bool

||| The smallest positive floating point number that is normal, i.e. is representable with full precision.
public export
smallestPositiveNormalNumber : Double

||| The biggest floating point number, i.e. plus infinity.
public export
plusInfinity : Double
plusInfinity = 1.0 / 0.0

||| The smallest floating point number, i.e. minus infinity.
public export
minusInfinity : Double
minusInfinity = negate plusInfinity

||| A NaN, i.e. a floating point number for which `isNaN` evaluates to `True`.
public export
aNaN : Double
aNaN = minusInfinity + plusInfinity

||| The smallest positive floating point number. Equals the negative of `smallestPositiveNumber`.
public export
smallestPositiveNumber : Double

||| The biggest negative floating point number. Equals the negative of `smallestPositiveNumber`.
public export
biggestNegativeNumber : Double

||| The biggest finite floating point number. Equals the negative of `smallestFiniteNumber`.
public export
biggestFiniteNumber : Double

||| The smallest finite floating point number. Equals the negative of `biggestFiniteNumber`.
public export
smallestFiniteNumber : Double

||| The machine epsilon (unit round off), i.e. the smallest `x` such that `1+x > 1`.
public export
epsilon : Double

-- Implementation details of the floating point predicates and constants
%foreign "javascript:lambda: x => Number.isNaN(x) ? BigInt(1) : BigInt(0)"
         "scheme:ieee_isNaN"
prim__isNaN : Double -> Int

%foreign "javascript:lambda: x => Number.isFinite(x) && !Number.isNaN(x) ? BigInt(1) : BigInt(0)"
         "scheme:ieee_isInfinite"
prim__isInfinite : Double -> Int

%foreign "javascript:lambda: x => Number.isFinite(x) ? BigInt(1) : BigInt(0)"
         "scheme:ieee_isFinite"
prim__isFinite : Double -> Int

%foreign "javascript:lambda: x => (x == 0.0) ? BigInt(1) : BigInt(0)"
         "scheme:ieee_isZero"
prim__isZero : Double -> Int

%foreign "javascript:lambda: (s,m,e) => Number(s * m) * Math.pow(2, Number(e))"
         "scheme:ieee_encodeFloat"
prim__encodeFloat : Int -> Int -> Int -> Double

encodeFloat s (MkMantissa m) (MkExponent e) = prim__encodeFloat (case s of
                                                                   Negative => -1
                                                                   Positive => 1)
                                                                m
                                                                e
isNaN = intToBool . prim__isNaN
isInfinite = intToBool . prim__isInfinite
isFinite = intToBool . prim__isFinite
isZero = intToBool . prim__isZero
isNormal x = (isFinite x) && not (isZero x) && (abs x) >= smallestPositiveNormalNumber
isSubnormal x = (isFinite x) && not (isZero x) && (abs x) < smallestPositiveNormalNumber
smallestPositiveNormalNumber = encodeFloat Positive (MkMantissa 4503599627370496) minExponent --4503599627370496 = 2 ** 52 
smallestPositiveNumber = encodeFloat Positive (MkMantissa 1) minExponent
biggestNegativeNumber = negate smallestPositiveNumber
biggestFiniteNumber = encodeFloat Positive maxMantissa maxExponent
smallestFiniteNumber = negate biggestFiniteNumber
epsilon = encodeFloat Positive (MkMantissa 1) (MkExponent (negate (precision - 1)))
