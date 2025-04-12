
{-
 - idris-datetime
 -
 - Copyright (C) 2022 Brandon Lewis
 -
 - This program is free software: you can redistribute it and/or modify
 - it under the terms of the GNU Affero General Public License as
 - published by the Free Software Foundation, either version 3 of the
 - License, or (at your option) any later version.
 -
 - This program is distributed in the hope that it will be useful,
 - but WITHOUT ANY WARRANTY; without even the implied warranty of
 - MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 - GNU Affero General Public License for more details.
 -
 - You should have received a copy of the GNU Affero General Public License
 - along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}


||| This is modeled after Python's datetime module, except key
||| operations are total.
|||
||| I represent ordinals as Natural numbers, because Data.Nat defines
||| so many theorems and lemmas which are not defined for
||| `Integer`. If there's a way to re-formulate this code for integers
||| without sacrificing totality, let me know.
|||
||| The approach is taken from a discord conversation I had a few
||| months back.
|||
||| Special thanks to Stephen Hoek and Kiana for all their help on
||| Discord.


module Date


import Data.Nat
import Data.Nat.Equational
import Data.Nat.Order.Properties
import Data.Fin
import Data.Fin.Extra
import Derive.Prelude
import JSON.Derive
import Language.Reflection.Util
import Syntax.PreorderReasoning
import System.Clock


%default total
%language ElabReflection

{- Transforms required for acceptable performance ************************** -}

%transform "divNatNZ" divNatNZ x y _ =
  integerToNat $ div (natToInteger x) (natToInteger y)
%transform "modNatNZ" modNatNZ x y _ =
  integerToNat $ mod (natToInteger x) (natToInteger y)
%transform "divmodNatNZ" divmodNatNZ x y _ =
  let
    x = natToInteger x
    y = natToInteger y
    d = integerToNat (div x y)
    m = integerToNat (mod x y)
  in (d, m)


||| Convert a `NonZero n` to an `LTE 1 n`
0 nonZeroToLTE : NonZero n -> LTE 1 n
nonZeroToLTE (SIsNonZero) = LTESucc LTEZero


||| Convert an `LTE 1 n` to a `NonZero n`
0 LTEToNonZero : LTE 1 n -> NonZero n
LTEToNonZero (LTESucc x) = SIsNonZero

||| Adding a nat to a `NonZero n` preserves nonzero status
0 nonZeroPlus : (m : Nat) -> NonZero n -> NonZero (n + m)
nonZeroPlus 0 SIsNonZero = SIsNonZero
nonZeroPlus (S k) SIsNonZero = SIsNonZero

ltzToNonZ : Lt 0 a -> NonZero a
ltzToNonZ (LTESucc x) = ItIsSucc

||| Subtracting a bounded number also preserves nonzero status
|||
||| Proof suplied by FFFluoride from Discord.
0 nonZeroMinusLT : NonZero n -> LT m n -> NonZero (n `minus` m)
nonZeroMinusLT x y = nzLTrewrite m n y
where
  nzLTrewrite : (m, n : Nat) -> LT m n -> NonZero (n `minus m)
  nzLTrewrite m n x = ltzToNonZ (minusPos x)



{- Implementation ********************************************************** -}

||| A Year is just a Nat, so there's no special type alias.
|||
||| We use natural numbers here, rather than integers, because there
||| are more theorems available for working with Nat and Fin.
namespace Year

  ||| Returns true if the given year is a leap year.
  public export
  IsLeapYear : (n: Nat) -> Bool
  IsLeapYear year =
    let
      mod4   := (modNatNZ year 4   SIsNonZero) == 0
      mod100 := (modNatNZ year 100 SIsNonZero) == 0
      mod400 := (modNatNZ year 400 SIsNonZero) == 0
    in
      mod4 && ((not mod100) || mod400)

  ||| Return the number of days in the given year
  public export
  Days : Bool -> Nat
  Days True = 366
  Days False = 365

  ||| The number of days in a year is nonzero
  |||
  ||| This obvious fact isn't transparent to Idris.  It also doesn't
  ||| work if it's given a 0 quantity, so it's not marked as erased.
  public export
  daysNZ : (leap : Bool) -> NonZero (Year.Days leap)
  daysNZ False = SIsNonZero
  daysNZ True  = SIsNonZero

  ||| A natural number bounded to the number of days in a given year.
  public export
  0 Day : Bool -> Type
  Day leap = Fin (Days leap)

  ||| Number of days before Janary 1st of year.
  public export
  daysBefore : (y : Nat) -> Nat
  daysBefore Z     = 0
  daysBefore (S y) =
    let
      yOver4    := divNatNZ y 4   SIsNonZero
      yOver100  := divNatNZ y 100 SIsNonZero
      yOver400  := divNatNZ y 400 SIsNonZero
    in (y * 365) + yOver4 + yOver400 `minus` yOver100

  {- Some useful constants -}
  public export DaysIn400Years : Nat ; DaysIn400Years = daysBefore 401
  public export DaysIn100Years : Nat ; DaysIn100Years = daysBefore 101
  public export DaysIn4Years   : Nat ; DaysIn4Years   = daysBefore 5


||| Symbolic month names
public export
data Month
  = Jan
  | Feb
  | Mar
  | Apr
  | May
  | Jun
  | Jul
  | Aug
  | Sep
  | Oct
  | Nov
  | Dec

namespace Month
  %runElab derive "Month" [Show, Eq, Ord]

  ||| Convert a Month to a natural number < 12
  monthToFin : Month -> Fin 12
  monthToFin Jan = 0
  monthToFin Feb = 1
  monthToFin Mar = 2
  monthToFin Apr = 3
  monthToFin May = 4
  monthToFin Jun = 5
  monthToFin Jul = 6
  monthToFin Aug = 7
  monthToFin Sep = 8
  monthToFin Oct = 9
  monthToFin Nov = 10
  monthToFin Dec = 11

  ||| Convert a natural number < 12 to a Month.
  finToMonth : Fin 12 -> Month
  finToMonth 0 = Jan
  finToMonth 1 = Feb
  finToMonth 2 = Mar
  finToMonth 3 = Apr
  finToMonth 4 = May
  finToMonth 5 = Jun
  finToMonth 6 = Jul
  finToMonth 7 = Aug
  finToMonth 8 = Sep
  finToMonth 9 = Oct
  finToMonth 10 = Nov
  finToMonth 11 = Dec

  {- support some useful casts -}
  public export Cast Month    (Fin 12) where cast = monthToFin
  public export Cast (Fin 12) Month    where cast = finToMonth
  public export Cast Month    Nat      where cast = finToNat . monthToFin

  ||| The previous month, wrapping around to December
  public export
  prevMonth : Month -> Month
  prevMonth m = finToMonth $ (monthToFin m) - 1

  ||| The next month, wrapping around to Jan
  public export
  nextMonth : Month -> Month
  nextMonth m = finToMonth $ finS $ monthToFin m

  ||| The number of days of the given month and leap status.
  %inline public export
  Days : Bool -> Month -> Nat
  Days True  Feb = 29
  Days False Feb = 28
  Days _     Apr = 30
  Days _     Jun = 30
  Days _     Sep = 30
  Days _     Nov = 30
  Days _     _   = 31

  ||| A valid day of a given month and leap status
  public export
  0 Day : Bool -> Month -> Type
  Day leap month = Fin (Days leap month)

  public export
  daysBeforeRec : (leap : Bool) -> (m : Month) -> Nat
  daysBeforeRec leap Jan = Z
  daysBeforeRec leap m =
    let pm = prevMonth m
    in Days leap pm + daysBeforeRec leap (assert_smaller m pm)

  ||| The number of days in the year before the first of the given month
  public export
  daysBefore : (leap : Bool) -> Month -> Year.Day leap
  daysBefore True  m = modFin (daysBeforeRec True m) (Year.Days True)
  daysBefore False m = modFin (daysBeforeRec False m) (Year.Days False)

  ||| prove that it's okay to re-arrange the braces like so
  minusAssoc
    : (n,r,x : Nat)
    -> LTE x n
    -> (n `minus` x) + r = (n + r) `minus` x
  minusAssoc n r Z _ = trans (cong (+r) $ minusZeroRight n) (sym $ minusZeroRight (n + r))
  minusAssoc (S n) r (S x) (LTESucc ok) = minusAssoc n r x ok

  ||| prove that we can 'move' from the value to its complement
  loopInvariant
    :  {0 n, r, x, b : Nat}
    -> LTE x n -- these need to be available at runtime
    -> n + r = b
    -> ((n `minus` x) + (r + x) = b)
  loopInvariant ok eq = Calc $
    |~ (n `minus` x) + (r + x)
    ~~ (n `minus` x) + r + x    ...(plusAssociative (n `minus` x) r x)
    ~~ ((n + r) `minus` x) + x  ...(cong (+x) $ minusAssoc n r x ok)
    ~~ n + r                    ...(plusMinusLte x (n + r) (transitive ok (lteAddRight n)))
    ~~ b                        ...(eq)

  ||| Recursively search for the given month, leaving the
  ||| remainder as the 0-indexed day of the month.
  |||
  ||| `n` is the day of the year
  ||| `r` is its complement, modulo `Year.Days leap`
  |||
  ||| `prf` is a proof that establishes that `n + r = Year.Days leap`,
  ||| i.e. the "loop invariant" we must maintain.
  |||
  ||| `m` is used to keep track of the month as we recurse. We search
  ||| in increasing order, so kick off the recusrion by passing `Jan`,
  ||| or all hell will break loose.
  findMonthAndDay
    :  (leap : Bool)
    -> (n, r : Nat)
    -> (0 prf : n + r = Year.Days leap)
    -> (m : Month)
    -> DPair Month (Day leap)
  findMonthAndDay leap n r prf m =
    case isLT n (Days leap m) of
      Yes was_less  => (m ** natToFinLTE n was_less)
      No  not_less =>
        findMonthAndDay
          leap
          (assert_smaller n (n `minus` (Days leap m)))
          (r + (Days leap m))
          (loopInvariant (fromLteSucc $ notLTEImpliesGT not_less) prf)
          (nextMonth m)

  ||| Converts a library theorem to the form we need in `findDayOf`.
  |||
  ||| complementSpec is almost the theorem we need, but gives:
  |||   (S n) + r = b
  |||
  ||| we need:
  |||    n + (S r) = b`
  |||
  ||| We want the `S` on the complement side, not on the day value.
  0 succPlusAssoc
    :  {0 n, r, b : Nat}
    -> (0 prf : (S n) + r     = b)
    -> (        n     + (S r) = b)
  succPlusAssoc prf = rewrite sym (plusSuccRightSucc n r) in prf

  ||| Find the month and day for the given day of year.
  |||
  ||| This returns a dependent pair of (Month ** Day).
  |||
  ||| Note: Day is 0-based!
  public export
  findDayOf
    : (leap : Bool)
    -> Year.Day leap
    -> DPair Month (Day leap)
  findDayOf leap doy = findMonthAndDay
    leap
    --- complementSpec helps decompose a `Fin n` into a value and its
    --- complement `mod n`, along with a proof of the loop invariant
    --- for `findMonthAndDay`.
    (finToNat doy)
    (S (finToNat (complement doy)))
    (succPlusAssoc (complementSpec doy))
    Jan

  ||| Make a (Month ** Day) pair from a static 1-based day.
  |||
  ||| Note: The Day field of the return value is 0-based.
  public export
  day
    : (leap : Bool)
    -> (m : Month)
    -> (d : Nat)
    -> {auto 0 dnZ : NonZero d}
    -> {auto 0 dlt : LTE d (Days leap m)}
    -> DPair Month (Month.Day leap)
  day True  m (S d) = (m ** natToFinLT d)
  day False m (S d) = (m ** natToFinLT d)

  ||| Simplify making this specific day of the year.
  public export
  dec31st : (leap : Bool) -> DPair Month (Month.Day leap)
  dec31st True  = day True  Dec 31
  dec31st False = day False Dec 31


||| A valid Gregorian Date, which correctly handles leap years.
|||
||| Month is symbolic, and days are represented as 0-based finite
||| integers which depend on the month and leap year status.
|||
||| You can't make a date wich stores a `Apr 31`, for example. Or `Feb
||| 29` when the year isn't a leap year.
|||
||| Note that `Month.Day` stores days as 0-based integers. So `Jan
||| 1st` is represented as `Jan FZ`. The convenience api handles this
||| for you, so you shouldn't have to worry about it unless you
||| directly construct or destruct a Date, which I am trying to
||| prevent here.
export
record Date where
  constructor MkDate
  year:  Nat
  month: Month
  day:   Month.Day (IsLeapYear year) month


namespace Date
  ||| Construct a date from unrefined components.
  |||
  ||| This may fail if the month or day fall outside expected intervals.
  |||
  ||| Note that, internally, days are represented as 0-based finite
  ||| integers.
  public export
  pack : Nat -> Nat -> Nat -> Maybe Date
  pack _ Z _ = Nothing
  pack _ _ Z = Nothing
  pack y (S m) (S d) = do
    m <- natToFin m 12
    d <- natToFin d (Month.Days (IsLeapYear y) (cast m))
    Just $ MkDate y (cast m) (cast d)

  ||| Unpack the date into its components.
  public export
  unpack : Date -> (Nat, Nat, Nat)
  unpack (MkDate y m d) = (y, S (cast m), S (cast d))

  ||| Parse an iso date string to a date
  public export
  fromString : String -> Maybe Date
  fromString s = case forget $ split ('-' ==) s of
    [y, m, d] =>
      let
        y = stringToNatOrZ y
        m = stringToNatOrZ m
        d = stringToNatOrZ d
      in pack y m d
    _ => Nothing

  ||| Parse an iso date string from JSON.
  public export
  parseDate : Parser String Date
  parseDate s = case fromString s of
    Nothing => fail "Invalid Date"
    Just d  => Right d

  ||| Convert a date into an ordinal number
  public export
  toOrdinal : Date -> Nat
  toOrdinal (MkDate y m d) =
    let
      leap := IsLeapYear y
      dim  := Month.Days leap m
      dby  := daysBefore y
      dbm  := daysBefore leap m
    in dby + cast dbm + S (cast d)

  ||| Construct a date from a non-zero ordinal number
  public export
  fromOrdinal : (o : Nat) -> {auto 0 onz : NonZero o} -> Date
  fromOrdinal (S n) =
    let
      (n400, n) := divmodNatNZ n DaysIn400Years SIsNonZero
      (n100, n) := divmodNatNZ n DaysIn100Years SIsNonZero
      (n4,   n) := divmodNatNZ n DaysIn4Years   SIsNonZero
      (n1,   n) := divmodNatNZ n 365            SIsNonZero
      year      := (n400 * 400 + 1) + (n100 * 100) + n4 * 4 + n1
    in
      if (n1 == 4) || (n100) == 4
      then
        let
          year     := pred year
          (m ** d) := dec31st (IsLeapYear year)
        in MkDate year m d
      else
        let
          (m ** d) := findDayOf
            (IsLeapYear year)
            (modFin n (Year.Days (IsLeapYear year)) @{daysNZ _})
        in MkDate year m d

  ||| Create a date from static data.
  public export
  date
    :  (y : Nat)
    -> (m : Month)
    -> (d : Nat)
    -> {auto 0 dnz : NonZero d}
    -> {auto 0 dlt : LTE d (Month.Days (IsLeapYear y) m)}
    -> Date
  date y m d =
    let (m ** d) := day (IsLeapYear y) m d
    in MkDate y m d

  ||| Date representing the true beginning of the unverse.
  epochStart : Nat
  -- XXX: works, but takes too long to typechceck
  -- epochStart = toOrdinal $ date 1970 Jan 1
  epochStart = 719163

  ||| Construct a date from a unix timestamp (in seconds)
  public export
  fromUnixTime : Nat -> Date
  fromUnixTime s =
    fromOrdinal (epochStart + (divNatNZ s 86400 SIsNonZero))

  ||| Convert date to an iso string
  public export
  toString : Date -> String
  toString d = let (y, m, d) := unpack d in "\{show y}-\{show m}-\{show d}"

  {- Implement common interfaces -}
  public export Show     Date where show        = toString
  public export Eq       Date where x == y      = (unpack x) == (unpack y)
  public export Ord      Date where compare x y = compare (unpack x) (unpack y)
  public export ToJSON   Date where toJSON d    = string $ show d
  public export FromJSON Date where fromJSON    = withString "Date" parseDate

  ||| Proof that the ordinal of a date is always nonzero
  |||
  ||| This is true because ordinals are Nats, and 1-Jan-1 is ordinal
  ||| 1. The implementation explicitly adds one to the day field, so
  ||| the value can never be less than one. This wouldn't be true for
  ||| proleptic ordinals, which are integers. On the other hand if
  ||| ordinals were integers, we wouldn't need this proof.
  0 toOrdinalNZ : (d : Date) -> NonZero (toOrdinal d)
  -- also true, but again not sure how to prove this

  ||| Proof that adding a nat to an ordinal will be always be nonzero
  0 toOrdinalPlusNNZ
    :  {auto 0 d : Date}
    -> {auto 0 n : Nat}
    -> NonZero ((toOrdinal d) + n)
  toOrdinalPlusNNZ {d} = nonZeroPlus n (toOrdinalNZ d)

  ||| Proof that subtracting `n` from a date is nonzero if `n` is less
  ||| than the date's ordinal representation.
  0 toOrdinalMinusNNZ
    :  {auto 0 d      : Date}
    -> {auto 0 n      : Nat}
    -> {auto 0 nvalid : LT n (toOrdinal d)}
    -> NonZero ((toOrdinal d) `minus` n)
  toOrdinalMinusNNZ {d} = nonZeroMinusLT (toOrdinalNZ d) nvalid

  ||| The date that is `n` days after the given date
  public export
  daysAfter : Nat -> Date -> Date
  daysAfter n d = fromOrdinal ((toOrdinal d) + n) {onz = toOrdinalPlusNNZ}

  ||| The date that is `n` days before the given date, stopping at `1 Jan 1`
  daysBefore : Nat -> Date -> Date
  daysBefore n d = case isLT n (toOrdinal d) of
    Yes prf => fromOrdinal ((toOrdinal d) `minus` n) {onz = toOrdinalMinusNNZ}
    No  _   => MkDate 1 Jan 1

  ||| Subtracting two dates yields a natural (in days)
  (-) : (a : Date) -> (b : Date) -> Nat
  (-) x y = (toOrdinal x) `minus` (toOrdinal y)


||| Get the current system time as a Date
export
today : IO Date
today = do
  ct <- clockTime UTC
  pure $ fromUnixTime $ cast $ seconds ct


||| A short interactive test of the library
partial
main : IO ()
main = do
  d <- today
  putStrLn $ show d
  main
