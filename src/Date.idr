{-
 - A Meal Planner in Idris
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


||| This is a cut-down version of a date-time library I started earlier.
|||
||| The approach is taken from a discord conversation I had a few
||| months back.
|||
||| I'm doing more run-time checking here than I would like to do in
||| my stand-alone date-time library, in the interest of moving things
||| along.


||| Special thanks to Stephen Hoek and Kiana


module Date


import Data.Nat
import Data.Nat.Order.Properties
import Data.Fin
import Data.Fin.Extra
import Derive.Prelude
import JSON.Derive
import Language.Reflection.Util
import System.Clock


%default total
%language ElabReflection


||| A Year is just a natural number.
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

  ||| A natural number bounded to the number of days in a given year
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
    in (y * 365 + yOver4) `minus` yOver100 + yOver400

  {- Some useful constants -}
  public export DaysIn400Years : Nat ; DaysIn400Years = daysBefore 401
  public export DaysIn100Years : Nat ; DaysIn100Years = daysBefore 101
  public export DaysIn4Years   : Nat ; DaysIn4Years   = daysBefore 5


||| A month is an 8-bit unsigned integer between 1 and 12, inclusive.
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
  Days True  Jan = 31
  Days True  Feb = 29
  Days True  Mar = 31
  Days True  Apr = 30
  Days True  May = 31
  Days True  Jun = 30
  Days True  Jul = 31
  Days True  Aug = 31
  Days True  Sep = 30
  Days True  Oct = 31
  Days True  Nov = 30
  Days True  Dec = 31
  Days False Jan = 31
  Days False Feb = 28
  Days False Mar = 31
  Days False Apr = 30
  Days False May = 31
  Days False Jun = 30
  Days False Jul = 31
  Days False Aug = 31
  Days False Sep = 30
  Days False Oct = 31
  Days False Nov = 30
  Days False Dec = 31

  {-
  Days True  Feb = 29
  Days False Feb = 28
  Days _     Apr = 30
  Days _     Jun = 30
  Days _     Sep = 30
  Days _     Nov = 30
  Days _     _   = 31
  -}

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

  ||| Doing the opposite thing to both sides of a sum doesn't change
  ||| the total
  lemma1
    :  {n, r, x, b : Nat}
    -> (0 prf : n + r = b)
    -> ((n `minus` x) + (r + x) = b)
  lemma1 prf = ?lemma_rhs

  ||| This is also true if we just use S
  lemma2
    :  {n, r, b : Nat}
    -> (0 prf : (S n) + r = b)
    -> (n + (S r) = b)

  ||| Recursively search for the given month, leaving the
  ||| remainder as the 0-indexed day of the month
  public export
  findMonthAndDay
    : (leap : Bool)
    -> (n, r : Nat)
    -> (0 prf : n + r = Year.Days leap)
    -> (m : Month)
    -> DPair Month (Day leap)
  findMonthAndDay leap n r prf m =
    let days := Days leap m
    in case isLT n (Days leap m) of
      Yes dltdm  => (m ** natToFinLTE n dltdm)
      No  contra =>
        findMonthAndDay
          leap
          (assert_smaller n (n `minus` days))
          (r + days)
          (lemma1 prf)
          (nextMonth m)

  ||| Find the month and day for the given day of year.
  public export
  findDayOf
    : (leap : Bool)
    -> Year.Day leap
    -> DPair Month (Day leap)
  findDayOf leap doy = findMonthAndDay
    leap
    (finToNat doy)
    (S (finToNat (invFin doy)))
    (lemma2 (invFinSpec doy))
    Jan


||| A valid Gregorian Date, which correctly handles leap years.
|||
||| Month and days are represented as 0-based finite integers.
export
record Date where
  constructor MkDate
  year:  Nat
  month: Month
  day:   Month.Day (IsLeapYear year) month


namespace Date

  Show Date where
    show (MkDate y m d) =
      show y ++ "-" ++ show m ++ "-" ++ show (FS d)

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

  ||| Unpack the date into its unrefined components.
  public export
  unpack : Date -> (Nat, Nat, Nat)
  unpack (MkDate y m d) = (y, S (cast m), S (cast d))

  ||| Parse an iso date string into a Date
  public export
  parseDate : Parser String Date
  parseDate s = case forget $ split ('-' ==) s of
    [y, m, d] =>
      let
        y = stringToNatOrZ y
        m = stringToNatOrZ m
        d = stringToNatOrZ d
      in case pack y m d of
        Nothing => fail "Invalid date"
        Just d  => Right d
    _ => fail "Invalid date"

  ||| Convert a date into an ordinal number
  public export
  toOrdinal : Date -> Nat
  toOrdinal (MkDate y m d) =
    let
      leap := IsLeapYear y
      dim  := Month.Days leap m
      dby  := daysBefore y
      dbm  := daysBefore leap m
    in dby + cast dbm + cast d

{-
  dec31st : Nat -> Date

  ||| Construct a date from a non-zero ordinal number
  fromOrdinal : (o : Nat) -> {auto onz : NonZero o} -> Date
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
          year := pred year
          leap := IsLeapYear year
        in dec31st year
      else case IsLeapYear year of
        True  => let (m ** d) := findDayOf True (modFin n (Year.Days True))
                 in MkDate year m d
        False => let (m ** d) := findDayOf False (modFin n (Year.Days False))
                 in MkDate year m d


{-

||| Get the current system time as a Date
||| XXX: just returns dummy value for now
export
today : IO Date
today = do
  ct <- clockTime UTC
  let s = seconds ct
  putStrLn $ show s
  pure $ MkDate 2023 8 25


{- Implement common interfaces -}


export
Show Date where
  show d =
    let (y, m, d) = unpack d
    in "\{show y}-\{show m}-\{show d}"

export Eq Date       where x == y      = (unpack x) == (unpack y)
export Ord Date      where compare x y = compare (unpack x) (unpack y)
export ToJSON   Date where toJSON d    = string $ show d
export FromJSON Date where fromJSON    = withString "Date" parseDate
