||| Concrete date/time and related types.


{-
 Inspired from Python's Lib/datetime.py.
 
 Gregorian calendar indefinitely extended into the future. Unlike the
 python from which this is derived library, this module uses natural
 numbers to represent dates: Dates before Jan 1, 1 C.E are
 unrepresentable 
 
 In addition, this library makes an effort to prevent representation
 of invalid julian dates, such as:
 
 2023 Mar 32
 2023 Feb 29
 1000 Jan 0
 2024 Nov 31
 
 I.e. the day of month *must* be between 1 and the number of days in
 that month, for that year.
-}

module Date

import Data.Nat
import Decidable.Equality

%default total

||| Safe integer division with statically nonzero divisor
staticDiv 
  :  Nat 
  -> (divisor : Nat) 
  -> {auto prf : NonZero divisor} 
  -> Nat
staticDiv a b {prf} = divNatNZ a b prf

||| Safe integer modulo with statically nonzero divisor
staticMod 
  :  Nat 
  -> (divisor : Nat) 
  -> {auto prf : NonZero divisor} 
  -> Nat
staticMod a b {prf} = modNatNZ a b prf

||| Safe integer divmod with statically nonzero divisor
staticDivmod 
  :  Nat 
  -> (divisor : Nat) 
  -> {auto prf : NonZero divisor} 
  -> (Nat, Nat)
staticDivmod a b {prf} = divmodNatNZ a b prf

||| Return a non-zero constant together with a proof that it's not zero
constNZ
  :  (n : Nat)
  -> {auto prf : NonZero n}
  -> DPair Nat NonZero
constNZ n = MkDPair n prf

||| Abbreviated symbolic month
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

||| Return the previous month for the given month
prevMonth : Month -> Month
prevMonth Jan = Dec
prevMonth Feb = Jan
prevMonth Mar = Feb
prevMonth Apr = Mar
prevMonth May = Apr
prevMonth Jun = May
prevMonth Jul = Jun
prevMonth Aug = Jul
prevMonth Sep = Aug
prevMonth Oct = Sep
prevMonth Nov = Oct
prevMonth Dec = Nov

||| Return the next month for the given month
nextMonth : Month -> Month
nextMonth Jan = Feb
nextMonth Feb = Mar
nextMonth Mar = Apr
nextMonth Apr = May
nextMonth May = Jun
nextMonth Jun = Jul
nextMonth Jul = Aug
nextMonth Aug = Sep
nextMonth Sep = Oct
nextMonth Oct = Nov
nextMonth Nov = Dec
nextMonth Dec = Jan


||| Year -> True if leap year, else False
isLeap : (n : Nat) -> Bool
isLeap year = 
  let
    nthYear : (n : Nat) -> {auto prf : NonZero n} -> Bool
    nthYear n {prf} = (staticMod year n) == 0
  in 
    (nthYear 4) && (not (nthYear 100) || (nthYear 400))

||| Number of days in the given month and year
daysInMonth : Nat -> Month -> Nat
daysInMonth year Jan = 31
daysInMonth year Feb = if isLeap year then 29 else 28
daysInMonth year Mar = 31
daysInMonth year Apr = 30
daysInMonth year May = 31
daysInMonth year Jun = 30
daysInMonth year Jul = 31
daysInMonth year Aug = 31
daysInMonth year Sep = 30
daysInMonth year Oct = 31
daysInMonth year Nov = 30
daysInMonth year Dec = 31

||| Number of days before January 1st of the given year.
daysBeforeYear : (y : Nat) -> {auto _ : NonZero y} -> Nat
daysBeforeYear year =
  let y = pred year
  in y * 365 + (staticDiv y 4) + (staticDiv y 400)

||| Number of days in year preceding first day of month.
daysBeforeMonth : Nat -> Month -> Nat
daysBeforeMonth year Jan   = 0
daysBeforeMonth year month = 
  let
    prev = prevMonth month
    dim  = daysInMonth year prev
    -- assuming definition of prevMonth is correct, it will terminate:
    -- we eventually reach non-recursive Jan case. I am unsure how to
    -- prove this.
    dbm  = daysBeforeMonth year (assert_smaller year prev)
  in
    dim + dbm

||| Number of days inthe given year
daysInYear : (y : Nat) -> Nat
daysInYear y = if isLeap y then 366 else 365

||| A Julian date that cannot hold invalid dates
|||
||| e.g. 2023-Jan-0, 2023-Feb-29, 2012-Aug-35 
export
data Julian : Type where
  YMD
    :  (year   : Nat)
    -> (month  : Month)
    -> (day    : Nat)
    -> {auto _ : NonZero year}
    -> {auto _ : NonZero day}
    -> {auto _ : LTE day (daysInMonth year month) }
    -> Julian

||| Number of days in 400 years
DI400Y : Nat
DI400Y = daysBeforeYear 401

||| Number of days in 100 years
DI100Y : Nat
DI100Y = daysBeforeYear 101

||| Number of days in 4 years
DI4Y : Nat
DI4Y = daysBeforeYear 5

-- XXX: convert these into proofs
-- assert DIY4    == 365 + 1
-- assert DIY400Y == 4 * DI100Y + 1
-- assert DI100Y  == 25 * DI4Y - 1

||| Recursively find month and day for given year and day of year
||| 
||| Note: The day here is zero-indexed!
findMonthAndDay 
  :  (year     : Nat) 
  -> (residual : Nat)
  -> {auto _   : LTE residual (daysInYear year)}
  -> (Month, Nat)
findMonthAndDay year month = 
  let diy = daysInYear year
  in  fmdRec year residual Jan 
where 
  fmdRec 
    :  (year     : Nat) 
    -> (residual : Nat) 
    -> (month    : Month) 
    -> {auto _   : LTE residual (daysInYear year)}
    -> (Month, Nat)
  fmdRec year residual month =
    let  dim = daysInMonth year month
    in if   residual < dim
       then (month, residual)
       else fmdRec year (residual `minus` dim) (nextMonth month)
  

{-
||| Gregorian ordinal to (y, m, d) typle, Considering 1-Jan-1 as day 1
ord2ymd 
  :  (ordinal : Nat) 
  -> {auto prf : NonZero ordinal}
  -> Julian
ord2ymd ordinal =
  let
    n         := pred ordinal
    (n400, n) := n `staticDivmod` DI400Y
    (n100, n) := n `staticDivmod` DI100Y
    (n4,   n) := n `staticDivmod` DI4Y
    (n1,   n) := n `staticDivmod` 365
    year      := (n400 * 400 + 1) + (n100 * 100) + (n4 * 4) + n1
  in if (n1 == 4) || (n100 == 4)
  then YMD (?hole (pred year)) Dec 31
  else 
    let (month, day) = findMonthAndDay year n Dec
    in YMD (?hole2 year) month (?hole3 (S day))

{-

||| Concrete date type
export 
data Date : Type where
  -- choosing to represent this internally
  MkDate
    :  (ord     : Nat) 
    -> {auto _  : NonZero ord}
    -> Date
    
public export
fromOrdinal
  :  (ord : Nat)
  -> {auto _ : NonZero ord}
  -> Date
fromOrdinal ord = MkDate ord

||| Proleptic Gregorian ordinal for the year, month and day.
|||
||| January 1 of year 1 is day 1.
public export
fromYMD 
  :  (year   : Nat)
  -> (month  : Month)
  -> (day    : Nat)
  -> {auto _ : NonZero year}
  -> {auto _ : NonZero day}
  -> {auto _ : LTE day (daysInMonth year month)}
  -> Maybe Date
fromYMD year month day =
  let
    dby = daysBeforeYear year
    dbm = daysBeforeMonth year month
    ord = dby + dbm + day
  in case ord of
    Z   => Nothing
    S n => Just (MkDate (S n))

{-
||| Proleptic Gregorian ordinal for the year, month and day.
|||
||| January 1 of year 1 is day 1.
public export
toOrdinal : Date -> Nat
toOrdinal (MkDate ord) = ord

||| Project the year, month, and day from a Date.
public export
toYMD : Date -> (Nat, Month, Nat)
toYMD (MkDate date) = ord2ymd date

||| Project the year from a Date.
public export
year : Date -> Nat
year date = fst (toYMD date)

||| Project the month from a Date
public export
month : Date -> Month
month date = let (_, m, _ ) := (toYMD date) in m

||| Project the day from a Date
public export
day : Date -> Month
day date = let (_, _, d) := (toYMD date) in d


-}
