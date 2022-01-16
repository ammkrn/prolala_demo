import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Data.List.Basic
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Nat.Gcd
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Init.Set
import Mathlib.Init.SetNotation
import Prolala.Util

namespace Time

/- The number of nanoseconds in one second -/
abbrev oneSecondNanos : Nat := 1000000000

/- The number of nanoseconds in one minute -/
abbrev oneMinuteNanos : Nat := 60000000000

/- The number of nanoseconds in one hour -/
abbrev oneHourNanos : Nat := 3600000000000

/- The number of nanoseconds in one day -/
abbrev oneDayNanos : Nat := 86400000000000

/- The number of nanoseconds in one week -/
abbrev oneWeekNanos : Nat := 604800000000000

abbrev oneYearNanos : Nat := 31536000000000000

/- Every year that is exactly divisible by four is a leap year, except for years that 
   are exactly divisible by 100, but these centurial years are leap years if they 
   are exactly divisible by 400. For example, the years 1700, 1800, and 1900 are not 
   leap years, but the years 1600 and 2000 are.
       — United States Naval Observatory  -/
@[reducible] def isLeapYear (y : Nat) : Prop := (y % 4 = 0 ∧ y % 100 ≠ 0) ∨ (y % 400 = 0)

example : ¬isLeapYear 1700 := by decide
example : ¬isLeapYear 1800 := by decide
example : ¬isLeapYear 1900 := by decide
example : isLeapYear 1600 := by decide
example : isLeapYear 2000 := by decide
example : isLeapYear 0 := by decide

@[reducible] def numDaysInGregorianYear (y : Nat) : Nat := 365 + (if isLeapYear y then 1 else 0)

theorem num_days_in_gregorian_year_eq (n : Nat) : (numDaysInGregorianYear n = 365) ∨ (numDaysInGregorianYear n = 366) := by
  byCases h : isLeapYear n <;> simp only [numDaysInGregorianYear, h]

theorem num_days_in_gregorian_year_pos (n : Nat) : 0 < numDaysInGregorianYear n :=  
  match num_days_in_gregorian_year_eq n with
  | Or.inl hl => by rw [hl]; apply Nat.zero_lt_succ 
  | Or.inr hr => by rw [hr]; apply Nat.zero_lt_succ

/- In a 400 year block (e.g. 0-399 inclusive), there are 97 leap years, so 
   (366 * 97) + (365 * (400 - 97)) = 146097 days -/
abbrev daysIn400Group : Nat := 146097
abbrev daysIn100Group (year : Nat) : Nat := 36524 + if isLeapYear year then 1 else 0
abbrev daysIn4Group (year : Nat) : Nat := 1460 + if isLeapYear year then 1 else 0
abbrev daysIn100GroupLeap : Nat := 36525
abbrev daysIn100GroupNoLeap : Nat := 36524
abbrev daysIn4GroupLeap : Nat := 1461
abbrev daysIn4GroupNoLeap : Nat := 1460

/- A duration in nanoseconds. Arithmetic behaves as `Nat`. -/
structure Duration where
  val : Nat

instance : Add Duration where
  add a b := ⟨a.val + b.val⟩ 

instance : Sub Duration where
  sub a b := ⟨a.val - b.val⟩ 

instance : Mul Duration where
  mul a b := ⟨a.val * b.val⟩ 

instance : Mod Duration where
  mod a b := ⟨a.val % b.val⟩ 

instance : HMod Duration Nat Duration where
  hMod a n := ⟨a.val % n⟩ 

instance : Div Duration where
  div a b := ⟨a.val / b.val⟩ 

instance : Pow Duration Duration where
  pow a b := ⟨a.val ^ b.val⟩ 

instance : Pow Duration Nat where
  pow a n := ⟨a.val ^ n⟩ 

instance : LT Duration where
  lt := InvImage Nat.lt Duration.val

instance : LE Duration where
  le := InvImage Nat.le Duration.val

theorem Duration.le_def {d₁ d₂ : Duration} : (d₁ <= d₂) = (d₁.val <= d₂.val) := rfl
theorem Duration.lt_def {d₁ d₂ : Duration} : (d₁ < d₂) = (d₁.val < d₂.val) := rfl

theorem Duration.le_refl (d : Duration) : d <= d := Nat.le_refl d.val

theorem Duration.monotone {d₁ d₂ : Duration} : d₁.val <= d₂.val -> d₁ <= d₂ := 
  fun h => (Duration.le_def) ▸ h

theorem Duration.val_eq_of_eq : ∀ {d1 d2 : Duration} (h : d1 = d2), d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem Duration.eq_of_val_eq : ∀ {d1 d2 : Duration} (h : d1.val = d2.val), d1 = d2
| ⟨_⟩, _, rfl => rfl

instance : DecidableEq Duration
| ⟨v⟩, ⟨v'⟩ =>
  if h:v = v' 
  then isTrue <| congrArg Duration.mk h
  else isFalse (fun hf => Duration.noConfusion hf (fun hh => absurd hh h))

instance (a b : Duration) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : Duration) : Decidable (a <= b) := inferInstanceAs (Decidable (a.val <= b.val))
  
def Duration.nanos (d : Duration) : Nat := d.val % oneSecondNanos
def Duration.seconds (d : Duration) : Nat := d.val / oneSecondNanos
def Duration.minutes (d : Duration) : Nat := d.val / oneMinuteNanos
def Duration.hours (d : Duration) : Nat := d.val / oneHourNanos
def Duration.days (d : Duration) : Nat := d.val / oneDayNanos
def Duration.weeks (d : Duration) : Nat := d.val / oneWeekNanos
def Duration.years (d : Duration) : Nat := d.val / (365 * oneDayNanos)

def Duration.fromNanos (n : Nat) : Duration := ⟨n⟩ 
def Duration.fromSeconds (n : Nat) : Duration := ⟨n * oneSecondNanos⟩
def Duration.fromMinutes (n : Nat) : Duration := ⟨n * oneMinuteNanos⟩ 
def Duration.fromHours (n : Nat) : Duration := ⟨n * oneHourNanos⟩ 
@[reducible] def Duration.fromDays (n : Nat) : Duration := ⟨n * oneDayNanos⟩ 

theorem Duration.from_days_monotone {n₁ n₂ : Nat} (h : n₁ <= n₂) : Duration.fromDays n₁ <= Duration.fromDays n₂ := 
  Duration.monotone <| Nat.mul_le_mul_right oneDayNanos h


abbrev Duration.oneDay : Duration := ⟨oneDayNanos⟩
def Duration.fromWeeks (n : Nat) : Duration := ⟨n * oneWeekNanos⟩
/- May or may not keep this -/
@[irreducible] def Duration.fromYears (n : Nat) : Duration := ⟨n * oneYearNanos⟩

example : (Duration.fromSeconds 100).seconds = 100 := rfl
example : (Duration.fromDays 100).days = 100 := rfl
example : (Duration.fromDays 2).hours = 48 := rfl
example : (Duration.fromDays 35).weeks = 5 := rfl
example : (Duration.fromWeeks 12).days = 84 := rfl

instance (n : Nat) : OfNat Duration n where
  ofNat := ⟨n⟩ 

-- PnS.nanos
def Duration.toString (d : Duration) : String := 
  let secs := String.leftpad 2 '0' s!"{d.seconds}"
  let nanos := String.leftpad 9 '0' s!"{d.nanos}"
  s!"P{secs}.{nanos}S"

instance : ToString Duration where
  toString := Duration.toString

structure Year where
  val : Nat
deriving DecidableEq, Repr

instance (n : Nat) : OfNat Year n where
  ofNat := Year.mk n

instance : LE Year where
  le := InvImage Nat.le Year.val

instance : LT Year where
  lt := InvImage Nat.lt Year.val

theorem Year.le_def {y y' : Year} : (y <= y') = (y.val <= y'.val) := rfl
theorem Year.lt_def {y y' : Year} : (y < y') = (y.val < y'.val) := rfl

instance (y y' : Year) : Decidable (y <= y') := inferInstanceAs (Decidable (y.val <= y'.val))
instance (y y' : Year) : Decidable (y < y') := inferInstanceAs (Decidable (y.val < y'.val))

instance : ToString Year where
  toString y := ToString.toString y.val

/- Month is a value `m : Nat`, 0 < m < 13. -/
structure Month where
  val : Nat
  isGt : 0 < val
  isLt : val < 13

instance : ToString Month where
  toString m := ToString.toString m.val

instance : OfNat Month (nat_lit 1) := ⟨⟨1, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 2) := ⟨⟨2, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 3) := ⟨⟨3, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 4) := ⟨⟨4, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 5) := ⟨⟨5, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 6) := ⟨⟨6, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 7) := ⟨⟨7, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 8) := ⟨⟨8, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 9) := ⟨⟨9, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 10) := ⟨⟨10, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 11) := ⟨⟨11, by decide, by decide⟩⟩ 
instance : OfNat Month (nat_lit 12) := ⟨⟨12, by decide, by decide⟩⟩ 

theorem Month.eq_of_val_eq : ∀ {m m' : Month} (h : m.val = m'.val), m = m'
| ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

instance : LE Month where
  le := InvImage Nat.le Month.val 

instance : LT Month where
  lt := InvImage Nat.lt Month.val 

theorem Month.le_def {m m' : Month} : (m <= m') = (m.val <= m'.val) := rfl
theorem Month.lt_def {m m' : Month} : (m < m') = (m.val < m'.val) := rfl

instance : DecidableEq Month
| ⟨v, _, _⟩, ⟨v', _, _⟩ =>
  if h0 : v = v' 
  then isTrue $ Month.eq_of_val_eq h0
  else isFalse (fun h_eq => Month.noConfusion h_eq (fun v_eq => absurd v_eq h0))

instance (m m' : Month) : Decidable (m <= m') := inferInstanceAs (Decidable (m.val <= m'.val))
instance (m m' : Month) : Decidable (m < m') := inferInstanceAs (Decidable (m.val < m'.val))

def monthName : Month -> String
| ⟨1, _, _⟩ => "January"
| ⟨2, _, _⟩ => "February"
| ⟨3, _, _⟩ => "March"
| ⟨4, _, _⟩ => "April"
| ⟨5, _, _⟩ => "May"
| ⟨6, _, _⟩ => "June"
| ⟨7, _, _⟩ => "July"
| ⟨8, _, _⟩ => "August"
| ⟨9, _, _⟩ => "September"
| ⟨10, _, _⟩ => "October"
| ⟨11, _, _⟩ => "November"
| ⟨12, _, _⟩ => "December"

def Month.numDays (m : Month) (y : Year) : Nat := 
  if m.val = 2 then (if isLeapYear y.val then 29 else 28)
  else if m.val = 4 then 30
  else if m.val = 6 then 30
  else if m.val = 9 then 30
  else if m.val = 11 then 30
  else 31

@[reducible] def daysInMonth (year : Nat) : ∀ (month : Nat), Nat
| 2  => if isLeapYear year then 29 else 28
| 4  => 30
| 6  => 30
| 9  => 30
| 11 => 30
| _  => 31

theorem days_in_month_pos (year : Nat) (month : Nat) : 0 < daysInMonth year month := by
  simp only [daysInMonth]
  byCases hy : isLeapYear year
  case inl => split <;> simp [hy, if_true]
  case inr => split <;> simp [hy, if_false]

structure Date where
  val : Nat
deriving DecidableEq, Repr

theorem Date.eq_of_val_eq : ∀ {d1 d2 : Date} (h : d1 = d2), d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem Date.val_ne_of_ne : ∀ {d1 d2 : Date} (h : d1 ≠ d2), d1.val ≠ d2.val
| ⟨x⟩, ⟨y⟩, h => by intro hh; apply h; exact congrArg Date.mk hh

instance {n : Nat} : OfNat Date n where
  ofNat := ⟨n⟩

instance : HAdd Date Duration Date where
  hAdd da du := ⟨da.val + du.days⟩

theorem Date.hAdd_def (d : Date) (dur : Duration) : d + dur = ⟨d.val + dur.days⟩ := rfl

instance : HSub Date Duration Date where
  hSub da du := ⟨da.val - du.days⟩

theorem Date.sub_duration_def (d : Date) (dur : Duration) : d - dur = ⟨d.val - dur.days⟩ := rfl

instance : HSub Date Date Duration where
  hSub d d' := Duration.fromDays (d.val - d'.val)

def Date.absDiff (d₁ d₂ : Date) : Duration := max (d₁ - d₂) (d₂ - d₁)

instance : LT Date where
  lt := InvImage (Nat.lt) Date.val

instance : LE Date where
  le := InvImage (Nat.le) Date.val
  
theorem Date.le_def (d₁ d₂ : Date) : (d₁ <= d₂) = (d₁.val <= d₂.val) := rfl
theorem Date.lt_def (d₁ d₂ : Date) : (d₁ < d₂) = (d₁.val < d₂.val) := rfl

instance : Preorder Date where
  le_refl := by simp [Date.le_def]
  le_trans := by 
    simp [Date.le_def]
    intro a b c
    exact Nat.le_trans
  lt_iff_le_not_le := by
    intro a b
    simp [Date.lt_def, Date.le_def]
    exact Nat.le_of_lt

theorem Date.le_of_not_lt {a b : Date} : ¬a < b -> b <= a := by
  intro h1
  simp [Date.le_def]
  simp [Date.lt_def] at h1
  assumption

theorem Date.le_refl (d : Date) : d <= d := Nat.le_refl _

theorem Date.lt_irrefl (d : Date) : ¬d < d := by simp [Date.lt_def]

instance : DecidableEq Date
| ⟨v⟩, ⟨v'⟩ => 
  if h:v = v' 
  then isTrue <| congrArg Date.mk h
  else isFalse (fun hf => Date.noConfusion hf (fun hh => absurd hh h))

instance (a b : Date) : Decidable (a < b) := dite (a.val < b.val) isTrue (fun nlt => isFalse (fun hf => False.elim (nlt hf)))
instance (a b : Date) : Decidable (a <= b) := 
  dite (a.val <= b.val) isTrue (fun nle => isFalse (fun hf => False.elim (nle hf)))
instance : Ord Date where
  compare t t' := compareOfLessAndEq t t'

theorem Date.le_hAdd_right (d : Date) (dur : Duration) : d <= d + dur := by
  simp [Date.le_def, Date.hAdd_def, Nat.le_add_right]

theorem Date.le_hAdd_right' {d₁ d₂ : Date} (dur : Duration) (h : d₁ <= d₂) : d₁ <= d₂ + dur := by
  have h0 : d₂ <= d₂ + dur := Date.le_hAdd_right d₂ dur
  simp [Date.le_def, Date.hAdd_def, Nat.le_add_right]
  exact Nat.le_trans h h0

def Date.le_trans {a b c : Date} : a <= b -> b <= c -> a <= c := by
  simp [Date.le_def]
  exact Nat.le_trans

def Date.min_le_left (a b : Date) : min a b <= a := by
  simp [Date.le_def, min]
  byCases hx : a.val <= b.val
  case inl => simp [hx, Nat.le_refl]
  case inr => 
    simp [hx]
    have hy : b.val < a.val := Nat.lt_of_not_le hx
    exact Nat.le_of_lt hy

theorem Date.sub_duration_le (d : Date) (dur : Duration) : d - dur <= d := by
  rw [Date.le_def, Date.sub_duration_def]
  exact Nat.sub_le (d.val) (dur.days)

@[simp] theorem Date.sub_duration_succ (d : Date) (dur : Duration) : d - dur <= (d + Duration.oneDay) := Nat.le_step (Date.sub_duration_le d dur)

@[simp] theorem Date.le_add_right (d : Date) (dur : Duration) : d <= d + dur := Nat.le_add_right _ _
@[simp] theorem Date.le_add_right_of_le {a b: Date} {dur : Duration} : a <= b -> a <= b + dur := by
  intro h0
  have h1 : b <= b + dur := Date.le_add_right _ _
  exact Nat.le_trans h0 h1

structure DateRange where
  low : Date
  high : Date
  h : low <= high
deriving Repr
  
instance : Ord DateRange where
  compare r₁ r₂ :=   
  match Ord.compare r₁.low r₂.low with 
  | Ordering.lt => Ordering.lt
  | Ordering.gt => Ordering.gt
  | Ordering.eq => Ord.compare r₁.high r₂.high

theorem DateRange.eq_of_val_eq : ∀ {r₁ r₂ : DateRange} (hlow : r₁.low = r₂.low) (hhigh : r₁.high = r₂.high), r₁ = r₂
| ⟨l₁, h₁, _⟩, ⟨l₂, h₂, _⟩, hE => by intro hH; simp [hH, hE]

theorem DateRange.val_eq_of_eq {r₁ r₂ : DateRange} (he : r₁ = r₂) : r₁.low = r₂.low ∧ r₁.high = r₂.high :=
  DateRange.noConfusion he (fun h1 h2 => And.intro h1 h2)

instance : DecidableEq DateRange
| ⟨low₁, high₁, _⟩, ⟨low₂, high₂, _⟩ => 
  if hlow : low₁ = low₂ 
  then
    if hhigh : high₁ = high₂   
    then isTrue (DateRange.eq_of_val_eq hlow hhigh)
    else isFalse (fun hf => DateRange.noConfusion hf (fun _ hf' => absurd hf' hhigh))
  else isFalse (fun hf => DateRange.noConfusion hf (fun hf' _ => absurd hf' hlow))

@[reducible] def DateRange.mkInclusive (low high : Date) (h : low <= high) : DateRange :=
  DateRange.mk low (high + Duration.fromDays 1) (le_trans h (Date.le_add_right _ _))

theorem Date.add_le_add_left {a : Date} {b c : Duration} (h : b <= c) : a + b <= a + c := by
  simp [HAdd.hAdd, Add.add, Date.le_def]
  refine Nat.add_le_add_left ?h a.val
  simp [Duration.days, Duration.le_def]
  exact Nat.div_le_div_right h


def DateRange.tryMk (start finish : Date) : Option DateRange :=
  if h : start <= finish 
  then some (DateRange.mk start finish h)
  else none

def DateRange.extendHigh (r : DateRange) (dur : Duration) : DateRange := ⟨r.low, r.high + dur, Date.le_hAdd_right' dur r.h⟩ 

instance : Mem Date DateRange where
  mem d r := r.low <= d ∧ d < r.high

theorem DateRange.mem_def (range : DateRange) (date : Date) : (date ∈ range) = (range.low <= date ∧ date < range.high) := by rfl

instance : EmptyCollection DateRange where
  emptyCollection := DateRange.mk ⟨0⟩ ⟨0⟩ (Nat.le_refl _)

instance : Inter DateRange where
  inter r₁ r₂ :=
    let low := max r₁.low r₂.low
    let high := min r₂.high r₂.high
    if h0 : low <= high 
    then ⟨low, high, h0⟩ 
    else ∅ 

theorem DateRange.empty_collection_def : (∅ : DateRange) = DateRange.mk ⟨0⟩ ⟨0⟩ (Nat.le_refl _) := rfl

theorem emptyRange : ¬∃ elem, elem ∈ (∅ : DateRange)
| ⟨elem, h⟩ => by
  rw [DateRange.mem_def] at h
  simp at h
  rw [Date.le_def] at h
  rw [Date.lt_def] at h
  match Nat.eq_or_lt_of_le h.left with
  | Or.inl hl =>
    rw [hl, DateRange.empty_collection_def] at h
    simp at h
    exact False.elim (Nat.not_lt_zero (elem.val) h)
  | Or.inr hl =>
    have hh := Nat.not_le_of_gt h.right
    exact False.elim (hh (Nat.le_of_lt hl))

theorem foldr_helper {start finish : Date} (h : start < finish) : (start + Duration.oneDay) <= finish := by
  rw [Date.hAdd_def, Date.le_def]
  rw [Date.lt_def] at h
  simp only [Duration.days, Duration.fromDays, Nat.div_self]
  exact Nat.succ_le_of_lt h

theorem fold_decreasing0 {start : Date} : start.val < (start + Duration.oneDay).val := by
  simp only [Date.hAdd_def]
  have hh : 0 < (Duration.fromDays 1).val := by simp 
  refine Nat.lt_add_of_pos_right ?x
  simp

theorem fold_decreasing {start finish : Date} (h : start < finish) : (finish.val - (start + Duration.oneDay).val) < (finish.val - start.val) := by
  rw [Date.lt_def] at h
  refine Nat.sub_lt_sub_left ?h1 ?h2
  case h1 => exact h
  case h2 => exact fold_decreasing0

def DateRange.foldl {α} (f : α → Date → α) (initial : α) (r : DateRange) : α :=
  if h0 : r.low < r.high
  then foldl f (f initial r.low) (DateRange.mk (r.low + Duration.oneDay) r.high (foldr_helper h0))
  else initial
termination_by measure (fun ⟨_, _, _, r⟩ => (r.high.val - r.low.val))
decreasing_by exact fold_decreasing h0


def DateRange.duration (d : DateRange) : Duration := d.high - d.low

theorem Date.lt_succ_of_le {d₁ d₂ : Date} (h : d₁ <= d₂) : d₁ < d₂ + Duration.fromDays 1 := by
  simp [Date.le_def] at h
  simp [Date.lt_def, HAdd.hAdd, Add.add, Duration.fromDays, Duration.days]
  rw [Nat.div_self (Nat.zero_lt_succ _)]
  exact Nat.lt_succ_of_le h

@[simp] abbrev DateRange.startsOn (r : DateRange) (d : Date) : Prop := r.low = d
@[simp] abbrev DateRange.endsMidnightOf (r : DateRange) (d : Date) : Prop := r.high = (d + Duration.fromDays 1)

/- Does d begin before d' begins -/
@[reducible] def DateRange.startsBefore (d d' : DateRange) : Prop := d.low <= d'.low

/- Does d begin after d' begins -/
@[reducible] def DateRange.startsAfter (d d' : DateRange) : Prop := ¬(d.startsBefore d')

/- Does d finish before d' begins -/
@[reducible] def DateRange.finishesBefore (d d' : DateRange) : Prop := d.high <= d'.high

/- Does d finish after d' begins -/
@[reducible] def DateRange.finishesAfter (d d' : DateRange) : Prop := ¬(d.finishesBefore d')

/- Do d and d' overlap (do they share any points in common; (m, 3) overlaps (3, n)) -/
@[reducible] def DateRange.overlapping (d d' : DateRange) : Prop := (d'.low <= d.high) ∨ (d.low <= d'.high)
@[reducible] def DateRange.disjoint (d d' : DateRange) : Prop := ¬(d.overlapping d')
/- Consecutive with open end-points -/
@[reducible] def DateRange.consecutiveOpen (d d' : DateRange) : Prop := (d.high + (Duration.fromDays 1)) = d'.low
/- Consecutive with open end-points -/
@[reducible] def DateRange.consecutiveClosed (d d' : DateRange) : Prop := d.high = d'.low
@[reducible] def DateRange.compareStart (d d' : DateRange) : Ordering := Ord.compare d.low d'.low

instance (d : Date) (r : DateRange) : Decidable (d ∈ r) := 
  inferInstanceAs (Decidable $ r.low <= d ∧ d < r.high)

/- These are all guaranteed to begin on leap years. -/
def dty400' (ds : Nat) : (Nat × Nat) :=
  let num400Groups := (ds / daysIn400Group) 
  let years := 400 * num400Groups
  (years, ds - (num400Groups * daysIn400Group))

def dty100' (ds : Nat) : (Nat × Nat) :=
  if ds < daysIn100GroupLeap 
  then (0, ds)
  else 
  let nonLeap100Groups := ((ds - daysIn100GroupLeap) / daysIn100GroupNoLeap)
  let years := 100 * (1 + nonLeap100Groups)
  (years, ds - (daysIn100GroupLeap + (nonLeap100Groups * daysIn100GroupNoLeap)))

def dty4' (ds : Nat) (yearSoFar: Nat) : (Nat × Nat) :=
  let firstYearDays := daysIn4GroupNoLeap + if isLeapYear yearSoFar then 1 else 0
  if ds < firstYearDays then (0, ds)
  else 
  let rest4chunks := ((ds - firstYearDays) / daysIn4GroupLeap)
  let years := 4 * (rest4chunks + 1)
  (years, ds - ((rest4chunks * daysIn4GroupLeap) + firstYearDays))

def dtylast' (ds : Nat) (yearSoFar : Nat) : (Nat × Nat) :=
  let first := numDaysInGregorianYear yearSoFar
  if h0 : ds < first then (0, ds)
  else if h1 : ds < first + 365 then (1, ds - first)
  else if h2 : ds < first + (365 * 2) then (2, ds - (first + 365))
  else if h3: ds < first + (365 * 3) then (3, ds - (first + 365 * 2))
  else panic! "dtylast'"

def dty' (ds : Nat) : (Nat × Nat) :=
  let (ys400, rem400) := dty400' ds
  let (ys100, rem100) := dty100' rem400
  let (ys4, rem4) := dty4' rem100 (ys400 + ys100)
  let (yslast, remlast) := (dtylast' rem4 (ys400 + ys100 + ys4))
  (ys400 + ys100 + ys4 + yslast, remlast)

/- These will all begin on leap years. -/
def ytd400' (ys : Nat) : (Nat × Nat) :=
  let numGroups := ys / 400
  let days := numGroups * daysIn400Group
  (days, ys % 400)
  --(days, ys - (400 * numGroups))

/- The first one will always begin on a leap year, while the subsequent
   100 groups will not begin with leap years. -/
def ytd100' (ys : Nat) : (Nat × Nat) :=
  if ys < 100 
  then (0, ys)  
  else 
  let num100Groups := ys / 100
  let days := (daysIn100GroupLeap + (num100Groups.pred * daysIn100GroupNoLeap))
  (days, ys % 100)
  --(days, ys - (100 * num100Groups))

/- The first 4 group may or may not be a leap year; all other 4 groups begin
   on leap years. -/
def ytd4' (ys : Nat) (yearSoFar : Nat) : (Nat × Nat) :=
  if ys < 4 
  then (0, ys)
  else 
  let firstGroupDays := daysIn4Group yearSoFar
  let numGroups := ys / 4
  let days := (firstGroupDays + (numGroups.pred * daysIn4GroupLeap))
  (days, ys % 4)
  --(days, ys - (4 * numGroups))

theorem ytd4'_lt : ∀ (ys ysf), (ytd4' ys ysf).2 < 4 := by
  intro ys ysf
  simp [ytd4']
  split
  next h => exact h
  next => exact Nat.mod_lt _ (by decide)

/- The last group of either 0, 1, 2, or 3 years. As with the other way,
   this may or may not begin on initial leap year (year 3 vs. year 303). -/
def ytdlast' (ys : Nat) (yearSoFar : Nat) (h : ys < 4) : Nat :=
  let first := 365 + if isLeapYear yearSoFar then 1 else 0
  match hys:ys with
  | 0 => 0
  | 1 => first
  | 2 => first + 365
  | 3 => first + (365 * 2)
  | n+4 => by rw [hys] at h; exact absurd h lt_plus

/- From the current calendar year, returns the number of days that are 
   known to have elapsed, NOT COUNTING THE DAYS IN THE CURRENT/ONGOING YEAR.
   For example, ytd' 0 = 0, ytd' 1 = 366, ytd' 2 = 731.
   This behavior is important for calculating the serial day from a calendar date. -/
def ytd' (ys : Nat) : Nat :=
  let (ds400, rem400) := ytd400' ys
  let (ds100, rem100) := ytd100' rem400
  let days_x_rem4 := ytd4' rem100 (ys - rem100)
  ds400 + ds100 + days_x_rem4.fst + (ytdlast' days_x_rem4.snd (ys - days_x_rem4.snd) (ytd4'_lt _ _))
def ytdTo4 (ys : Nat) : Nat :=
  let (ds400, rem400) := ytd400' ys
  let (ds100, rem100) := ytd100' rem400
  let (ds4, rem4) := ytd4' rem100 (ys - rem100)
  (ds400 + ds100 + ds4)

def dty2' (ds : Nat) : Nat :=
  let (ys400, rem400) := dty400' ds
  let (ys100, rem100) := dty100' rem400
  let (ys4, rem4) := dty4' rem100 (ys400 + ys100)
  let (yslast, remlast) := (dtylast' rem4 (ys400 + ys100 + ys4))
  ys400 + ys100 + ys4 + yslast

/- Get the ordinal date (yyyy, 1-based ddd) by adding the extra day needed to account
   for the 0-based nature of gregorian days as calculated in dty'. -/
def ordinalDateFromGregorianDay (ds : Nat) : (Nat × Nat) := 
  match dty' ds with
  | (yr, plusDays) => (yr, plusDays + 1)

abbrev lastDayJanuary             : Nat := 31
abbrev lastDayFebruary  (y : Nat) : Nat := 59  + (ite (isLeapYear y) 1 0)  
abbrev lastDayMarch     (y : Nat) : Nat := 90  + (ite (isLeapYear y) 1 0)  
abbrev lastDayApril     (y : Nat) : Nat := 120 + (ite (isLeapYear y) 1 0)  
abbrev lastDayMay       (y : Nat) : Nat := 151 + (ite (isLeapYear y) 1 0)  
abbrev lastDayJune      (y : Nat) : Nat := 181 + (ite (isLeapYear y) 1 0)  
abbrev lastDayJuly      (y : Nat) : Nat := 212 + (ite (isLeapYear y) 1 0)  
abbrev lastDayAugust    (y : Nat) : Nat := 243 + (ite (isLeapYear y) 1 0)  
abbrev lastDaySeptember (y : Nat) : Nat := 273 + (ite (isLeapYear y) 1 0)  
abbrev lastDayOctober   (y : Nat) : Nat := 304 + (ite (isLeapYear y) 1 0)  
abbrev lastDayNovember  (y : Nat) : Nat := 334 + (ite (isLeapYear y) 1 0)  
abbrev lastDayDecember  (y : Nat) : Nat := 365 + (ite (isLeapYear y) 1 0)  

/- Predicates used to show that the conversion between (days <= 365) and (Month, day) pairs
   is a bijection. There's no clean functional way of doing this recursively, because
   months have irregular numbers of days and depend on leap years. Lean can't handle a function
   that just maps with 365 cases, so instead we chunk them into 12 groups by month -/
@[reducible] def isJanuaryDay   (d : Nat) : Prop := d <= 31
@[reducible] def isFebruaryDay  (y : Nat) (d : Nat) : Prop := lastDayJanuary < d ∧ d <= lastDayFebruary y
@[reducible] def isMarchDay     (y : Nat) (d : Nat) : Prop := lastDayFebruary y < d ∧ d <= lastDayMarch y
@[reducible] def isAprilDay     (y : Nat) (d : Nat) : Prop := lastDayMarch y < d ∧ d <= lastDayApril y
@[reducible] def isMayDay       (y : Nat) (d : Nat) : Prop := lastDayApril y < d ∧ d <= lastDayMay y
@[reducible] def isJuneDay      (y : Nat) (d : Nat) : Prop := lastDayMay y < d ∧ d <= lastDayJune y
@[reducible] def isJulyDay      (y : Nat) (d : Nat) : Prop := lastDayJune y < d ∧ d <= lastDayJuly y
@[reducible] def isAugustDay    (y : Nat) (d : Nat) : Prop := lastDayJuly y < d ∧ d <= lastDayAugust y
@[reducible] def isSeptemberDay (y : Nat) (d : Nat) : Prop := lastDayAugust y < d ∧ d <= lastDaySeptember y
@[reducible] def isOctoberDay   (y : Nat) (d : Nat) : Prop := lastDaySeptember y < d ∧ d <= lastDayOctober y
@[reducible] def isNovemberDay  (y : Nat) (d : Nat) : Prop := lastDayOctober y < d ∧ d <= lastDayNovember y
@[reducible] def isDecemberDay  (y : Nat) (d : Nat) : Prop := lastDayNovember y < d ∧ d <= lastDayDecember y

/- Convert an ordinal day to its (month, day) pair. -/
-- (Nat × Nat) // pr.2 <= numDaysInMonth pr.1
@[reducible] def ordinalDayToMd (y : Nat) (d : Nat) : (Nat × Nat) :=
  if isJanuaryDay d then          (1, d)
  else if isFebruaryDay y d  then (2, d - lastDayJanuary)
  else if isMarchDay y d     then (3, d - lastDayFebruary y)
  else if isAprilDay y d     then (4, d - lastDayMarch y)
  else if isMayDay y d       then (5, d - lastDayApril y)
  else if isJuneDay y d      then (6, d - lastDayMay y)
  else if isJulyDay y d      then (7, d - lastDayJune y)
  else if isAugustDay y d    then (8, d - lastDayJuly y)
  else if isSeptemberDay y d then (9, d - lastDayAugust y)
  else if isOctoberDay y d   then (10, d - lastDaySeptember y)
  else if isNovemberDay y d  then (11, d - lastDayOctober y)
  else                            (12, d - lastDayNovember y)

@[reducible] def ordinalDateToYmd (y : Nat) (d : Nat) : (Nat × Nat × Nat) :=
  if isJanuaryDay d then          (y, 1, d)
  else if isFebruaryDay y d  then (y, 2, d - lastDayJanuary)
  else if isMarchDay y d     then (y, 3, d - lastDayFebruary y)
  else if isAprilDay y d     then (y, 4, d - lastDayMarch y)
  else if isMayDay y d       then (y, 5, d - lastDayApril y)
  else if isJuneDay y d      then (y, 6, d - lastDayMay y)
  else if isJulyDay y d      then (y, 7, d - lastDayJune y)
  else if isAugustDay y d    then (y, 8, d - lastDayJuly y)
  else if isSeptemberDay y d then (y, 9, d - lastDayAugust y)
  else if isOctoberDay y d   then (y, 10, d - lastDaySeptember y)
  else if isNovemberDay y d  then (y, 11, d - lastDayOctober y)
  else                            (y, 12, d - lastDayNovember y)

/- Convert a (month, day) pair to its ordinal date (y, (1-366)) -/
def ordinalDateFromYmd (y : Nat) (m : Nat) (d : Nat) (h : 0 < m ∧ m < 13) : (Nat × Nat) :=
  match hh:m with
  | 0 => False.elim $ Nat.not_lt_zero 0 (hh ▸ h.left)
  | 1  => (y, d)
  | 2  => (y, d + lastDayJanuary)
  | 3  => (y, d + lastDayFebruary y)
  | 4  => (y, d + lastDayMarch y)
  | 5  => (y, d + lastDayApril y)
  | 6  => (y, d + lastDayMay y)
  | 7  => (y, d + lastDayJune y)
  | 8  => (y, d + lastDayJuly y)
  | 9  => (y, d + lastDayAugust y)
  | 10 => (y, d + lastDaySeptember y)
  | 11 => (y, d + lastDayOctober y)
  | 12 => (y, d + lastDayNovember y)
  | _+13 => by rw [hh] at h; exfalso; exact lt_plus (h.right)

/- This is in mathlib3, and I'm lazy. -/
theorem sub_le_right_of_le_add {n m k : Nat} : n ≤ m + k → n - k ≤ m := sorry
    
/-
A big ugly cases proof to show that the function for converting
an ordinay Y/D pair to a (M/D) pair produces a result in the correct
range.

The statement is that for the (M/D) pair, that the month is between
1 and 12, and the day is within the bounds of the given month for
that year, depending on whether or not it's a leap year. 
-/
theorem ordinalDayToMd_in_bounds (y : Nat) (d : Nat) (hd : d <= numDaysInGregorianYear y) : (ordinalDayToMd y d).1 < 13 ∧ (ordinalDayToMd y d).2 <= (daysInMonth y (ordinalDayToMd y d).1) :=
  if h_jan : isJanuaryDay d
  then by simp [ordinalDayToMd, if_pos h_jan, daysInMonth]; assumption
  else if h_feb : isFebruaryDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, if_pos h_feb, hl, h_jan]
     simp [isFebruaryDay, lastDayJanuary, lastDayFebruary, hl] at h_feb
     exact sub_le_right_of_le_add h_feb.right)
  else if h_mar : isMarchDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDayFebruary, hl, h_jan, h_feb, if_pos h_mar]
     simp [isMarchDay, lastDayFebruary, lastDayMarch, hl] at h_mar
     exact sub_le_right_of_le_add h_mar.right)
  else if h_apr : isAprilDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDayMarch, hl, h_jan, h_feb, h_mar, if_pos h_apr]
     simp [isAprilDay, lastDayMarch, lastDayApril, hl] at h_apr
     exact sub_le_right_of_le_add h_apr.right)
  else if h_may : isMayDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDayApril, hl, h_jan, h_feb, h_mar, h_apr, if_pos h_may]
     simp [isMayDay, lastDayApril, lastDayMay, hl] at h_may
     exact sub_le_right_of_le_add h_may.right)
  else if h_jun : isJuneDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDayMay, hl, h_jan, h_feb, h_mar, h_apr, h_may, if_pos h_jun]
     simp [isJuneDay, lastDayMay, lastDayJune, hl] at h_jun
     exact sub_le_right_of_le_add h_jun.right)
  else if h_jul : isJulyDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDayJune, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, if_pos h_jul]
     simp [isJulyDay, lastDayJune, lastDayJuly, hl] at h_jul
     exact sub_le_right_of_le_add h_jul.right)
  else if h_aug : isAugustDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDayJuly, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, if_pos h_aug]
     simp [isAugustDay, lastDayJuly, lastDayAugust, hl] at h_aug
     exact sub_le_right_of_le_add h_aug.right)
  else if h_sep : isSeptemberDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDayAugust, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, h_aug, if_pos h_sep]
     simp [isSeptemberDay, lastDayAugust, lastDaySeptember, hl] at h_sep
     exact sub_le_right_of_le_add h_sep.right)
  else if h_oct : isOctoberDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDaySeptember, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, h_aug, h_sep, if_pos h_oct]
     simp [isOctoberDay, lastDaySeptember, lastDayOctober, hl] at h_oct
     exact sub_le_right_of_le_add h_oct.right)
  else if h_nov : isNovemberDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDayOctober, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, h_aug, h_sep, h_oct, if_pos h_nov]
     simp [isNovemberDay, lastDayOctober, lastDayNovember, hl] at h_nov
     exact sub_le_right_of_le_add h_nov.right)
  else by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDayToMd, daysInMonth, lastDayNovember, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, h_aug, h_sep, h_oct, h_nov]
     simp [numDaysInGregorianYear, hl] at hd
     exact sub_le_right_of_le_add hd)

theorem ordinalDateToYmd_in_bounds (y : Nat) (d : Nat) (hd : d <= numDaysInGregorianYear y) : (ordinalDateToYmd y d).2.1 < 13 ∧ (ordinalDateToYmd y d).2.2 <= (daysInMonth y (ordinalDateToYmd y d).2.1) ∧ (y = (ordinalDateToYmd y d).1) :=
  if h_jan : isJanuaryDay d
  then by simp [ordinalDateToYmd, if_pos h_jan, daysInMonth]; assumption
  else if h_feb : isFebruaryDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, if_pos h_feb, hl, h_jan]
     simp [isFebruaryDay, lastDayJanuary, lastDayFebruary, hl] at h_feb
     exact sub_le_right_of_le_add h_feb.right)
  else if h_mar : isMarchDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDayFebruary, hl, h_jan, h_feb, if_pos h_mar]
     simp [isMarchDay, lastDayFebruary, lastDayMarch, hl] at h_mar
     exact sub_le_right_of_le_add h_mar.right)
  else if h_apr : isAprilDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDayMarch, hl, h_jan, h_feb, h_mar, if_pos h_apr]
     simp [isAprilDay, lastDayMarch, lastDayApril, hl] at h_apr
     exact sub_le_right_of_le_add h_apr.right)
  else if h_may : isMayDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDayApril, hl, h_jan, h_feb, h_mar, h_apr, if_pos h_may]
     simp [isMayDay, lastDayApril, lastDayMay, hl] at h_may
     exact sub_le_right_of_le_add h_may.right)
  else if h_jun : isJuneDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDayMay, hl, h_jan, h_feb, h_mar, h_apr, h_may, if_pos h_jun]
     simp [isJuneDay, lastDayMay, lastDayJune, hl] at h_jun
     exact sub_le_right_of_le_add h_jun.right)
  else if h_jul : isJulyDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDayJune, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, if_pos h_jul]
     simp [isJulyDay, lastDayJune, lastDayJuly, hl] at h_jul
     exact sub_le_right_of_le_add h_jul.right)
  else if h_aug : isAugustDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDayJuly, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, if_pos h_aug]
     simp [isAugustDay, lastDayJuly, lastDayAugust, hl] at h_aug
     exact sub_le_right_of_le_add h_aug.right)
  else if h_sep : isSeptemberDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDayAugust, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, h_aug, if_pos h_sep]
     simp [isSeptemberDay, lastDayAugust, lastDaySeptember, hl] at h_sep
     exact sub_le_right_of_le_add h_sep.right)
  else if h_oct : isOctoberDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDaySeptember, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, h_aug, h_sep, if_pos h_oct]
     simp [isOctoberDay, lastDaySeptember, lastDayOctober, hl] at h_oct
     exact sub_le_right_of_le_add h_oct.right)
  else if h_nov : isNovemberDay y d
  then by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDayOctober, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, h_aug, h_sep, h_oct, if_pos h_nov]
     simp [isNovemberDay, lastDayOctober, lastDayNovember, hl] at h_nov
     exact sub_le_right_of_le_add h_nov.right)
  else by
    byCases hl : isLeapYear y <;>
    (simp [ordinalDateToYmd, daysInMonth, lastDayNovember, hl, h_jan, h_feb, h_mar, h_apr, h_may, h_jun, h_jul, h_aug, h_sep, h_oct, h_nov]
     simp [numDaysInGregorianYear, hl] at hd
     exact sub_le_right_of_le_add hd)


--def ymdFromGregorianDay (d : Nat) : (Nat × Nat × Nat) :=
--  let (year, day) := ordinalDateFromGregorianDay d
--  let (month, day) := ordinalDayToMd year day
--  (year, month, day)

def ymdFromGregorianDay (d : Nat) : (Nat × Nat × Nat) :=
  let (year, day) := ordinalDateFromGregorianDay d
  ordinalDateToYmd year day

def gregorianDayFromYmd (y : Nat) (m : Nat) (d : Nat) (h : 0 < m ∧ m < 13) : Nat :=
  (ytd' y) + (ordinalDateFromYmd y m d h).snd.pred

structure ClockTime where
  val : Nat
  isLt : val < oneDayNanos

theorem ClockTime.eq_of_val_eq : ∀ {t t' : ClockTime} (h : t.val = t'.val), t = t'
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

def ClockTime.nanos (d : ClockTime) : Nat := d.val % oneSecondNanos
def ClockTime.seconds (d : ClockTime) : Nat := (d.val % oneMinuteNanos) / oneSecondNanos
def ClockTime.minutes (d : ClockTime) : Nat := (d.val % oneHourNanos) / oneMinuteNanos
def ClockTime.hours (d : ClockTime) : Nat := d.val / oneHourNanos

def ClockTime.fromHmsn (h : Nat) (m : Nat) (s : Nat) (n : Nat) : ClockTime := 
  ClockTime.mk
    (((h * oneHourNanos) + (m * oneMinuteNanos) + (s * oneSecondNanos) + n) % oneDayNanos)
    (Nat.mod_lt _ (by decide))

instance : HAdd ClockTime Duration ClockTime where
  hAdd t d := ClockTime.mk ((t.val + d.val) % oneDayNanos) (Nat.mod_lt _ (by decide))

instance : HAdd Duration ClockTime ClockTime where
  hAdd t d := d + t

instance : LT ClockTime where
  lt := InvImage Nat.lt ClockTime.val

instance : LE ClockTime where
  le := InvImage Nat.le ClockTime.val

instance : DecidableEq ClockTime
| ⟨v, _⟩, ⟨v', _⟩ =>
  if h:v = v' 
  then isTrue <| ClockTime.eq_of_val_eq h
  else isFalse (fun hf => ClockTime.noConfusion hf (fun hh => absurd hh h))

instance (a b : ClockTime) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : ClockTime) : Decidable (a <= b) := inferInstanceAs (Decidable (a.val <= b.val))

instance : Ord ClockTime where
  compare t t' := compareOfLessAndEq t t'

instance : ToString ClockTime where
  toString t := 
    let h := String.leftpad 2 '0' (ToString.toString t.hours)
    let m := String.leftpad 2 '0' (ToString.toString t.minutes)
    let s := String.leftpad 2 '0' (ToString.toString t.seconds)
    let n := String.leftpad 9 '0' (ToString.toString t.nanos)
  s!"H{h}M{m}S{s}.{n}"

structure DateTime where
  date : Date
  time : ClockTime
deriving DecidableEq, Ord

def Date.fromYmd 
  (y : Nat) 
  (m : Nat) 
  (d : Nat) 
  (hm : 0 < m ∧ m < 13 := by decide) 
  (hd : d <= daysInMonth y m := by decide) : Date := 
  Date.mk (gregorianDayFromYmd y m d hm)

structure Ymd where
  y : Year
  m : Month
  d : Nat
  dayLe : d <= daysInMonth y.val m.val

instance : Inhabited Ymd where
  default := ⟨0, ⟨1, by decide, by decide⟩, 1, by decide⟩

def Ymd.new 
  (y : Nat) 
  (m : Nat) 
  (d : Nat) 
  (hm : 0 < m ∧ m < 13 := by decide) 
  (hd : d <= daysInMonth y m := by decide) : Ymd := 
  Ymd.mk ⟨y⟩ ⟨m, hm.left, hm.right⟩ d hd

instance : HAdd Ymd Duration Ymd where
  hAdd ymd dur := 
    let gregDay := gregorianDayFromYmd ymd.y.val ymd.m.val ymd.d (And.intro ymd.m.isGt ymd.m.isLt)
    let gregDay' := gregDay + dur.days
    let (y, m, d) := ymdFromGregorianDay gregDay'
    if h0 : ((0 < m ∧ m < 13) ∧ d <= daysInMonth y m)
    then ⟨OfNat.ofNat y, ⟨m, h0.left.left, h0.left.right⟩, d, h0.right⟩ 
    else panic! "hAdd failed"
    
instance : ToString Ymd where
  toString d := 
    let y := String.leftpad 4 '0' (ToString.toString d.y)
    let m := String.leftpad 2 '0' (ToString.toString d.m)
    let d := String.leftpad 2 '0' (ToString.toString d.d)
    s!"{y}/{m}/{d}"

structure YmdTime where
  date : Ymd
  time : ClockTime
--deriving DecidableEq, Ord

instance : ToString YmdTime where
  toString dt := s!"{dt.date},{dt.time}"

def Ymd.tryFromDate (d : Date) : Option Ymd :=
  let (y, m, d) := ymdFromGregorianDay d.val
  if h0 : (d <= daysInMonth y m) ∧ (0 < m ∧ m < 13)
  then some $ Ymd.mk ⟨y⟩ ⟨m, h0.right.left, h0.right.right⟩ d h0.left
  else none

set_option autoBoundImplicitLocal false

abbrev DateList := List Date

def DateList.tryToYmds (l : DateList) : List (Option Ymd) := l.map (Ymd.tryFromDate)

instance : Inhabited Duration where
  default := Duration.mk 0

constant DateList.cumulativeDuration (l : DateList) : Duration

instance : Sdiff DateList where
  sdiff l₁ l₂ := l₁.filter (fun x => ¬x ∈ l₂)

def DateList.sdiff_def (l₁ l₂ : DateList) : (l₁ \ l₂) = (l₁.filter (fun x => ¬x ∈ l₂)) := rfl

instance : Union DateList := ⟨List.union⟩

def DateList.union_def (l₁ l₂ : DateList) : (l₁ ∪ l₂) = l₁.union l₂ := rfl

instance : Inter DateList := ⟨List.inter⟩ 

def DateList.inter_def (l₁ l₂ : DateList) : (l₁ ∩ l₂) = l₁.inter l₂ := rfl

theorem mem_diff (l₁ l₂ : DateList) : ∀ elem ∈ l₂, ¬elem ∈ l₁ \ l₂ := by
  simp [DateList.sdiff_def]
  intro elem h h'
  have ⟨_, nmem⟩ := (List.mem_filter l₁ (fun (x : Date) => ¬x ∈ l₂) elem).mp h'
  exact (of_decide_eq_true nmem) h

theorem mem_diff' (l₁ l₂ : DateList) : ∀ d ∈ l₁, d ∈ l₁ \ l₂ <-> (d ∈ l₁ ∧ ¬d ∈ l₂) := by
  intro d h
  refine Iff.intro ?mp ?mpr
  case mp =>
    simp [DateList.sdiff_def]
    intro x
    have y := (List.mem_filter l₁ (fun (x : Date) => ¬x ∈ l₂) d).mp
    specialize y x
    refine And.intro h ?r
    exact (of_decide_eq_true y.right)
  case mpr =>
    intro h'
    simp [DateList.sdiff_def]
    have x := (List.mem_filter l₁ (fun (x : Date) => ¬x ∈ l₂) d).mpr
    apply x
    refine And.intro h ?x
    exact decide_eq_true h'.right

/-- Closed/Inclusive of both endpoints -/
@[reducible] def DateList.between (l : DateList) (low high : Date) : DateList :=
  l.filter (fun d => low <= d ∧ d <= high)

theorem DateList.between_spec (low high : Date) (ds : DateList) : ∀ d ∈ (between ds low high), low <= d ∧ d <= high := by
  simp [between]
  intro d h0
  have ⟨a, b⟩ := List.mem_filter ds (fun d' => low <= d' ∧ d' <= high) d
  specialize a h0
  exact (of_decide_eq_true a.right)

/-- Closed -/
@[reducible] def DateList.onBefore (l : DateList) (high : Date) : DateList :=
  l.filter (fun d => d <= high)

theorem DateList.before_spec (high : Date) (ds : DateList) : ∀ d ∈ (onBefore ds high), d <= high := by
  simp [onBefore]
  intro d h0
  have ⟨a, b⟩ := List.mem_filter ds (fun d' => d' <= high) d
  specialize a h0
  exact (of_decide_eq_true a.right)

/-- Closed -/
@[reducible] def DateList.onAfter (l : DateList) (low : Date) : DateList :=
  l.filter (fun d => low <= d)

theorem DateList.after_spec (low : Date) (ds : DateList) : ∀ d ∈ (onAfter ds low), d >= low := by
  simp [onAfter]
  intro d h0
  have ⟨a, b⟩ := List.mem_filter ds (fun d' => low <= d') d
  specialize a h0
  exact (of_decide_eq_true a.right)

@[reducible] def DateList.max : DateList -> Option Date
| [] => none
| h :: t => some $ t.foldl (fun sink next => _root_.max sink next) h 

@[reducible] def DateList.min : DateList -> Option Date
| [] => none
| h :: t => some $ t.foldl (fun sink next => _root_.min sink next) h 

theorem f_decreasing {start finish : Date} (h : start < finish) : (finish.val - (start + Duration.oneDay).val) < (finish.val - start.val) := by
  rw [Date.lt_def] at h
  refine Nat.sub_lt_sub_left ?h1 ?h2
  case h1 => exact h
  case h2 => exact fold_decreasing0

def f : ∀ (ds : DateRange), DateList
| ⟨lo, hi, h⟩ => 
  if h0 : lo < hi
  then lo :: f ⟨lo + (Duration.fromDays 1), hi, h0⟩
  else []
termination_by measure (fun r => (r.high.val - r.low.val))
decreasing_by exact f_decreasing h0

instance : Coe DateRange DateList where
  coe := f

macro yl:num "/" ml:num "/" dl:num "...=" yh:num "/" mh:num "/" dh:num : term =>
  `(DateRange.mk (Date.fromYmd $yl $ml $dl) (Date.fromYmd $yh $mh ($dh + 1)) (by simp [Date.le_refl, Date.le_add_right, Date.le_of_not_lt, Date.le_def]))


macro yl:num "/" ml:num "/" dl:num "...=" yh:num "/" mh:num "/" dh:num h:term : term =>
  `(DateRange.mk (Date.fromYmd $yl $ml $dl) (Date.fromYmd $yh $mh ($dh + 1)) $h)

macro low:term "...=" high:term "," h:term : term => `((DateRange.mk $low $high $h).extendHigh (Duration.oneDay))
macro low:term "...=" high:term : term => `((DateRange.mk $low $high (by decide)).extendHigh (Duration.oneDay))

macro yl:num "/" ml:num "/" dl:num "..." yh:num "/" mh:num "/" dh:num : term => `(DateRange.mk (Date.fromYmd $yl $ml $dl) (Date.fromYmd $yh $mh $dh) (by decide))
macro yl:num "/" ml:num "/" dl:num "..." yh:num "/" mh:num "/" dh:num h:term : term => `(DateRange.mk (Date.fromYmd $yl $ml $dl) (Date.fromYmd $yh $mh $dh) $h)
macro low:term "..." high:term "," h:term : term => `(DateRange.mk $low $high $h)
macro low:term "..." high:term : term => `(DateRange.mk $low $high (by decide))

def Date.reachingBack (d : Date) (dur : Duration) : DateRange := 
  let start := d - dur
  DateRange.mk start (d + Duration.oneDay) (Date.sub_duration_succ _ _) 

def Date.reachingForward (start : Date) (dur : Duration) : DateRange :=
  (DateRange.mk start start (Date.le_refl _)).extendHigh Duration.oneDay

theorem Date.min_le {a b c : Date} (h : a <= c) (h2 : b <= c) : min a b <= c := by
  simp [min]
  byCases hc : a <= b
  case inl => simp [hc]; exact h
  case inr => simp [hc]; exact h2

theorem Date.le_min {a b c : Date} (h : a <= b) (h2 : a <= c) : a <= min b c := by
  simp [min]
  byCases hc : b <= c
  case inl => simp [hc] exact h
  case inr => simp [hc]; exact h2

instance : Preorder Duration where
  le_refl := by simp [Duration.le_def]
  le_trans := by 
    simp [Duration.le_def]
    intro a b c
    exact Nat.le_trans
  lt_iff_le_not_le := by
    intro a b
    simp only [Duration.lt_def, Duration.le_def]
    exact Nat.lt_iff_le_not_le

instance : LinearOrder Duration where
  le_antisymm := by
    simp [Duration.le_def]
    intro a b h1 h2
    apply Duration.eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [Duration.le_def, le_total]
  decidable_le := Time.instDecidableLe

def dur (l : DateList) : Duration := 
  Duration.fromDays (l.length)

instance : ToString Date where
  toString d :=
    let (y, m, d) := ymdFromGregorianDay d.val
    s!"{y}/{m}/{d}"

instance : ToString DateRange where
  toString d := s!"From 00:00:00 of {d.low} .. to 00:00:00 of {d.high}"

instance : ToString DateTime where
  toString dt := s!"{dt.date},{dt.time}"


