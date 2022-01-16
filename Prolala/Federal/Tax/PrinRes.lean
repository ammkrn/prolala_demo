import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Init.Data.Int.Order
import Mathlib.Tactic.Basic
import Mathlib.Init.SetNotation
import Mathlib.Init.Set
import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Federal.Tax.Util
import Prolala.Util

open Time Property PropertyTxn

inductive Kind
| single 
| widowed
| joint 
deriving DecidableEq, Repr

structure Info where
  /-- Single, joint, or widowed -/
  kind : Kind
  /-- The duration of the "suspension period" for qualified duty claimed by the taxpayer. -/
  suspensionPeriod : Duration
  h1 : suspensionPeriod <= Duration.fromYears 10
  /-- The actual date of sale -/
  saleDate : Date
  /-- The amount realized from the sale. -/
  amtRealized : NonnegMoney
  /-- The taxpayer's adjusted basis in the property -/
  adjustedBasis : NonnegMoney
  /-- Depreciation taken after May 6, 1997. -/
  applicableDepreciationTaken : NonnegMoney
  /-- When did the taxpayer's ownership of the property begin -/
  ownershipStart : Date
  /-- 
  The periods of time (less minor absences) during which this was used as the taxpayer's
  principal residence
  -/
  principalResidencePeriods : DateList
  /-- 
  The amount of time that's elapsed since the last use of S121 by the taxpayer,
  but only if that duration is less than 2 years. If it's GE 2 years,
  it's irrelevant, but if it's less, we need the actual duration in order to calculate
  the partial ratio. 
  -/
  timeSinceLast121 : Option { d : Duration // d < Duration.fromDays 730 }
  /-- Dates the taxpayer is claiming as extended duty time. -/
  extendedDuty : DateList
  /-- 
  "periods of temporary absence (not to exceed an aggregate period of 2 years) due to 
  change of employment, health conditions, or such other unforeseen circumstances as 
  may be specified by the Secretary."
  -/
  emergencyTime : DateList
  /--
  True if this sale of exchange is by reason of a change in place of employment, health, 
  or, to the extent provided in regulations, unforeseen circumstances.
  -/
  exigentSale : Bool
  /-- `some d` if this was acquired via like-kind exchange on date `d`. -/
  acquiredViaLkeDate : Option ({ lkeDate : Date // lkeDate + Duration.fromYears 5 <= saleDate })
  h0 : ownershipStart <= saleDate
  h2 : extendedDuty.cumulativeDuration <= (Duration.fromYears 10)
  h3 : emergencyTime.cumulativeDuration <= (Duration.fromYears 2)
  h4 : 0 < (ownershipStart ...= saleDate, h0).duration.val 

instance : Property Info where
  adjustedBasis info := info.adjustedBasis

instance : PropertyTxn Info where
  amtRealized info := info.amtRealized

section InfoStuff

variable (info : Info) 

/-- The maximum possible nonrecognition given a taxpayer's filing status.
    We refer to this as the base nonrecognition, because the operating mechanism of
    S121 is to start with this, and reduce it in the presence of certain conditions. -/
def Info.baseNonrecognition : Money :=
  match info.kind with
  | Kind.single => 250000
  | owise => 500000

/-- If the taxpayer was not involved in any qualified extended duty, then
    the `periodEndDate` is the sale date. If they were involved in qualified
    extended duty, the taxpayer may be able to push the `periodEndDate` back up to
    ten years, effectively moving the `fiveYearPeriod` window backward relative to
    the sale date. The IRS calls this the `suspension period`. -/
def Info.periodEndDate : Date := info.saleDate - info.suspensionPeriod

/-- The `fiveYearPeriod` is a five year span, ending on the `periodEndDate`. -/
def Info.fiveYearPeriod : DateRange := 
  info.periodEndDate.reachingBack <| Duration.fromYears 5

/-- The two year period preceding the sale; used to check whether there was another S121 
   transaction too close to the current one. -/
def Info.twoYearPeriod : DateRange := 
  info.periodEndDate.reachingBack <| Duration.fromYears 2

def Info.ownershipPeriod : DateRange := 
  info.ownershipStart ...= info.saleDate, info.h0

abbrev Info.ownershipDuration := info.ownershipPeriod.duration

def Info.qualifyingOwnership : DateList :=
  info.fiveYearPeriod ∩ info.ownershipPeriod

def Info.qualifyingUse : DateList := 
  info.fiveYearPeriod ∩ info.principalResidencePeriods

/--The period after the last qualifying use, and before the end of the 5 year period. 
   Used in calculating the periods of nonqualifying use. -/
def Info.afterLastQualifying : DateList := 
  match info.qualifyingUse.max with
  | none => ∅ 
  | some m => if h0 : m <= info.periodEndDate then m ...= info.periodEndDate, h0 else ∅ 

/-- The identified periods of nonqualified use. The difference between the period in which
    the property was owned, and the union of periods prior to 2009, periods of qualifying use,
    periods after the last instance of qualifying use, any extended duty, and any time taken off
    for exigent circumstances as defined in S121. -/
def Info.nonqualifyingUse : DateList :=
  info.ownershipPeriod \ (0/1/1 ... 2009/1/1 ∪ info.qualifyingUse ∪ info.afterLastQualifying ∪ info.extendedDuty ∪ info.emergencyTime)

/-- Taxpayer meets the ownership requirement if, during the `fiveYearPeriod`, they owned
    the property for at least 700 days. -/
@[simp, reducible] def Info.ownershipRequirementMet :=
  DateList.cumulativeDuration info.qualifyingOwnership >= Duration.fromYears 2

/-- Taxpayer meets the use requirement if, during the `fiveYearPeriod`, they used the property
    as their principal residence for at least 700 days. -/
@[simp, reducible] def Info.useRequirementMet := info.qualifyingUse.cumulativeDuration >= Duration.fromYears 2

/-- The realized gain, minus the depreciation taken after May 6, 1997. -/
def Info.gainLessDepreciation := realizedGainLoss info - info.applicableDepreciationTaken

/-- cumulative duration of nonqualifying use periods / total duration of ownership -/
def Info.nonqualifiedUseRatio : Rat := ⟨info.nonqualifyingUse.cumulativeDuration.val, info.ownershipDuration.val, info.h4⟩

/-- The amount of gain attributable to periods of nonqualified use. -/
def Info.nonqualifiedUseGain := info.gainLessDepreciation * info.nonqualifiedUseRatio

/-- The amount of gain eligible for nonrecognition. Calculated as eligible gain minus
    the eligible gain attributable to nonqualified use. -/
def Info.eligibleGain := info.gainLessDepreciation - info.nonqualifiedUseGain

/-- A taxpayer qualifies for the maximum nonrecognition if they meet the ownership
    requirement, use requirement, and have not claimed a section 121 nonrecognition
    in the last two years. -/
@[reducible] def Info.qualifiesForMax : Prop := 
  info.ownershipRequirementMet ∧ info.useRequirementMet ∧ ¬info.timeSinceLast121.isSome

@[reducible] def Info.qualifiesForPartial : Prop := 
  info.exigentSale ∧ (info.timeSinceLast121.isSome ∨ ¬info.ownershipRequirementMet ∨ ¬info.useRequirementMet)

/-- 
The partial ratio, if one is warranted. Defined as (x / 730 days), where x
is the minimum of the ownership duration, qualifying use duration, and time
since the last 121 use if there is one. Because we have a proof that this taxpayer
qualifies for partial nonrecognition, a proof (below) that NAND max partial,
and a proof that partial qualification requires that one of the three values
is less than 730 days, we know that this ratio is less than one.
-/
def Info.partialRatio (h : info.qualifiesForPartial) : Rat := 
  let base := (min info.qualifyingUse.cumulativeDuration info.qualifyingOwnership.cumulativeDuration)
  match info.timeSinceLast121 with
  | none => ⟨base.days, 730, by decide⟩ 
  | some d => ⟨(min d.val base).days, 730, by decide⟩ 
    
theorem Info.partial_ratio_denom (h : info.qualifiesForPartial) : (info.partialRatio h).den = 730 := by
  simp [partialRatio]; split <;> simp

theorem Info.req_or : 
  info.qualifiesForPartial 
  -> info.timeSinceLast121 = none 
  -> ¬info.useRequirementMet ∨ ¬info.ownershipRequirementMet := by
  intro h h'
  simp [qualifiesForPartial, h'] at h
  simp [useRequirementMet, ownershipRequirementMet]
  apply Or.swap; exact h.right

theorem Info.partial_lt_none
  (h0 : info.qualifiesForPartial) 
  (h1 : info.timeSinceLast121 = none)
  : (info.partialRatio h0).num < (info.partialRatio h0).den := by
  have h2 := right_or_of_not_left h0.right (Option.not_isSome_iff_eq_none.mpr h1)
  simp [(show Duration.fromYears 2 = Duration.fromDays 730 by rfl), Duration.fromDays, Duration.lt_def] at h2
  simp [partialRatio, h1, Duration.days, Nat.div_lt_iff_lt_mul (show 0 < oneDayNanos by decide)]
  match casesmin (DateList.cumulativeDuration info.qualifyingUse) (DateList.cumulativeDuration info.qualifyingOwnership) with
  | Or.inl hl => 
    rw [hl]
    match h2 with
    | Or.inl hl' => have hl'' := casesmin2 hl; exact lt_of_le_of_lt hl'' hl'
    | Or.inr hr' => exact hr'
  | Or.inr hr => 
    rw [hr]
    match h2 with
    | Or.inl hl' => exact hl'
    | Or.inr hr' => rw [min_comm] at hr; have hr'' := casesmin2 hr; exact lt_of_le_of_lt hr'' hr'

theorem Info.partial_lt_some 
  (h0 : info.qualifiesForPartial) 
  (h1 : info.timeSinceLast121.isSome)
  : (info.partialRatio h0).num < (info.partialRatio h0).den := by
  have h_or := h0.right
  simp [(show Duration.fromYears 2 = Duration.fromDays 730 by rfl)] at h_or
  simp [partialRatio, h1, Duration.days]
  have is_some_thing : ∀ {d}, info.timeSinceLast121 = some d -> (d.val.val < 730 * oneDayNanos) := by
    intro d h; have h' := d.property; simp [Duration.fromDays, Duration.lt_def] at h'; exact h'
  split
  next opt => rw [opt] at h1; cases h1
  next _ d h_some =>
    simp [Duration.fromDays, Duration.lt_def] at h_or
    simp [Nat.div_lt_iff_lt_mul (show 0 < oneDayNanos by decide)]
    byCases hx : d.val <= (min (DateList.cumulativeDuration info.qualifyingUse) (DateList.cumulativeDuration info.qualifyingOwnership))
    case inl => rw [min_eq_left hx]; exact is_some_thing h_some
    case inr =>
      have h_le := le_of_not_ge hx
      rw [min_eq_right h_le]
      exact lt_of_le_of_lt h_le (is_some_thing h_some)

/-- 
If a taxpayer qualifies for partial nonrecognition, their nonrecognition will always
be less than the base max nonrecognition.
-/
theorem Info.partial_lt (h : info.qualifiesForPartial) : (info.partialRatio h).num < (info.partialRatio h).den := by
  byCases hx : info.timeSinceLast121.isSome
  case inl => exact info.partial_lt_some h hx
  case inr => 
    rw [Option.not_isSome_iff_eq_none] at hx
    exact info.partial_lt_none h hx

/-- 
A taxpayer can qualify for the max nonrecognition, partial nonrecognition, or neither,
but they cannot qualify for both max and partial.
-/
theorem Info.nand_max_partial : ¬(info.qualifiesForMax ∧ info.qualifiesForPartial)
| ⟨h_max, h_partial⟩ =>
    have h_mp : info.qualifiesForMax -> ¬info.qualifiesForPartial := by
      simp [qualifiesForMax, qualifiesForPartial]
      intro h_own h_use h121 h' hf
      match hf with
      | Or.inl hL => exact absurd hL h121
      | Or.inr (Or.inl hL) => rw [lt_iff_not_ge] at hL; exact absurd h_own hL
      | Or.inr (Or.inr hR) => rw [lt_iff_not_ge] at hR; exact absurd h_use hR
  (h_mp h_max) h_partial

/--The base nonrecognition is either $250,000 or $500,000 -/
theorem Info.base_nonrecognition_cases (i : Info) : i.baseNonrecognition = 250000 ∨ i.baseNonrecognition = 500000 := by
  simp [baseNonrecognition]; split
  next => exact Or.inl rfl
  next => exact Or.inr rfl

/--The base nonrecognition is always non-negative. -/
theorem Info.base_nonrecognition_nonneg (info : Info) : 0 <= info.baseNonrecognition := 
  match info.base_nonrecognition_cases with
  | Or.inl hl => by rw [hl]; decide
  | Or.inr hr => by rw [hr]; decide

@[reducible, simp] 
def Info.maxPermittedNonrec := 
  if h_max : info.qualifiesForMax
  then info.baseNonrecognition
  else if h_partial : info.qualifiesForPartial
  then info.baseNonrecognition * info.partialRatio h_partial
  else 0

 @[reducible, simp] 
 def Info.nonrec : Money := min info.eligibleGain info.maxPermittedNonrec

def Info.maxNonrecognition (h : info.qualifiesForMax) : { n : Int // n <= info.baseNonrecognition } := 
  ⟨min info.eligibleGain info.baseNonrecognition, min_le_right _ _⟩ 

def Info.partialNonrecognition (h : info.qualifiesForPartial) : { n : Int // n <= info.baseNonrecognition }  := 
  have h0 := le_trans (min_le_right _ _) (int_rat_hMul_le info.baseNonrecognition info.base_nonrecognition_nonneg <| (le_of_lt $ info.partial_lt h))
  ⟨min info.eligibleGain (info.baseNonrecognition * info.partialRatio h), h0⟩ 

def Info.tryNonrecognition : Option { n : Int // n <= info.baseNonrecognition } := 
  if h_max : info.qualifiesForMax
  then some <| info.maxNonrecognition h_max
  else if h_partial : info.qualifiesForPartial
  then some <| info.partialNonrecognition h_partial
  else none

def Info.nonrecognition : Money := 
  match info.tryNonrecognition with
  | some ⟨n, _⟩ => n
  | none => 0

instance : Nonrecognition Info where
  unrecognizedGainLoss := Info.nonrecognition
  recognizedGainLoss := fun info => info.amtRealized - info.nonrecognition
  deferredGainLoss := fun _ => 0

end InfoStuff

def Info.qualifyingWidowed
  (combined : Info)
  (unmarriedAtTimeOfSale : Bool)
  (dateOfPassing : Date) : Prop :=
  unmarriedAtTimeOfSale
  ∧ combined.saleDate - dateOfPassing <= (Duration.fromYears 2)
  ∧ combined.ownershipRequirementMet
  ∧ combined.useRequirementMet

@[reducible] def qualifyingJoint
  (spouse1 : { i : Info // i.kind = Kind.single })
  (spouse2 : { i : Info // i.kind = Kind.single }) : Prop :=
  (spouse1.val.ownershipRequirementMet ∨ spouse2.val.ownershipRequirementMet)
  ∧ (spouse1.val.useRequirementMet ∧ spouse2.val.useRequirementMet)
  ∧ ¬(spouse1.val.timeSinceLast121.isSome ∨ spouse2.val.timeSinceLast121.isSome)

/-- The actual nonrecognition is always less than or equal to the base nonrecognition. -/
theorem Info.nonrecognition_le_base_nonrecognition (i : Info) : i.nonrecognition <= i.baseNonrecognition := by
  simp [nonrecognition]
  split
  next p _ => exact p
  next => 
    match i.base_nonrecognition_cases with
    | Or.inl hl => rw [hl]; decide
    | Or.inr hr => rw [hr]; decide

/-- The actual nonrecognition is always less than or equal to $500,000, regardless of filing status. -/
theorem Info.nonrecognition_le_max (i : Info) : i.nonrecognition <= 500000 := by
  simp [nonrecognition]
  split
  next p h => 
    match i.base_nonrecognition_cases with
    | Or.inl hl => rw [hl] at p; exact le_trans p (by decide)
    | Or.inr hr => rw [hr] at p; assumption
  next => simp

section Lawful

open Info Kind

/-
The code section indicates that there exists SOME function taxpayers are supposed to
use to combine their S121 information when creating a joint return, and there
are some properties we know this function has to have. However, it doesn't actually
tell us what the full function is. For spouses who don't meet the joint max nonrecognition
requirements, the code says they're to file as if they weren't married. Can they therefore
claim e.g. different suspension periods? To respect this ambiguity, we make the theorems 
generic over any function which combines two sets of S121 information and respects the
properties we know it has to exhibit. In this way, we can show that the theorems hold
for any function which respects the relevant requirements.

Users are free to experiment with different conforming functions and see what different
tax results are produced.
-/
variable {A : Type u} (info : Info) 
  (combineSpouses : ∀ (s₁ s₂ : { i : Info // i.kind = single }), Info)
  (hSpouses : ∀ s₁ s₂, (combineSpouses s₁ s₂).kind = Kind.joint)
  (combineSpousesOwnership : 
    ∀ s₁ s₂, ¬qualifyingJoint s₁ s₂ → (combineSpouses s₁ s₂).ownershipPeriod = (s₁.val.ownershipPeriod : DateList) ∪ s₂.val.ownershipPeriod)
  (combineSpousesOr : 
    ∀ s₁ s₂, s₁.val.qualifiesForMax ∨ s₂.val.qualifiesForMax → (combineSpouses s₁ s₂).qualifiesForMax  ∨ (combineSpouse s₁ s₂).qualifiesForPartial)
  (combineWidowed : ∀ (s₁ s₂ : { i : Info // i.kind = widowed }), Info)
  (hWidowed: ∀ s₁ s₂, (combineWidowed s₁ s₂).kind = Kind.widowed)

/--
If a taxpayer qualifies for the max nonrecognition by meeting the requirements of section (a),
then there exists some amount that is not recognized as income. Sort of vacuous, but this is
essentially what 121(a) says.
-/
theorem «121(a)» : info.qualifiesForMax → ∃ nr, info.maxNonrecognition h = nr :=
  fun h => Exists.intro (info.maxNonrecognition h) rfl

/--The nonrecognition for single filing taxpayers never exceeds $250,000 -/
theorem «121(b)(1)» (h0 : info.kind = Kind.single) : info.nonrecognition <= 250000 := by
  simp [nonrecognition, tryNonrecognition]
  split
  next h_le _ => simp [baseNonrecognition, h0] at h_le; exact h_le
  next => simp

/--
For spouses who meet the joint max nonrec requirements, their base nonrecognition is $500,000, 
and under no circumstances does their recognition exceed $500,000.
-/
theorem «121(b)(2)(A)» (s1 s2) (joint : Info) (h : qualifyingJoint s1 s2 ∧ joint = combineSpouses s1 s2) : 
  joint.nonrecognition <= 500000 ∧ joint.baseNonrecognition = 500000 := by
  refine And.intro joint.nonrecognition_le_max ?r
  simp [baseNonrecognition]
  split
  next h' => rw [h.right, hSpouses s1 s2] at h'; cases h'
  next => rfl

/--If a joint filing qualifies for the max nonrecognition, at least one spouse fulfills the ownership requirement. -/
theorem «121(b)(2)(A)(i)» (s1 s2) (h : qualifyingJoint s1 s2) : s1.val.ownershipRequirementMet ∨ s2.val.ownershipRequirementMet := h.left
/--If a joint filing qualifies for the max nonrecognition, both spouses fulfill the use requirement. -/
theorem «121(b)(2)(A)(ii)» (s1 s2) (h : qualifyingJoint s1 s2) : s1.val.useRequirementMet ∧ s2.val.useRequirementMet := h.right.left
/--If a joint filing qualifies for the max nonrecognition, neither spouse has claimed 121 nonrecognition in the last 2 years. -/
theorem «121(b)(2)(A)(iii)» (s1 s2) (h : qualifyingJoint s1 s2) : ¬(s1.val.timeSinceLast121.isSome ∨ s2.val.timeSinceLast121.isSome) := h.right.right

/--
For spouses filing jointly who do NOT meet the requirements needed to get the $500,000 base
nonrecognition, the base nonrecognition for their joint filing is equal to the sum of their
individual nonrecognitions, as if they had filed without being married.
-/
theorem «121(b)(2)(B)» (s1 s2) (combined : Info) (h : ¬qualifyingJoint s1 s2 ∧ combined = combineSpouses s1 s2) : 
  combined.baseNonrecognition = s1.val.baseNonrecognition + s2.val.baseNonrecognition
  ∧ combined.ownershipPeriod = (s1.val.ownershipPeriod : DateList) ∪ s2.val.ownershipPeriod := by
    refine And.intro ?l (h.right ▸ (combineSpousesOwnership s1 s2 h.left))
    simp [baseNonrecognition, h.right, hSpouses s1 s2, s1.property, s2.property]

/--
A taxpayer who has claimed nonrecognition under S121 in the last two years
cannot qualify for the max nonrecognition.
-/
theorem «121(b)(3)» : info.timeSinceLast121.isSome → ¬info.qualifiesForMax := 
  fun h_last ⟨_, _, h_last'⟩ => absurd h_last h_last'

/--
Taxpayers who fulfill the conditions of (b)(4) for a widowed taxpayer are eligible for a base 
nonrecognition of $500,000
-/
theorem «121(b)(4)» 
  (s1 s2) 
  (combined)
  (h : combined = combineWidowed s1 s2)
  (unmarriedAtTimeOfSale : Bool)
  (dateOfPassing : Date) : 
  combined.qualifyingWidowed unmarriedAtTimeOfSale dateOfPassing -> combined.baseNonrecognition = 500000 := by
    simp [baseNonrecognition, (h ▸ hWidowed s1 s2 : combined.kind = widowed)]

/--
The eligible gain does not include the amount allocated to periods of nonqualified use;
the allocation is accomplished by subtracting some fraction defined as `nonqualifiedUseRatio`.
-/
theorem «121(b)(5)(A)» : info.eligibleGain = info.gainLessDepreciation - (info.gainLessDepreciation * info.nonqualifiedUseRatio) := rfl

/--
The nonqualified use ratio is the cumulative duration of the periods of nonqualifying
use over the total ownership duration.
-/
theorem «121(b)(5)(B)» : info.nonqualifiedUseRatio = ⟨info.nonqualifyingUse.cumulativeDuration.val, info.ownershipDuration.val, info.h4⟩  := rfl

/--
Nonqualifying use is defined in the negative. It's periods of ownership, but not including
periods before 2009, periods of qualifying use (as the principal residence), any time AFTER 
the last period of qualifying use (which is the tricky one), and not including time allocated
to qualified extended duty, or "emergency time" as defined earlier.
-/
theorem «121(b)(5)(C)» : info.nonqualifyingUse = (info.ownershipPeriod : DateList) \ (0/1/1 ... 2009/1/1 ∪ info.qualifyingUse ∪ info.afterLastQualifying ∪ info.extendedDuty ∪ info.emergencyTime) := rfl

/--5.A and 5.D.i end up being logically equivalent. -/
def «121(b)(5)(D)(i)» := «121(b)(5)(A)»

/--
Application of the nonqualified use ratio takes place after the subtraction
of the applicable depreciation.
-/
theorem «121(b)(5)(D)(ii)»  : info.nonqualifiedUseGain = info.gainLessDepreciation * info.nonqualifiedUseRatio := rfl

/--
The numerator of the partial exclusion ratio is equal to the minimum of
time since last 121 use, qualifying use periods, qualifying ownership periods,
and the denominator is 2 years.
-/
theorem «121(c)(1)» (h : info.qualifiesForPartial) : 
  ((info.partialRatio h).num = (min info.qualifyingUse.cumulativeDuration info.qualifyingOwnership.cumulativeDuration).days
  ∨ (∃ d, info.timeSinceLast121 = some d ∧ (info.partialRatio h).num = (min d.val (min info.qualifyingUse.cumulativeDuration info.qualifyingOwnership.cumulativeDuration)).days))
  ∧ (info.partialRatio h).den = 730 := 
  Classical.byCases (p := (∃ d, info.timeSinceLast121 = some d))
  (fun ⟨d, hd⟩ => by
    refine And.intro ?lp (info.partial_ratio_denom h)
    apply Or.inr
    refine (Exists.intro d) (And.intro hd ?hd2)
    simp only [partialRatio, hd])
  (fun hnp => by
    have h_op : info.timeSinceLast121 = none := Option.eq_none_of_nexi hnp
    refine And.intro ?lnp (info.partial_ratio_denom h)
    apply Or.inl
    simp only [partialRatio, h_op])


/--The exact definition of when a taxpayer qualifies for partial nonrecognition. -/
theorem «121(c)(2)» : 
  info.qualifiesForPartial = (info.exigentSale ∧ (info.timeSinceLast121.isSome ∨ ¬info.ownershipRequirementMet ∨ ¬info.useRequirementMet)) := rfl

/--
If a husband and wife make a joint return for the taxable year of the sale or exchange 
of the property, subsections (a) and (c) shall apply if either spouse meets the ownership 
and use requirements of subsection (a) with respect to such property.

Where (a) defines the max nonrecognition, and (c) defines the partial nonrecognition.
-/
theorem «121(d)(1)» 
  (s1 s2)
  (combined : Info)
  (h : combineSpouses s1 s2 = combined)
  (h' : s1.val.qualifiesForMax ∨ s2.val.qualifiesForMax) : 
  combined.qualifiesForMax ∨ combined.qualifiesForPartial := combineSpousesOr

/--Show that the eligible gain does not include depreciation taken after May 1996. -/
theorem «121(d)(6)» : info.eligibleGain = realizedGainLoss info - info.applicableDepreciationTaken - info.nonqualifiedUseGain := rfl

/--Show that the five year period accounts for the suspension period -/
theorem «121(d)(9)(A)» : info.fiveYearPeriod = ((info.saleDate - info.suspensionPeriod).reachingBack <| Duration.fromYears 5) := rfl

/--The suspension period does not exceed ten years. -/
theorem «121(d)(9)(B)» : info.suspensionPeriod <= Duration.fromYears 10 := info.h1

end Lawful