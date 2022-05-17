import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Int.Order
import Mathlib.Tactic.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Tax.Util
import Prolala.Federal.Sources

open Time Property PropertyTxn 

structure BaseLke' where
  /-- TP's adjusted basis in elements of outgoing like-kind property -/
  outgoingLkpAb : List NonnegMoney
  /-- TP's adjusted basis in elements out outgoing non-LKP -/
  outgoingOtherPropertyAb : List NonnegMoney
  /-- The fair market values of elements out outgoing non-LKP -/
  outgoingOtherPropertyFmv : List NonnegMoney
  /-- The total amount of outgoing cash -/
  outgoingCash : NonnegMoney
  /-- The sum of any libilities being assumed by the other party -/
  outgoingLiabilities : NonnegMoney
  /-- The fair market values of incoming property that is of like-kind -/
  incomingLkpFmv : List NonnegMoney
  /-- The fair market values of incoming property that is not of like-kind -/
  incomingOtherPropertyFmv : List NonnegMoney
  /-- The sum of any incoming cash -/
  incomingCash : NonnegMoney
  /-- The sum of any liabilties being assumed by the taxpayer -/
  incomingLiabilities : NonnegMoney
  /-- true iff this exchange is being made by TP with a related party -/
  toRelatedParty : Bool
  heldPrimarilyForSale : Bool
  isUsProperty : Bool
  h_is_us_property : isUsProperty = true := by decide
  h_primarily_for_sale : heldPrimarilyForSale = false := by decide
  /-- The date when TP transferred the outgoing property to the recipient -/
  outgoingRelinquishedDate : Date
  /-- The date when the parties identified the incoming LKP to be exchanged -/
  identificationDate : Date
  /-- The date on which TP received the incoming property -/
  incomingReceivedDate : Date
  /-- The date on which the taxes are due for the year in which the exchange takes place -/
  taxYearDueDate : Date
  /-- The date on which the transaction is completed -/
  completionDate : Date
  h_due_date : outgoingRelinquishedDate <= taxYearDueDate := by decide
  timingOk1 : completionDate <= outgoingRelinquishedDate + Duration.fromDays 180 := by decide
  timingOk2 : identificationDate <= outgoingRelinquishedDate + Duration.fromDays 45 := by decide
  timingOk3 : incomingReceivedDate <= min (outgoingRelinquishedDate + Duration.fromDays 180)  taxYearDueDate := by decide
  h_outgoing_other_property : outgoingOtherPropertyAb.length = outgoingOtherPropertyFmv.length := by decide
  h_num : incomingLkpFmv.length <= 3 ∨ sum incomingLkpFmv <= 2 * (sum outgoingLkpAb).val := by decide
deriving Repr

structure LkeResult where
  completionDate : Date
  recognizedGainLoss : NonnegMoney
  basisIncomingLkp : Money
  basisIncomingBootProperty : NonnegMoney
  relatedPartySunsetDate : Option Date
  source : Tax.SourceOfLaw
deriving Repr, DecidableEq

open BaseLke' 
section BaseLke'Section
variable (txn : BaseLke')

/-- Incoming cash, plus net outgoing liabilities -/
def BaseLke'.incomingMoney := txn.incomingCash.val + (max 0 <| txn.outgoingLiabilities.val - txn.incomingLiabilities)

/-- Outgoing cash, plus net incoming liabilities -/
def BaseLke'.outgoingMoney := txn.outgoingCash.val + (max 0 <| txn.incomingLiabilities.val - txn.outgoingLiabilities.val)

/-- All incoming money and property, excluding like-kind property -/
def BaseLke'.incomingBoot := sum txn.incomingOtherPropertyFmv + txn.incomingMoney

/-- All outgoing money and property excluding like-kind property -/
def BaseLke'.outgoingBoot := sum txn.outgoingOtherPropertyFmv + txn.outgoingMoney

/- The basis in the incoming boot property (non-cash) is just the fair market value. -/
def BaseLke'.basisIncomingBootProperty := sum txn.incomingOtherPropertyFmv

theorem BaseLke'.incoming_money_nonneg : 0 <= txn.incomingMoney := 
  Int.add_nonneg txn.incomingCash.property <| le_max_left 0 _
theorem BaseLke'.outgoing_money_nonneg : 0 <= txn.outgoingMoney := 
  Int.add_nonneg txn.outgoingCash.property <| le_max_left 0 _
theorem BaseLke'.incoming_boot_nonneg : 0 <= txn.incomingBoot := 
  Int.add_nonneg (sum txn.incomingOtherPropertyFmv).property txn.incoming_money_nonneg
theorem BaseLke'.outgoing_boot_nonneg : 0 <= txn.outgoingBoot := 
  Int.add_nonneg (sum txn.outgoingOtherPropertyFmv).property txn.outgoing_money_nonneg

instance : PropertyTxn BaseLke' where
  adjustedBasis (txn) := sum txn.outgoingLkpAb + txn.outgoingMoney
  amtRealized (txn) := sum txn.incomingLkpFmv + txn.incomingBoot

def BaseLke'.otherRecognizedGainLoss := (sum txn.outgoingOtherPropertyFmv).val - (sum txn.outgoingOtherPropertyAb)

def BaseLke'.recognizedGainLoss := max 0 (min (incomingBoot txn) (realizedGainLoss txn))

def BaseLke'.totalBasisIncoming := 
  if txn.outgoingOtherPropertyAb.isEmpty
  then adjustedBasis txn - incomingMoney txn + recognizedGainLoss txn
  else adjustedBasis txn + sum txn.outgoingOtherPropertyAb + otherRecognizedGainLoss txn

def BaseLke'.basisIncomingLkp := txn.totalBasisIncoming - sum txn.incomingOtherPropertyFmv

@[reducible] def BaseLke'.identificationPeriod := 
  DateRange.mkInclusive
    txn.outgoingRelinquishedDate
    (txn.outgoingRelinquishedDate + Duration.fromDays 45)
    (Date.le_add_right _ _)

@[reducible] def BaseLke'.exchangePeriod : DateRange := 
  DateRange.mkInclusive
    txn.outgoingRelinquishedDate
    (min (txn.outgoingRelinquishedDate + Duration.fromDays 180) txn.taxYearDueDate)
    (Date.le_min (Date.le_add_right _ _) txn.h_due_date)

instance : Conditioned LkeResult where
  conditions (r) := 
    [
      ("Exchanaged property claimed to be of like-kind is held for productive use in a trade or business or for investment.", ⟨"26 U.S.C. § 1031(a)(1)"⟩),
      ("Exchanged property claimed to be of like-kind is not held primarily for sale.", ⟨"26 U.S.C. § 1031(a)(2)"⟩),
      ("Exchanged property claimed to be of like-kind is located in the United States.", ⟨"26 U.S.C. § 1031(h)"⟩)
    ]

instance : Explain LkeResult where
  explain (r) := 
    "Result to taxpayer is subject to the following conditions:\n"
    ++ (Conditioned.conditions r).foldl (fun sink next => sink ++ s!"- {next.fst} {next.snd.citation}.\n") ""
    ++ "\n"
    ++ "Result to taxpayer:\n"
    ++ s!"Taxpayer's recognized gain or loss is ${r.recognizedGainLoss}\n"
    ++ s!"Taxpayer's basis in the incoming like-kind property is ${r.basisIncomingLkp}\n"
    ++ s!"taxpayer's basis in the incoming non-like-kind property is ${r.basisIncomingBootProperty}\n"

def BaseLke'.taxResult : LkeResult :=
  {
    completionDate := txn.completionDate
    recognizedGainLoss := ⟨txn.recognizedGainLoss, le_max_left 0 _⟩
    basisIncomingLkp := txn.basisIncomingLkp
    basisIncomingBootProperty := txn.basisIncomingBootProperty
    relatedPartySunsetDate := 
      if txn.toRelatedParty 
      then some <| txn.completionDate + Duration.fromYears 2
      else none
    source := ⟨Administrative.cfr 26, by decide⟩
  }

def BaseLke'.taxResultM : StateT String Id LkeResult := do
  let r := {
    completionDate := txn.completionDate
    recognizedGainLoss := ⟨txn.recognizedGainLoss, le_max_left 0 _⟩
    basisIncomingLkp := txn.basisIncomingLkp
    basisIncomingBootProperty := txn.basisIncomingBootProperty
    relatedPartySunsetDate := 
      if txn.toRelatedParty 
      then some <| txn.completionDate + Duration.fromYears 2
      else none
    source := ⟨Administrative.cfr 26, by decide⟩
  }
  modify (fun s => s ++ Explain.explain r)
  return r
  
end BaseLke'Section


section BaseLke'Section

variable (txn : BaseLke')

@[simp] theorem BaseLke'.incoming_money_zero_of_incoming_boot_zero : txn.incomingBoot = 0 → txn.incomingMoney = 0 := 
  fun h => add_eq_zero_right (sum txn.incomingOtherPropertyFmv).property txn.incoming_money_nonneg h

@[simp] theorem BaseLke'.sum_incoming_other_property_fmv_of_incoming_boot_zero : txn.incomingBoot = 0 → sum txn.incomingOtherPropertyFmv = 0 := 
  fun h => subtype_eq $ add_eq_zero_left (sum txn.incomingOtherPropertyFmv).property (le_of_eq $ (txn.incoming_money_zero_of_incoming_boot_zero h).symm) h

@[simp] theorem BaseLke'.outgoing_money_zero_of_outgoing_boot_zero : txn.outgoingBoot = 0 → txn.outgoingMoney = 0 := 
  fun h => add_eq_zero_right (sum txn.outgoingOtherPropertyFmv).property txn.outgoing_money_nonneg h

@[simp] theorem BaseLke'.sum_outgoing_other_property_fmv_of_outgoing_boot_zero : txn.outgoingBoot = 0 → sum txn.outgoingOtherPropertyFmv = 0 := 
  fun h => subtype_eq $ add_eq_zero_left (sum txn.outgoingOtherPropertyFmv).property (le_of_eq $ (txn.outgoing_money_zero_of_outgoing_boot_zero h).symm) h

theorem base_usc_compliant1 (h : txn.outgoingOtherPropertyFmv.isEmpty) : 
  amtRealized txn = sum txn.incomingLkpFmv + txn.incomingBoot := by
  simp [amtRealized, sum_zero_of_empty h]

theorem base_usc_compliant2 (h : txn.outgoingOtherPropertyAb.isEmpty) : 
  txn.totalBasisIncoming = adjustedBasis txn - incomingMoney txn + recognizedGainLoss txn := by
  simp [-List.isEmpty, totalBasisIncoming, h]

/-- In a sub-section (a) transfer (a transfer purely of LKP), there is no
    recognized gain or loss. -/
theorem BaseLke'.«1031(a)(1)» (h : incomingBoot txn = 0) : recognizedGainLoss txn = 0 := by
  simp only [recognizedGainLoss, realizedGainLoss, h, min_le_left 0]
  exact max_eq_left <| min_le_left 0 _

/-- Marker -/
theorem BaseLke'.«1031(a)(2)» : ¬heldPrimarilyForSale txn := by rw [h_primarily_for_sale txn]; simp

/-- Requirement that property be identified and that exchange be completed not 
    more than 180 days after transfer of exchanged property -/
theorem BaseLke'.«1031(a)(3)» : 
  identificationDate txn <= outgoingRelinquishedDate txn + Duration.fromDays 180
  ∧ completionDate txn <= outgoingRelinquishedDate txn + Duration.fromDays 180 := by
  refine And.intro ?l txn.timingOk1
  have h0 : txn.outgoingRelinquishedDate + Duration.fromDays 45 <= txn.outgoingRelinquishedDate + Duration.fromDays 180 := 
    Date.add_le_add_left (by decide)
  exact le_trans txn.timingOk2 h0

/-- Identification of the incoming LKP has to be done within 45 days of the outgiong LKP
    being relinquished. -/
theorem BaseLke'.«1031(a)(3)(A)» : identificationDate txn <= outgoingRelinquishedDate txn + Duration.fromDays 45 := timingOk2 txn

/-- The incoming LKP must be received within the shorter of (relinquished + 180 days),
    or the due date of the relevant taxes. -/
theorem BaseLke'.«1031(a)(3)(B)» : 
  txn.incomingReceivedDate <= min (outgoingRelinquishedDate txn + Duration.fromDays 180) txn.taxYearDueDate := txn.timingOk3

/-- Covers both ways of stating (b), with the second being more rigorous;
    the recognized gain loss shall not exceed the amount of boot, and the recognized
    gain loss is equal to the amount of gain attributable to boot. -/
theorem BaseLke'.«1031(b)» : txn.recognizedGainLoss <= txn.incomingBoot ∧ recognizedGainLoss txn = max 0 (min txn.incomingBoot (realizedGainLoss txn)) := by
  refine And.intro ?l rfl
  simp only [recognizedGainLoss]
  byCases h' : 0 <= min (incomingBoot txn) (realizedGainLoss txn)
  case inl => rw [max_eq_right h']; exact min_le_left _ _
  case inr => 
    rw [max_eq_left <| le_of_lt <| lt_of_not_ge h']
    exact Int.add_nonneg (sum <| txn.incomingOtherPropertyFmv).property txn.incoming_money_nonneg

/-- No loss shall be recognized, regardless of whether or not there's incoming boot. -/
theorem BaseLke'.«1031(c)» : recognizedGainLoss txn >= 0 := le_max_left 0 _

/-- Provided there's no outgoing non-LKP, the total basis in the incoming property is 
   calculated in the manner required by 1031, and the basis in incoming non-LKP is 
   equal to the fair market value. -/
theorem BaseLke'.«1031(d)» : 
  (txn.outgoingOtherPropertyAb.isEmpty → totalBasisIncoming txn = adjustedBasis txn - incomingMoney txn + recognizedGainLoss txn)
  ∧ basisIncomingBootProperty txn = sum txn.incomingOtherPropertyFmv := by
  refine And.intro ?l rfl
  intro h; simp [-List.isEmpty, basisIncomingBootProperty, totalBasisIncoming, h]

/-- Marker -/
theorem BaseLke'.«1031(h)» : txn.isUsProperty := txn.h_is_us_property

@[simp] 
theorem BaseLke'.incoming_property_zero_of_incoming_boot_zero : txn.incomingBoot = 0 → sum txn.incomingOtherPropertyFmv = 0 := 
  fun h => subtype_eq (add_eq_zero_left (sum txn.incomingOtherPropertyFmv).property txn.incoming_money_nonneg h)

@[simp] 
theorem total_basis_incoming_empty (h : txn.outgoingOtherPropertyAb.isEmpty) :
  txn.totalBasisIncoming = adjustedBasis txn - txn.incomingMoney + txn.recognizedGainLoss := by
  delta BaseLke'.totalBasisIncoming; simp only [h, if_true]

@[simp] 
abbrev BaseLke'.purelyLke := txn.incomingBoot = 0 ∧ txn.outgoingBoot = 0 ∧ txn.outgoingOtherPropertyAb.isEmpty

/- There are naming conventions you get used to, but also tactics like `library_search` and
   `simp` are important automation tools. -/
theorem BaseLke'.recognized_gain_loss_zero_of_purely_lke : txn.purelyLke → txn.recognizedGainLoss = 0 := by
  intro ⟨h_in, h_out⟩; simp [recognizedGainLoss, h_in, max_zero_min_zero]

/- 1.1031(a) is about (qualitatively) what makes property "of like kind". -/

/- Both ways of stating that the recognized gain or loss is only to the extent of any boot;
   First that it's simply less than or equal to, and second, the more rigorous definition
   that the recognized gain loss is equal to the realized gain attributable direclty to
   the incoming boot. -/
theorem BaseLke'.«1.1031(b)-1» : txn.recognizedGainLoss <= txn.incomingBoot ∧ txn.recognizedGainLoss = max 0 (min txn.incomingBoot (realizedGainLoss txn)) := by
  refine And.intro ?l rfl
  simp only [recognizedGainLoss]
  byCases h' : 0 <= min txn.incomingBoot (realizedGainLoss txn)
  case inl => rw [max_eq_right h']; exact min_le_left _ _
  case inr => 
    rw [max_eq_left <| le_of_lt <| lt_of_not_ge h']
    exact Int.add_nonneg (sum txn.incomingOtherPropertyFmv).property txn.incoming_money_nonneg

/- Assumed liabilties are considered part of the formula for incoming and outgoing money. -/
theorem BaseLke'.«1.1031(b)-2» :
  txn.incomingMoney = txn.incomingCash.val + (max 0 <| txn.outgoingLiabilities.val - txn.incomingLiabilities.val)
  ∧ txn.outgoingMoney = txn.outgoingCash.val + (max 0 <| txn.incomingLiabilities.val - txn.outgoingLiabilities.val) :=
  ⟨rfl, rfl⟩ 

/- Reiteration of the US Code section 1031(c); no loss shall be recognized. -/
theorem BaseLke'.«1.1031(c)» : recognizedGainLoss txn >= 0 := le_max_left 0 _

/- If this is a purely like-kind exchange, then the total basis in the incoming property
   is equal fo the original adjusted basis in the outgoing lkp. -/
theorem BaseLke'.«1.1031(d)-1(a)(1)» (h : txn.purelyLke) : txn.totalBasisIncoming = sum txn.outgoingLkpAb := by
  have ⟨h_in, h_out, h_out'⟩ := h
  simp [
    -List.isEmpty, 
    adjustedBasis,
    totalBasisIncoming, 
    h_out', 
    recognized_gain_loss_zero_of_purely_lke _ h,
    outgoing_money_zero_of_outgoing_boot_zero _ h_out, 
    incoming_money_zero_of_incoming_boot_zero _ h_in
  ]

/- If there's no incoming boot, then the basis in the incoming LKP is equal to
   the sum of the outgoing lkps adjuted basis and any outgoing boot. -/
theorem BaseLke'.«1.1031(d)-1(a)(2)» : txn.incomingBoot = 0 → txn.basisIncomingLkp = sum txn.outgoingLkpAb + txn.outgoingBoot := by
    intro h
    simp [-List.isEmpty, basisIncomingLkp, totalBasisIncoming]
    rw [incoming_money_zero_of_incoming_boot_zero _ h]
    byCases hx : txn.outgoingOtherPropertyAb.isEmpty 
    case inl =>
      simp [-List.isEmpty, hx, recognizedGainLoss]
      rw [empty_iff_empty txn.h_outgoing_other_property] at hx
      rw [incoming_property_zero_of_incoming_boot_zero, h]
      simp [max_zero_min_zero, adjustedBasis, outgoingBoot, sum_zero_of_empty hx, zero_add]
      exact h
    case inr =>
      simp [-List.isEmpty, hx, otherRecognizedGainLoss]
      rw [incoming_property_zero_of_incoming_boot_zero]
      simp [sub_zero, adjustedBasis, outgoingBoot, outgoingMoney]
      generalize hy : txn.outgoingCash.val + max 0 (txn.incomingLiabilities.val - txn.outgoingLiabilities.val) = y
      generalize hq : (sum txn.outgoingLkpAb).val = q
      rw [add_comm (sum txn.outgoingOtherPropertyFmv).val y, <- add_assoc q y]
      rw [show ((sum txn.outgoingOtherPropertyFmv).val - (sum txn.outgoingOtherPropertyAb).val = (sum txn.outgoingOtherPropertyFmv).val + -(sum txn.outgoingOtherPropertyAb).val) by rfl]
      generalize hz : q + y = z
      rw [add_assoc z, add_cancel_mid (sum txn.outgoingOtherPropertyAb).val (sum txn.outgoingOtherPropertyFmv).val]
      exact h

theorem BaseLke'.«1.1031(d)-1(b)» (h : txn.outgoingOtherPropertyAb.isEmpty) : 
  txn.totalBasisIncoming = adjustedBasis txn - incomingMoney txn + recognizedGainLoss txn := by
  simp [-List.isEmpty, totalBasisIncoming]
  byCases hx : txn.outgoingOtherPropertyAb.isEmpty
  case inl => simp [-List.isEmpty, hx]
  case inr => exact absurd h hx

/- The basis in the incoming boot is always equal to the fair market value of the boot. -/
theorem BaseLke'.«1.1031(d)-1(c)» : txn.basisIncomingBootProperty = sum txn.incomingOtherPropertyFmv := rfl
    
/- If there's no outgoing non-like-kind property, no loss will be recognized. -/
theorem BaseLke'.«1.1031(d)-1(d)» (h : txn.outgoingOtherPropertyAb.isEmpty) : recognizedGainLoss txn >= 0 := by
  simp [-List.isEmpty, recognizedGainLoss, h]
  byCases hx : min (incomingBoot txn) (realizedGainLoss txn) <= 0
  case inl => simp [max_eq_left hx]
  case inr => have hx' := lt_of_not_ge hx; simp [max_eq_right (le_of_lt hx')]; exact le_of_lt hx'

/- If there is outgoing non-like-kind property, an alternate formula for the adjusted basis
   in the incoming property is required, which considers the recognized gain/loss in the
   outgoing non-like-kind property. -/
theorem BaseLke'.«1.1031(d)-1(e)» (h : ¬txn.outgoingOtherPropertyAb.isEmpty) : 
  txn.totalBasisIncoming = adjustedBasis txn + sum txn.outgoingOtherPropertyAb + otherRecognizedGainLoss txn := by
  simp [-List.isEmpty, totalBasisIncoming, h]

/- Codifies the netting procedure for assumption of outgoing and incoming liabilities as part
   of the incoming money calculation. -/
theorem BaseLke'.«1.1031(d)-2» (h : ¬txn.outgoingOtherPropertyAb.isEmpty) : 
  txn.incomingMoney = txn.incomingCash.val + (max 0 <| txn.outgoingLiabilities.val - txn.incomingLiabilities.val) := rfl

/- Replacement property is identified before the end of the identification period -/
theorem BaseLke'.«1.1031(k)-1(b)(1)(i)» : txn.identificationDate < txn.identificationPeriod.high := Date.lt_succ_of_le txn.timingOk2

/- The identified property is received before the end of the exchange period -/
theorem BaseLke'.«1.1031(k)-1(b)(1)(ii)» : txn.incomingReceivedDate < txn.exchangePeriod.high := Date.lt_succ_of_le txn.timingOk3

/- (i) The identification period begins on the date the taxpayer transfers the 
   relinquished property and ends at midnight on the 45th day thereafter. -/
theorem BaseLke'.«1.1031(k)-1(b)(2)(i)» : 
  txn.identificationPeriod.startsOn txn.outgoingRelinquishedDate
  ∧ txn.identificationPeriod.endsMidnightOf (txn.outgoingRelinquishedDate + Duration.fromDays 45) := ⟨rfl, rfl⟩ 

/- (ii) The exchange period begins on the date the taxpayer transfers the relinquished 
   property and ends at midnight on the earlier of the 180th day thereafter or the due date 
   (including extensions) for the taxpayer's return of the tax imposed by chapter 1 of 
   subtitle A of the Code for the taxable year in which the transfer of the relinquished 
   property occurs. -/
theorem BaseLke'.«1.1031(k)-1(b)(2)(ii)» : 
  txn.exchangePeriod.startsOn txn.outgoingRelinquishedDate
  ∧ txn.exchangePeriod.endsMidnightOf (min (txn.outgoingRelinquishedDate + Duration.fromDays 180) txn.taxYearDueDate) :=
  ⟨rfl, rfl⟩

/- The 3 property or 200% rule -/
theorem BaseLke'.«1.1031(k)-1(c)(4)(i)» : txn.incomingLkpFmv.length <= 3 ∨ sum txn.incomingLkpFmv <= 2 * (sum txn.outgoingLkpAb).val := txn.h_num


end BaseLke'Section

namespace CfrExamples

/- Outgoing: LKP with basis of 10k
   Incoming: LKP w/ fmv 9k, car with fmv 2k, 1.5k cash. -/
def «CFR 1.1031(d)-1 example 1» : BaseLke' := 
  {
    outgoingOtherPropertyAb := []
    outgoingOtherPropertyFmv := []
    h_outgoing_other_property := by decide
    outgoingLkpAb := [10000]
    outgoingCash := ⟨0, by decide⟩ 
    outgoingLiabilities := ⟨0, by decide⟩ 
    incomingLkpFmv :=  [9000]
    incomingOtherPropertyFmv := [2000]
    incomingCash := ⟨1500, by decide⟩ 
    incomingLiabilities := ⟨0, by decide⟩ 
    toRelatedParty := false
    heldPrimarilyForSale := false
    isUsProperty := true
    h_is_us_property := rfl
    h_primarily_for_sale := rfl
    outgoingRelinquishedDate := Date.fromYmd 1954 1 1
    identificationDate := Date.fromYmd 1954 1 1
    incomingReceivedDate := Date.fromYmd 1954 1 1
    taxYearDueDate := Date.fromYmd 1954 4 15
    completionDate := Date.fromYmd 1954 1 1
    timingOk1 := by decide
    timingOk2 := by decide
    timingOk3 := by decide
  }

theorem «CFR 1.1031(d)-1 example 1_1» : realizedGainLoss «CFR 1.1031(d)-1 example 1» = 2500 := rfl
theorem «CFR 1.1031(d)-1 example 1_2» : recognizedGainLoss «CFR 1.1031(d)-1 example 1» = 2500 := rfl
theorem «CFR 1.1031(d)-1 example 1_3» : totalBasisIncoming «CFR 1.1031(d)-1 example 1» = 11000 := rfl
theorem «CFR 1.1031(d)-1 example 1_4» : basisIncomingBootProperty «CFR 1.1031(d)-1 example 1» = 2000 := rfl
theorem «CFR 1.1031(d)-1 example 1_5» : basisIncomingLkp «CFR 1.1031(d)-1 example 1» = 9000 := rfl

/- 
The outgoing "other property" in this example is stock in which the
taxpayer is suffering a loss.
-/
def «CFR 1.1031(d)-1 example 2» : BaseLke' := 
  {
    outgoingLkpAb := [10000]
    outgoingOtherPropertyAb := [4000]
    h_outgoing_other_property := by decide
    outgoingOtherPropertyFmv := [2000]
    outgoingCash := ⟨0, by decide⟩ 
    outgoingLiabilities := ⟨0, by decide⟩ 
    incomingLkpFmv :=  [13000]
    incomingOtherPropertyFmv := [] 
    incomingCash := ⟨0, by decide⟩ 
    incomingLiabilities := ⟨0, by decide⟩ 
    toRelatedParty := false
    heldPrimarilyForSale := false
    isUsProperty := true
    h_is_us_property := rfl
    h_primarily_for_sale := rfl
    outgoingRelinquishedDate := Date.fromYmd 2020 1 1
    identificationDate := Date.fromYmd 2020 1 1
    incomingReceivedDate := Date.fromYmd 2020 1 1
    taxYearDueDate := Date.fromYmd 2020 1 1
    completionDate := Date.fromYmd 2020 1 1
    timingOk1 := by decide
    timingOk2 := by decide
    timingOk3 := by decide
  }

theorem «CFR 1.1031(d)-1 example 2_1» : basisIncomingLkp «CFR 1.1031(d)-1 example 2» = 12000 := rfl
theorem «CFR 1.1031(d)-1 example 2_2» : otherRecognizedGainLoss «CFR 1.1031(d)-1 example 2» = -2000 := rfl
theorem «CFR 1.1031(d)-1 example 2_3» : recognizedGainLoss «CFR 1.1031(d)-1 example 2» = 0 := rfl

def «CFR 1.1031(d)-2».example1 : BaseLke' := 
  {
    outgoingOtherPropertyAb := []
    outgoingOtherPropertyFmv := []
    h_outgoing_other_property := by decide
    outgoingLkpAb := [500000]
    outgoingCash := ⟨0, by decide⟩ 
    outgoingLiabilities := ⟨150000, by decide⟩ 
    incomingLkpFmv :=  [600000]
    incomingOtherPropertyFmv := [] 
    incomingCash := ⟨50000, by decide⟩ 
    incomingLiabilities := ⟨0, by decide⟩ 
    toRelatedParty := false
    heldPrimarilyForSale := false
    isUsProperty := true
    h_is_us_property := rfl
    h_primarily_for_sale := rfl
    outgoingRelinquishedDate := Date.fromYmd 1954 9 1
    identificationDate := Date.fromYmd 1954 9 1
    incomingReceivedDate := Date.fromYmd 1954 9 1
    taxYearDueDate := Date.fromYmd 1955 4 15
    completionDate := Date.fromYmd 1954 9 1
    timingOk1 := by decide
    timingOk2 := by decide
    timingOk3 := by decide
  }

theorem «CFR 1.1031(d)-2».example1.a : realizedGainLoss   «CFR 1.1031(d)-2».example1 = 300000 := rfl
theorem «CFR 1.1031(d)-2».example1.b : recognizedGainLoss «CFR 1.1031(d)-2».example1 = 200000 := rfl
theorem «CFR 1.1031(d)-2».example1.c : basisIncomingLkp   «CFR 1.1031(d)-2».example1 = 500000 := rfl

/-
The outgoing LKP has an ab of 100k, subject to a mortgage of 80k.
The incoming property has a fmv of 250k, but is subject to a mortgage of 150k.
D gets 40k cash in the exchange.
-/
def «CFR 1.1031(d)-2».example2 : BaseLke' := 
  {
    outgoingOtherPropertyAb := []
    outgoingOtherPropertyFmv := []
    h_outgoing_other_property := by decide
    outgoingLkpAb := [100000]
    outgoingCash := ⟨0, by decide⟩ 
    outgoingLiabilities := ⟨80000, by decide⟩ 
    incomingLkpFmv :=  [250000]
    incomingOtherPropertyFmv := [] 
    incomingCash := ⟨40000, by decide⟩ 
    incomingLiabilities := ⟨150000, by decide⟩ 
    toRelatedParty := false
    heldPrimarilyForSale := false
    isUsProperty := true
    h_is_us_property := rfl
    h_primarily_for_sale := rfl
    outgoingRelinquishedDate := Date.fromYmd 1955 12 1
    identificationDate := Date.fromYmd 1955 12 1
    incomingReceivedDate := Date.fromYmd 1955 12 1
    taxYearDueDate := Date.fromYmd 1956 4 15
    completionDate := Date.fromYmd 1955 12 1
    timingOk1 := by decide
    timingOk2 := by decide
    timingOk3 := by decide
  }

lemma «CFR 1.1031(d)-2».example2_01 : incomingMoney «CFR 1.1031(d)-2».example2 = 40000 := rfl
lemma «CFR 1.1031(d)-2».example2_02 : outgoingMoney «CFR 1.1031(d)-2».example2 = 70000 := rfl

theorem «CFR 1.1031(d)-2».example2_1 : realizedGainLoss «CFR 1.1031(d)-2».example2 = 120000 := rfl
theorem «CFR 1.1031(d)-2».example2_2 : recognizedGainLoss «CFR 1.1031(d)-2».example2 = 40000 := rfl
theorem «CFR 1.1031(d)-2».example2_3 : basisIncomingLkp «CFR 1.1031(d)-2».example2 = 170000 := rfl

#eval IO.println (Explain.explain «CFR 1.1031(d)-2».example2.taxResult)
#eval («CFR 1.1031(d)-2».example2.taxResultM).run ""

end CfrExamples

def BaseLke'.tryFrom
  (outgoingLkpAb : List NonnegMoney)
  (outgoingOtherPropertyAb : List NonnegMoney)
  (outgoingOtherPropertyFmv : List NonnegMoney)
  (outgoingCash : NonnegMoney)
  (outgoingLiabilities : NonnegMoney)
  (incomingLkpFmv : List NonnegMoney)
  (incomingOtherPropertyFmv : List NonnegMoney)
  (incomingCash : NonnegMoney)
  (incomingLiabilities : NonnegMoney)
  (toRelatedParty : Bool)
  (heldPrimarilyForSale : Bool)
  (isUsProperty : Bool)
  (outgoingRelinquishedDate : Date)
  (identificationDate : Date)
  (incomingReceivedDate : Date)
  (taxYearDueDate : Date)
  (completionDate : Date)
  : Except String BaseLke' :=
  if timingOk1 : ¬completionDate <= outgoingRelinquishedDate + Duration.fromDays 180
  then Except.error "Exchange was not completed within 180 days of relinquishing outgoing property"
  else if timingOk2 : ¬identificationDate <= outgoingRelinquishedDate + Duration.fromDays 45
  then Except.error "Replacement property was not identified within 45 days"
  else if timingOk3 : ¬incomingReceivedDate <= min (outgoingRelinquishedDate + Duration.fromDays 180) taxYearDueDate 
  then Except.error "Replacement property was not received within the time allowed"
  else if h_is_us_property : ¬isUsProperty = true
  then Except.error "Like-kind exchange property must be located in the United States"
  else if h_primarily_for_sale : ¬heldPrimarilyForSale = false
  then Except.error "Property held primarily for sale cannot be used in a like-kind exchange"
  else if h_outgoing_other_property : ¬outgoingOtherPropertyAb.length = outgoingOtherPropertyFmv.length
  then Except.error "Validation error: outgoing property lists are of different lengths"
  else if h_due_date : ¬outgoingRelinquishedDate <= taxYearDueDate
  then Except.error "Validation error: tax year due date must be for the year in which the exchange takes place"
  else if h_num : ¬(incomingLkpFmv.length <= 3 ∨ sum incomingLkpFmv <= 2 * (sum outgoingLkpAb).val)
  then Except.error "3 properties or 200% rule was violated."
  else
    Except.ok $ {
      outgoingLkpAb := outgoingLkpAb
      outgoingCash := outgoingCash
      outgoingLiabilities := outgoingLiabilities
      incomingLkpFmv := incomingLkpFmv
      incomingOtherPropertyFmv := incomingOtherPropertyFmv
      incomingCash := incomingCash
      incomingLiabilities := incomingLiabilities
      toRelatedParty := toRelatedParty
      heldPrimarilyForSale := heldPrimarilyForSale
      isUsProperty := isUsProperty
      h_is_us_property := not_not.mp h_is_us_property
      h_primarily_for_sale := not_not.mp h_primarily_for_sale
      outgoingRelinquishedDate := outgoingRelinquishedDate
      identificationDate := identificationDate
      incomingReceivedDate := incomingReceivedDate
      taxYearDueDate := taxYearDueDate
      completionDate := completionDate
      h_due_date := not_not.mp h_due_date
      timingOk1 := not_not.mp timingOk1
      timingOk2 := not_not.mp timingOk2
      timingOk3 := not_not.mp timingOk3
      outgoingOtherPropertyAb := outgoingOtherPropertyAb
      outgoingOtherPropertyFmv := outgoingOtherPropertyFmv
      h_outgoing_other_property := not_not.mp h_outgoing_other_property
      h_num := not_not.mp h_num
    }
