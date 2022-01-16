import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.Data.Int.Order
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Basic
import Prolala.Time
import Prolala.Federal.Tax.Lke.Basic
import Prolala.Federal.Tax.Util
import Prolala.Util

/-!
Implementation of sections 1 and 3, and proof of correspondence for section 3 of IRS 
form 8824 (2021 edition: OMB No. 1545-1190).

Section 2 just gets factual information about related-party exchanges, and section 4
deals with conflict-of-interest transactions for federal government officials and 
judicial officers.
-/
open Time Property PropertyTxn 

structure Form8824.Part1 extends BaseLke where
  outgoingLkpDescription : String
  incomingLkpDescription : String
  outgoingLkpAcquiredDate : Date
deriving Repr

section Part1
variable (form : Form8824.Part1)
abbrev Form8824.line1 := form.outgoingLkpDescription
abbrev Form8824.line2 := form.incomingLkpDescription
abbrev Form8824.line3 := form.outgoingLkpAcquiredDate
abbrev Form8824.line4 := form.outgoingRelinquishedDate
abbrev Form8824.line5 := form.identificationDate
abbrev Form8824.line6 := form.incomingReceivedDate
abbrev Form8824.line7 := form.toRelatedParty
end Part1

structure Form8824.Part3 extends BaseLke where
  transactionCostsIncurred : NonnegMoney
  recapture1245 : NonnegMoney 
  recapture1250 : NonnegMoney
deriving Repr
namespace Form8824.Part3

variable (form : Form8824.Part3)

/- 12, 13, and 14 treat outgoing non-lkp as a separate transaction, which is just a sale. -/
abbrev line12 := sum form.incomingOtherPropertyFmv
abbrev line13 := sum form.outgoingOtherPropertyAb
@[reducible] def line14 := form.line12.val - form.line13

@[simp] def line15 := max 0 (form.incomingBoot - form.transactionCostsIncurred)

def remainderTransactionCosts : Int := 
  if form.transactionCostsIncurred <= form.incomingBoot 
  then 0 
  else Int.natAbs <| form.transactionCostsIncurred - form.incomingBoot

@[simp] def line16 := sum form.incomingLkpFmv

@[simp] def line17 := form.line16 + form.line15

@[simp] theorem line_17_eq (h : form.transactionCostsIncurred = 0) : form.line17 = amtRealized form.toBaseLke := by
 simp [amtRealized, h, max_eq_right form.incoming_boot_nonneg]

@[reducible, simp] def line18 := sum form.outgoingLkpAb + form.outgoingMoney + form.remainderTransactionCosts

@[reducible, simp] def line19 := form.line17 - form.line18

@[reducible, simp] def line20 := max 0 <| min form.line15 form.line19

@[reducible, simp] def line21 :=  form.recapture1245.val + form.recapture1250

@[reducible, simp] def line22 :=  max 0 <| form.line20 - form.line21

@[reducible, simp] def line23 :=  form.line21 + form.line22

@[reducible, simp] def line24 :=  form.line19 - form.line23

@[reducible, simp] def line25 :=  form.line18 + form.line23 - form.line15

abbrev outgoingNonLkpGainLoss:= line14
abbrev amtRealized := line17
abbrev adjustedBasis := line18
abbrev realizedGainLoss := line19
abbrev recognizedGainLoss :=  line23
abbrev deferredGainLoss :=  line24
abbrev basisIncomingLkp := line25

def fromBase (b : BaseLke) : Form8824.Part3 := 
  { b with transactionCostsIncurred := 0, recapture1245 := 0, recapture1250 := 0 }

instance : PropertyTxn Form8824.Part3 where
  adjustedBasis := Form8824.Part3.adjustedBasis
  amtRealized := Form8824.Part3.amtRealized
  realizedGainLoss := Form8824.Part3.realizedGainLoss

def taxResult : LkeResult :=
  {
    completionDate := form.completionDate
    recognizedGainLoss := by
      refine Subtype.mk form.recognizedGainLoss ?p
      simp [recognizedGainLoss]
      apply Int.add_nonneg
      exact Int.add_nonneg form.recapture1245.property form.recapture1250.property
      exact le_max_left 0 _
    deferredGainLoss := form.deferredGainLoss
    basisIncomingLkp := form.basisIncomingLkp
    basisIncomingBootProperty := form.basisIncomingBootProperty
    relatedPartySunsetDate := 
      if form.toRelatedParty 
      then some <| form.completionDate + Duration.fromYears 2
      else none
    source := ⟨Administrative.miscGuidance AdministrativeBody.irs, by decide⟩
  }
  
section Correspondence

/- 
Show that modulo transaction costs and recapture, which are not covered in the relevant
USC/CFR sections, the worksheet provides results which are compliant with the covered/major 
provisions of 26 USC 1031 and 26 CFR 1.1031 w.r.t. recognized gain/loss, deferred gain/loss, 
and basis in LKP if there's no additional (non-like-kind) property being exchanged. 
The worksheet actually delivers non-conforming results for the new basis, which is dealt 
with as well.
-/

variable 
  (h0 : form.recapture1245 = 0)
  (h1 : form.recapture1250 = 0)
  (h2 : form.transactionCostsIncurred = 0)

/- Section-specific lemma -/
@[simp] lemma txn_costs_zero : form.remainderTransactionCosts = 0 := by
  simp [remainderTransactionCosts, h2, form.incoming_boot_nonneg]

/-
Form 8824 and the USC/CFR calculate the same recognized gain/loss.
-/
theorem recognized_gain_loss_eq_mod_unique : form.recognizedGainLoss = form.toBaseLke.recognizedGainLoss := by
  simp [
    recognizedGainLoss, BaseLke.recognizedGainLoss, h0, h1, h2,
    PropertyTxn.realizedGainLoss, max_eq_right form.incoming_boot_nonneg
  ]

/-
Form 8824 and the USC/CFR calculate the same deferred gain/loss.
-/
theorem deferred_gain_loss_eq_mod_unique : form.deferredGainLoss = form.toBaseLke.deferredGainLoss := by
  have h3 : max 0 (BaseLke.incomingBoot form.toBaseLke) = form.toBaseLke.incomingBoot := max_eq_right form.incoming_boot_nonneg
  simp [deferredGainLoss, h0, h1, h2, BaseLke.deferredGainLoss, BaseLke.recognizedGainLoss, PropertyTxn.realizedGainLoss, h3]

/-
The basis in the incoming like-kind property is the same if there's no
"extra" outgoing property (not like-kind property) involved in the exchange.
In that case, the form 8824 rules and the CFR rules give different results.
See `basis_in_lkp_ne` for a proof.
-/
theorem basis_in_lkp_no_property_eq_mod_unique (h3 : form.outgoingOtherPropertyAb.isEmpty) : 
  form.basisIncomingLkp = form.toBaseLke.basisIncomingLkp := by
    simp [basisIncomingLkp, BaseLke.basisIncomingLkp]
    rw [total_basis_incoming_empty form.toBaseLke h3]
    simp [h0, h1, h2, txn_costs_zero, max_eq_right form.incoming_boot_nonneg]
    simp [
      BaseLke.totalBasisIncoming, BaseLke.incomingBoot, BaseLke.recognizedGainLoss, 
      Property.adjustedBasis, PropertyTxn.realizedGainLoss, PropertyTxn.amtRealized,
      sub_add_eq_sub_sub, sub_add_eq_add_sub, sub_comm_right
    ]

/--
Uses a counter-example to show that in some cases, the basis in incoming property 
calculated by form 8824 is different from the basis calculated by the rules dictated in
the CFR. Specifically, this is the case when there is "other" property involved in 
the transaction (like outgoing stock).
-/
theorem basis_in_lkp_ne : ¬∀ (form : Form8824.Part3), form.basisIncomingLkp = form.toBaseLke.basisIncomingLkp :=
  let counterexample := fromBase CfrExamples.«CFR 1.1031(d)-1 example 2» 
  not_forall_of_exists_not <| Exists.intro counterexample (fun h => absurd h (by simp))

/-- 
This difference between the worksheet and the USC/CFR holds for larger hypothetical values of 
e.g. 1250 recapture, and even if there are transaction costs. 
-/
theorem basis_in_lkp_ne' : ∃ (form : Form8824.Part3), ¬form.basisIncomingLkp = form.toBaseLke.basisIncomingLkp :=
  let counterexample := { 
    CfrExamples.«CFR 1.1031(d)-1 example 2» 
    with 
    transactionCostsIncurred := 800
    recapture1245 := 0
    recapture1250 := 10000
  }
  Exists.intro counterexample (fun h => absurd h (by simp))

end Correspondence
end Form8824.Part3

def LkeResults (b : BaseLke) : List LkeResult := [(Form8824.Part3.fromBase b).taxResult, b.taxResult]

#eval (LkeResults CfrExamples.«CFR 1.1031(d)-1 example 2»).qsortBy (fun r => r.source.val)

