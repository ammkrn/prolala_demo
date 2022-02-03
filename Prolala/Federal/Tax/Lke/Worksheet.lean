import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.Data.Int.Order
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Basic
import Prolala.Time
import Prolala.Federal.Tax.Util
import Prolala.Util

open Time Property PropertyTxn 

structure BaseLke where
  /-- TP's adjusted basis in outgoing like-kind property -/
  outgoingLkpAb : NonnegMoney
  /-- TP's adjusted basis in elements out outgoing non-LKP -/
  outgoingOtherPropertyAdjustedBasis : List NonnegMoney
  /-- The fair market values of elements out outgoing non-LKP -/
  outgoingOtherPropertyFmv : List NonnegMoney
  /-- The total amount of outgoing cash -/
  outgoingCash : NonnegMoney
  /-- The sum of any libilities being assumed by the other party -/
  outgoingLiabilities : NonnegMoney
  /-- The fair market values of incoming property that is of like-kind -/
  incomingLkpFmv : NonnegMoney
  /-- The fair market values of incoming property that is not of like-kind -/
  incomingOtherPropertyFmv : List NonnegMoney
  /-- The sum of any incoming cash -/
  incomingCash : NonnegMoney
  /-- The sum of any liabilties being assumed by the taxpayer -/
  incomingLiabilities : NonnegMoney
  /- Both sides can have liabilities though -/
  hCash : incomingCash = 0 ∨ outgoingCash = 0
  -- If there are net outgoing liabiltiies, the taxpayer cannot be receiving any money
  h_outgoing_liabilities : max 0 (outgoingLiabilities.val - (incomingLiabilities + outgoingCash + sum outgoingOtherPropertyFmv)) > 0 -> incomingCash = 0 := by decide
  -- if there are net incoming liabilities... Then I shouldn't be able to give cash.
  h_incoming_liabilities : (max 0 <| incomingLiabilities.val - outgoingLiabilities.val) > 0 -> outgoingCash = 0 := by decide
  hOtherProperty : incomingOtherPropertyFmv.isEmpty ∨ outgoingOtherPropertyFmv.isEmpty
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
  h_outgoing_other_property : outgoingOtherPropertyAdjustedBasis.length = outgoingOtherPropertyFmv.length := by decide
deriving Repr


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

def netOutgoingLiabilities := max 0 (form.outgoingLiabilities.val - (form.incomingLiabilities + form.outgoingCash + sum form.outgoingOtherPropertyFmv))

/- 12, 13, and 14 treat outgoing non-lkp as a separate transaction, which is just a sale. -/
@[simp] abbrev line12 := sum form.outgoingOtherPropertyFmv
@[simp] abbrev line13 := sum form.outgoingOtherPropertyAdjustedBasis
@[reducible, simp] def line14 := form.line12.val - form.line13

/-
Cash received, FMV of other property received, plus net liabilities assumed by other party, reduced
(but not below zero) by any exchange expenses you incurred. See instruction
-/
@[simp] def line15 := 
  max 0 ((form.incomingCash.val + sum form.incomingOtherPropertyFmv + form.netOutgoingLiabilities) - form.transactionCostsIncurred)

def remainderTransactionCosts : Int := 
  if form.transactionCostsIncurred <= (form.incomingCash.val + sum form.incomingOtherPropertyFmv + form.netOutgoingLiabilities)
  then 0 
  else Int.natAbs <| form.transactionCostsIncurred - (form.incomingCash.val + sum form.incomingOtherPropertyFmv + form.netOutgoingLiabilities)

/- 16 FMV of like-kind property you received -/
@[simp] def line16 := form.incomingLkpFmv

/- 17 Add lines 15 and 16  -/
@[simp] def line17 := form.line15 + form.line16

/-
18 Adjusted basis of like-kind property you gave up, net 
amounts paid to other party, plus any exchange
expenses not used on line 15. See instructions
Include on line 18 the sum of:
• The adjusted basis of the like-kind real
property you gave up;
• Exchange expenses, if any (except for
expenses used to reduce the amount
reported on line 15); and
• The net amount paid to the other
party—the excess, if any, of the total of (a)
any liabilities you assumed, (b) cash you
paid to the other party, and (c) the FMV of
the other (not like-kind) property you gave up
over any liabilities assumed by the other
party
-/
@[reducible, simp] def line18 := 
  form.outgoingLkpAb
  + form.remainderTransactionCosts 
  + (max 0 ((form.incomingLiabilities + form.outgoingCash + sum form.outgoingOtherPropertyFmv) - form.outgoingLiabilities.val))

/- 19 Realized gain or (loss). Subtract line 18 from line 17 -/
@[reducible, simp] def line19 := form.line17 - form.line18

/- 20 Enter the smaller of line 15 or line 19, but not less than zero  -/
@[reducible, simp] def line20 := max 0 (min form.line15 form.line19)

@[reducible, simp] def line21 :=  form.recapture1245.val + form.recapture1250

/-
22 Subtract line 21 from line 20. If zero or less, enter -0-. If more than zero, 
enter here and on Schedule D or Form 4797, unless the installment method applies.
-/
@[reducible, simp] def line22 :=  max 0 (form.line20 - form.line21)

/- 23 Recognized gain. Add lines 21 and 2 -/
@[reducible, simp] def line23 :=  form.line21 + form.line22

/- 4 Deferred gain or (loss). Subtract line 23 from line 19. If a related party exchange -/
@[reducible, simp] def line24 :=  form.line19 - form.line23


/- Basis of like-kind property received. Subtract line 15 from the sum of lines 18 and 23. -/
@[reducible, simp] def line25 :=  (form.line18 + form.line23) - form.line15

abbrev outgoingOtherPropertyRecognizedGainLoss := line14
abbrev incomingBoot := line15
abbrev amtRealized := line17
abbrev adjustedBasis := line18
abbrev realizedGainLoss := line19
abbrev lkpRecognizedGainLoss :=  line23
abbrev deferredGainLoss :=  line24
abbrev basisIncomingLkp := line25
abbrev basisIncomingOtherProperty := sum form.incomingOtherPropertyFmv
abbrev totalRecognizedGainLoss := form.lkpRecognizedGainLoss + form.outgoingOtherPropertyRecognizedGainLoss

def fromBase (b : BaseLke) : Form8824.Part3 := 
  { b with transactionCostsIncurred := 0, recapture1245 := 0, recapture1250 := 0 }

instance : PropertyTxn Form8824.Part3 where
  adjustedBasis := Form8824.Part3.adjustedBasis
  amtRealized := Form8824.Part3.amtRealized
  realizedGainLoss := Form8824.Part3.realizedGainLoss

 def example0 : Form8824.Part3 := 
  {
    hCash := by decide
    hOtherProperty := by decide
    transactionCostsIncurred := 0
    recapture1245 := 0
    recapture1250 := 0
    outgoingLkpAb := 100000
    outgoingOtherPropertyAdjustedBasis := []
    h_outgoing_other_property := by decide
    outgoingOtherPropertyFmv := []
    outgoingCash := ⟨0, by decide⟩ 
    outgoingLiabilities := ⟨0, by decide⟩ 
    incomingLkpFmv :=  80000
    incomingOtherPropertyFmv := [0] 
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

def example18AtoB : Form8824.Part3 := 
  {
    hCash := by decide
    hOtherProperty := by decide
    transactionCostsIncurred := 0
    recapture1245 := 0
    recapture1250 := 0
    outgoingLkpAb := 100000
    outgoingOtherPropertyAdjustedBasis := []
    h_outgoing_other_property := by decide
    outgoingOtherPropertyFmv := []
    outgoingCash := ⟨0, by decide⟩ 
    outgoingLiabilities := ⟨80000, by decide⟩ 
    incomingLkpFmv :=  250000
    incomingOtherPropertyFmv := [] 
    incomingCash := ⟨40000, by decide⟩ 
    incomingLiabilities := ⟨150000, by decide⟩ 
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

example : example18AtoB.line15 = 40000 := rfl
example : example18AtoB.line16 = 250000 := rfl
example : example18AtoB.line17 = 290000 := rfl
example : example18AtoB.line18 = 170000 := rfl
example : example18AtoB.line19 = 120000 := rfl

def example18BtoA : Form8824.Part3 := 
  {
    hCash := by decide
    hOtherProperty := by decide
    transactionCostsIncurred := 0
    recapture1245 := 0
    recapture1250 := 0
    outgoingLkpAb := 175000
    outgoingOtherPropertyAdjustedBasis := []
    h_outgoing_other_property := by decide
    outgoingOtherPropertyFmv := []
    outgoingCash := ⟨40000, by decide⟩ 
    outgoingLiabilities := ⟨150000, by decide⟩ 
    incomingLkpFmv :=  220000
    incomingOtherPropertyFmv := [] 
    incomingCash := ⟨0, by decide⟩ 
    incomingLiabilities := ⟨80000, by decide⟩ 
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

example : example18BtoA.line15 = 30000 := rfl
example : example18BtoA.line16 = 220000 := rfl
example : example18BtoA.line17 = 250000 := rfl
example : example18BtoA.line18 = 175000 := rfl
example : example18BtoA.line19 = 75000 := rfl

def stockExample : Form8824.Part3 := 
  {
    hCash := by decide
    hOtherProperty := by decide
    transactionCostsIncurred := 0
    recapture1245 := 0
    recapture1250 := 0
    outgoingLkpAb := 10000
    outgoingOtherPropertyAdjustedBasis := [4000]
    h_outgoing_other_property := by decide
    outgoingOtherPropertyFmv := [2000]
    outgoingCash := ⟨0, by decide⟩ 
    outgoingLiabilities := ⟨0, by decide⟩ 
    incomingLkpFmv :=  13000
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

example : stockExample.lkpRecognizedGainLoss = 0 := rfl
example : stockExample.line12 = 2000 := rfl
example : stockExample.line13 = 4000 := rfl
example : stockExample.line14 = -2000 := rfl
example : stockExample.deferredGainLoss = 1000 := rfl
example : stockExample.basisIncomingLkp = 12000 := rfl

def stockExample2 : Form8824.Part3 := 
  {
    hCash := by decide
    hOtherProperty := by decide
    transactionCostsIncurred := 0
    recapture1245 := 0
    recapture1250 := 0
    outgoingLkpAb := 10000
    outgoingOtherPropertyAdjustedBasis := []
    h_outgoing_other_property := by decide
    outgoingOtherPropertyFmv := []
    outgoingCash := ⟨5000, by decide⟩ 
    outgoingLiabilities := ⟨0, by decide⟩ 
    incomingLkpFmv :=  15000
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

def stockExample3 : Form8824.Part3 := 
  {
    hCash := by decide
    hOtherProperty := by decide
    transactionCostsIncurred := 0
    recapture1245 := 0
    recapture1250 := 0
    outgoingLkpAb := 10000
    outgoingOtherPropertyAdjustedBasis := []
    h_outgoing_other_property := by decide
    outgoingOtherPropertyFmv := []
    outgoingCash := ⟨0, by decide⟩ 
    outgoingLiabilities := ⟨0, by decide⟩ 
    incomingLkpFmv :=  8000
    incomingOtherPropertyFmv := [] 
    incomingCash := ⟨2000, by decide⟩ 
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

def «CFR 1.1031(d)-1 example 2» : Form8824.Part3 := 
  {
    hCash := by decide
    hOtherProperty := by decide
    transactionCostsIncurred := 0
    recapture1245 := 0
    recapture1250 := 0
    outgoingLkpAb := 10000
    outgoingOtherPropertyAdjustedBasis := [4000]
    h_outgoing_other_property := by decide
    outgoingOtherPropertyFmv := [2000]
    outgoingCash := ⟨0, by decide⟩ 
    outgoingLiabilities := ⟨0, by decide⟩ 
    incomingLkpFmv :=  13000
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
theorem «CFR 1.1031(d)-1 example 2_2» : line14 «CFR 1.1031(d)-1 example 2» = -2000 := rfl
theorem «CFR 1.1031(d)-1 example 2_3» : lkpRecognizedGainLoss «CFR 1.1031(d)-1 example 2» = 0 := rfl
/- 
At this point, they're getting a FMV 11000 property for an adjustedBasis 
10000 property, so there's a $1000 deferred gain. 
-/
theorem «CFR 1.1031(d)-1 example 2_0» : deferredGainLoss «CFR 1.1031(d)-1 example 2» = 1000 := rfl
