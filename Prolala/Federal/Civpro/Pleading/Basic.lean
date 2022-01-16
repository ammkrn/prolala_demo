import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
import Prolala.Federal.Civpro.Pleading.Defs
import Prolala.Federal.Civpro.Defs

open Time Us.Federal

inductive Pleading.Step
| fileComplaint (c : FiledComplaint) : Step
| requestServiceWaiver (req : ServiceWaiverRequest) : Step
| waiveService (w : ServiceWaiverResponse) : Step
| serveProcess (s : CompletedSummons) : Step
| serveAnswer (a : Answer) : Step
| enterDefaultJudgment (date : Date) (explanation : String) : Step
deriving DecidableEq, Repr

section Requirements

variable (st : Civpro.State)

/-- 
To send a waiver request, there must be a filed complaint in an ongoing dispute,
and the defendant must not have already been served or returned a waiver.
-/
@[reducible]
def ServiceWaiverRequest.requirements (req : ServiceWaiverRequest) :=
  some req.complaint = st.complaint
  ∧ (Civpro.Status.complaintFiled <= st.status ∧ st.status <= Civpro.Status.servedOrWaived)

/--
For a defendant to waive service, they must not have already been served.
The timeliness requirement for returning the waiver is handled by the `ServiceWaiverResponse`
type, which cannot be constructed unless it's constructed in a timely manner, since the
form itself references the date on which it's being returned.
-/
@[reducible]
def ServiceWaiverResponse.requirements (w : ServiceWaiverResponse) := 
  st.summons.isNone
  ∧ (Civpro.Status.serviceWaiverSent <= st.status ∧ st.status <= Civpro.Status.servedOrWaived)

/-
Reflecting service of process requires proof that the defendant has not waived service,
and that there is a filed complaint. 
-/
@[reducible]
def CompletedSummons.requirements (s : CompletedSummons) :=
  st.serviceWaiver.isNone 
  ∧ (some s.complaint = st.complaint) 
  ∧ st.status >= Civpro.Status.complaintFiled

/-
To file an answer, one must show that an answer has not already been served
(if it has, you can amend by motion), and that process has been served or waived.
-/
@[reducible]
def Answer.requirements (a : Answer) :=
  Civpro.Status.servedOrWaived <= st.status ∧ st.status <= Civpro.Status.answered

/-
To effect a default judgment, there must be an ongoing dispute stemming from
a filed complaint.
-/
@[reducible]
def DefaultJudgment.requirements := Civpro.Status.complaintFiled <= st.status

end Requirements

section WfStepSection

inductive Pleading.WfStep : Civpro.State -> Pleading.Step -> Civpro.State -> Prop
| fileComplaint (complaint : FiledComplaint) : 
    WfStep (∅ : Civpro.State) (Pleading.Step.fileComplaint complaint) 
      { (∅ : Civpro.State) with 
        date := complaint.filedOn
        complaint
        status := Civpro.Status.complaintFiled }
| requestServiceWaiver (st : Civpro.State) (req : ServiceWaiverRequest)  (h : req.requirements st := by decide) :
    WfStep st (Pleading.Step.requestServiceWaiver req) { st with date := req.date }
| waiveService (st : Civpro.State) (response : ServiceWaiverResponse) (h : response.requirements st := by decide) :
    WfStep st (Pleading.Step.waiveService response) 
      { st with 
        date := some response.date
        serviceWaiver := response
        status := Civpro.Status.servedOrWaived }
| serveProcess (st : Civpro.State) (s : CompletedSummons) (h : s.requirements st := by decide) :
    WfStep st (Pleading.Step.serveProcess s) { st with date := s.servedOn, summons := s }
| serveAnswer (st : Civpro.State) (a : Answer) (h : a.requirements st := by decide) :
    WfStep st (Pleading.Step.serveAnswer a) { st with date := a.servedOn, answer := a }
| defaultJudgment (st : Civpro.State) (d : Date) (judgment : String) (h : DefaultJudgment.requirements st := by decide) :
    WfStep st (Pleading.Step.enterDefaultJudgment d judgment) 
      { st with 
        date := d 
        status := Civpro.Status.finalJudgmentEntered }

/--
Whether a given step is well-formed is decidble.
-/
instance (st st' : Civpro.State) (step : Pleading.Step) : Decidable <| Pleading.WfStep st step st' :=
  match h:step with
  | Pleading.Step.fileComplaint c =>
    if h0 : st = ∅ ∧ st' = { st with date := c.filedOn, complaint := c, status := Civpro.Status.complaintFiled  }
    then isTrue <| h0.right ▸ h0.left ▸ (Pleading.WfStep.fileComplaint c)
    else isFalse <| fun hf => by
      cases hf with
      | fileComplaint _ => 
        match Decidable.not_and_imp_nor h0 with
        | Or.inl hl => exact absurd rfl hl
        | Or.inr hr => simp at hr
  | Pleading.Step.requestServiceWaiver req => 
    if h0 : req.requirements st ∧ st' = { st with date := req.date }
    then isTrue <| h0.right ▸ (Pleading.WfStep.requestServiceWaiver st req h0.left)
    else isFalse fun hf => by
      cases hf with
      | requestServiceWaiver st _ h_req =>
        match Decidable.not_and_imp_nor h0 with
        | Or.inl hl => exact absurd h_req hl
        | Or.inr hr => simp at hr
  | Pleading.Step.serveProcess s => 
    if h0 : s.requirements st ∧ st' = { st with date := s.servedOn, summons := s }
    then isTrue <| h0.right ▸ (Pleading.WfStep.serveProcess st s h0.left)
    else isFalse fun hf => by
      cases hf with
      | serveProcess h_st h_s h_req =>
        match Decidable.not_and_imp_nor h0 with
        | Or.inl hl => exact absurd h_req hl
        | Or.inr hr => simp at hr

  | Pleading.Step.waiveService w => 
    if h0 : w.requirements st ∧ (st' = { st with date := some w.date, serviceWaiver := w, status := Civpro.Status.servedOrWaived })
    then isTrue <| h0.right ▸ (Pleading.WfStep.waiveService st w h0.left)
    else isFalse fun hf => by
      cases hf with
      | waiveService st w h_req =>
        match Decidable.not_and_imp_nor h0 with
        | Or.inl hl => exact absurd h_req hl
        | Or.inr hr => simp at hr
  | Pleading.Step.serveAnswer ans => 
    if h0 : ans.requirements st ∧ st' = { st with date := ans.servedOn, answer := ans }
    then isTrue <| h0.right ▸ (Pleading.WfStep.serveAnswer st ans h0.left)
    else isFalse fun hf => by
      cases hf with
      | serveAnswer st a h_status =>
        match Decidable.not_and_imp_nor h0 with
        | Or.inl hl => exact absurd h_status hl
        | Or.inr hr => simp at hr
  | Pleading.Step.enterDefaultJudgment date explanation => 
    if h0 : DefaultJudgment.requirements st ∧ st' = { st with date := date, status := Civpro.Status.finalJudgmentEntered }
    then isTrue <| h0.right ▸ (Pleading.WfStep.defaultJudgment st date explanation h0.left)
    else isFalse fun hf => by
      cases hf with
      | defaultJudgment st d j h_status =>
        match Decidable.not_and_imp_nor h0 with
        | Or.inl hl => exact absurd h_status hl
        | Or.inr hr => simp at hr

/--
Given a starting state and a step, we can compute the resulting state and provide
it along with a proof that it is well-formed, or we can return an error if it is not
well-formed.

The error messages are currently very lazy.
-/
def Pleading.evalStep (st : Civpro.State) : ∀ (step : Pleading.Step), Except String { st' : Civpro.State // Pleading.WfStep st step st' }
| Step.fileComplaint c => 
  if h0 : ∅ = st 
  then Except.ok ⟨{ st with date := c.filedOn, complaint := c, status := Civpro.Status.complaintFiled }, h0 ▸ (Pleading.WfStep.fileComplaint c)⟩ 
  else Except.error "Error evaluating evalStep fileComplaint. Initial state was not empty."
| Step.requestServiceWaiver req =>
  if h0 : req.requirements st
  then Except.ok ⟨{ st with date := req.date }, Pleading.WfStep.requestServiceWaiver st req h0⟩
  else Except.error "cannot request service waiver"
| Step.waiveService w => 
  if h0 : w.requirements st
  then Except.ok  
      ⟨{ st with 
        date := some w.date
        serviceWaiver := w
        status := Civpro.Status.servedOrWaived }, Pleading.WfStep.waiveService st w h0⟩ 
  else Except.error "cannot waive service"
| Step.serveProcess s => 
  if h0 : s.requirements st
  then Except.ok ⟨{ st with date := s.servedOn, summons := s }, Pleading.WfStep.serveProcess st s h0⟩
  else Except.error "cannot serve process"
| Step.serveAnswer a => 
  if h0 : a.requirements st
  then Except.ok ⟨{ st with date := a.servedOn, answer := a }, Pleading.WfStep.serveAnswer st a h0⟩ 
  else Except.error "cannot serve answer"
| Step.enterDefaultJudgment date explanation => 
  if h0 : DefaultJudgment.requirements st
  then Except.ok 
    ⟨{ st with 
       date := date
       status := Civpro.Status.finalJudgmentEntered }, Pleading.WfStep.defaultJudgment st date explanation h0⟩ 
  else Except.error "cannot enter default judgment"


end WfStepSection
