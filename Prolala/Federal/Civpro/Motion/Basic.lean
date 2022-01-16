import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
import Prolala.Federal.Civpro.Motion.Defs
import Prolala.Federal.Civpro.Defs

open Time

def amendComplaintRequirements (st : Civpro.State) (newComplaint : Complaint) (courtApproval : Option String) : Prop :=
  (st.complaint.isSome) ∧ 
  (courtApproval.isSome
    ∨ st.status < Civpro.Status.answered
    ∨ match st.summons, st.date with
      | some s, some d => s.servedOn + Duration.fromDays 21 <= d
      | _, _ => False)

inductive Motion.Grant : Civpro.State → Motion → Civpro.State → Prop
| rule12
  (st : Civpro.State)
  (arguments : List Rule12)
  (withPrejudice : Bool)
  (h_ok : ∀ a ∈ arguments, a.favored ∨ (Civpro.Status.complaintFiled <= st.status ∧ st.status < Civpro.Status.answered) := by decide) :
    Grant st (Motion.rule12 arguments)
      { st with status := 
          if withPrejudice 
          then Civpro.Status.dismissedWithPrejudice 
          else Civpro.Status.dismissedWithoutPrejudice }
| amendComplaint
  (st : Civpro.State)
  (newComplaint : Complaint)
  (courtApproval : Option String)
  (h_old : st.complaint.isSome := by decide)
  (h_ok : amendComplaintRequirements st newComplaint courtApproval) :
    Grant st (Motion.amendComplaint newComplaint courtApproval)
      { st with complaint := some { 
        newComplaint with 
        filedOn := (Option.get h_old).filedOn, 
        caseNum := (Option.get h_old).caseNum }}
| amendSummons
  (st : Civpro.State)
  (newSummons : CompletedSummons)
  (courtApproval : String)
  (h_old : st.complaint.isSome := by decide) :
    Grant st (Motion.amendSummons newSummons courtApproval) { st with summons := some newSummons }

