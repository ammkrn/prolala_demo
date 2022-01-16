import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
import Prolala.Federal.Civpro.Pleading.Defs
import Prolala.Federal.Civpro.Pretrial.Defs
import Prolala.Federal.Civpro.Trial.Defs
import Prolala.Federal.Civpro.Appeal.Defs
import Prolala.Federal.Civpro.Enforcement.Defs
import Prolala.Federal.Civpro.Pleading.Basic
import Prolala.Federal.Civpro.Pretrial.Basic
import Prolala.Federal.Civpro.Trial.Basic
import Prolala.Federal.Civpro.Appeal.Basic
import Prolala.Federal.Civpro.Enforcement.Basic
import Prolala.Federal.Civpro.Motion.Defs
import Prolala.Federal.Civpro.Motion.Basic
import Prolala.Federal.Civpro.Defs

open Time

/-!
Civil procedure, implemented in a manner which closely resembles a big-step
operational semantics with a bunch of scalars along with composition/sequencing
(as in `A then B`). A single procedural step moves the state of the dispute
to a new state'. An inductive prop is used to dictate when steps are well-formed, 
meaning they can legally be taken. 
Inductive props by themselves present two problems; first, it's cumbersome to construct
well-formedness proofs, and second, you end up losing some information due to proof
irrelevance and the lack of large elimination. We can get around the first by making sure
everything is written such that the well-formedness of a given `state, step, state` triplet
is decidable; given a starting state and a step, we can also calculate the resulting state,
and determine whether it's well-formed. Having both functional and relational evaluation available 
is common for big-step operational semantics, but it's even easier in this case since everything
is well-founded (e.g. we have no `while`). To get around the second, each `Step` is in `Type`,
and is stored in order in `History`. By starting with the empty state and iteratively applying
each `Step`, we can reconstruct and play back the procedural history.
-/

/-- 
Procedural steps; these are bucketed into phases of the dispute
to prevent the growth of one giant unwieldy inductive.
-/
inductive Civpro.Step
| pleading : Pleading.Step → Step
| pretrial : Pretrial.Step → Step
| trial : Trial.Step → Step
| appeal : Appeal.Step → Step
| enforcement : Enforcement.Step → Step
| motion : Motion → Step
deriving Repr

/--
The procedural history of a dispute; `state` is the current (latest) state.
-/
structure Civpro.History where
  state : State
  stack : List Step

instance : EmptyCollection Civpro.History where
  emptyCollection := ⟨∅, ∅⟩

/-- 
Whether a given state, step, and post-state are well-formed.
-/
inductive Civpro.WfStep : State → Step → State → Prop
| pleading 
    (step : Pleading.Step) 
    (state state' : Civpro.State) 
    (h_status : state.status.pleadingOk)
    (h' : Pleading.WfStep state step state') : 
      WfStep state (Step.pleading step) state'
| pretrial
    (step : Pretrial.Step) 
    (state state' : Civpro.State) 
    (h_status : state.status.pretrialOk)
    (h' : Pretrial.WfStep state step state') : 
      WfStep state (Step.pretrial step) state'
| trial
    (step : Trial.Step) 
    (state state' : Civpro.State) 
    (h_status : state.status.trialOk)
    (h' : Trial.WfStep state step state') : 
      WfStep state (Step.trial step) state'
| appeal
    (step : Appeal.Step) 
    (state state' : Civpro.State) 
    (h_status : state.status.appealOk)
    (h' : Appeal.WfStep state step state') : 
      WfStep state (Step.appeal step) state'
| enforcement
    (step : Enforcement.Step) 
    (state state' : Civpro.State) 
    (h_status : state.status.enforcementOk)
    (h' : Enforcement.WfStep state step state') : 
      WfStep state (Step.enforcement step) state'
| fileMotion
    (st : Civpro.State)
    (m : Motion) 
    (h : ¬m ∈ st.pendingMotions) 
    (h_case : st.status > Status.complaintUnfiled) :
      WfStep st (Step.motion m) { st with pendingMotions := m :: st.pendingMotions }
| grantMotion
    (st st' : Civpro.State)
    (m : Motion) 
    (h_st : m ∈ st.pendingMotions)
    (h' : Motion.Grant st m st') :
      WfStep st (Step.motion m) 
        { st' with 
          pendingMotions := st.pendingMotions.erase m
          grantedMotions := m :: st.grantedMotions }
| dismissMotion
    (st : Civpro.State)
    (m : Motion) 
    (h : m ∈ st.pendingMotions) :
      WfStep st (Step.motion m) 
      { st with 
        pendingMotions := st.pendingMotions.erase m
        deniedMotions := m :: st.deniedMotions }

/--
Used to accumulate multiple transitions between state, step, state'.
The goal of moving this into a separate inductive instead of adding a 
`seq` step is to simplify proofs using `WfStep`; the exclusion of `seq`
means that nothing is recursive, so we should be able to discharge more
proof obligations just with tactics looking at individual cases.
-/
inductive Civpro.WfHistory: History → History → Prop
| push
  (tl : History)
  (nextStep : Civpro.Step)
  (st' : Civpro.State)
  (h_head : WfStep tl.state nextStep st') :
  WfHistory tl ⟨st', nextStep :: tl.stack⟩

/--
The procedural history is accessible from below under the well-formed relation.
-/
theorem Civpro.is_acc (x : History) : Acc WfHistory x := by
  apply Acc.intro
  intro y hh
  generalize hx : x = x'
  cases hh with
  | push _ nxt st' h_head => exact is_acc ⟨y.state, y.stack⟩
termination_by measure (fun ⟨st, stk⟩ => stk.length)
decreasing_by rw [<- hx]; exact Nat.lt_succ_self (List.length y.stack)

/--
Well-founded proof: All histories are accessible from below.
-/
theorem Civpro.WfHistory.is_well_founded : WellFounded WfHistory := ⟨Civpro.is_acc⟩

open Us.Federal

/-- 
A procedural history is "complete" if it's in the transitive closure of `WfHistory`
and it begins with the empty state. Using ReflTransGen on incomplete histories
is still a very useful concept, since the `refl` constructor of ReflTransGen is synthetic
and allows you to reason about procedural issues from any starting state, without having
to invent an whole fake procedural history. When we say synthetic, we just mean that the
underlying relation doesn't actually have to be reflexive (which it isn't in this case).
-/
def Civpro.History.isComplete (hist : History) := ReflTransGen WfHistory ∅ hist

/-- "A civil action is commenced by filing a complaint with the court."
    Stated as: If there's a well formed step that begins with the empty procedural state,
    then the step must be that of filing a complaint. -/
theorem Civpro.FRCP.«3» (step : Step) (st' : State) (hwf : WfStep ∅ step st') :
  ∃ complaint, step = Step.pleading (Pleading.Step.fileComplaint complaint) := by 
  generalize hstep : step = x
  cases hwf with
  | pleading _ _ _ _ hwf => 
    cases hwf with
    | fileComplaint c => exact Exists.intro c hstep.symm
    | requestServiceWaiver _ _ h_req => simp [State.emptyCollection.def, ServiceWaiverRequest.requirements] at h_req
    | waiveService _ _ h_req => simp [State.emptyCollection.def, ServiceWaiverResponse.requirements] at h_req
    | serveProcess _ _ h_req => simp [State.emptyCollection.def, CompletedSummons.requirements] at h_req
    | serveAnswer _ _ h_req => simp [State.emptyCollection.def, Answer.requirements] at h_req
    | defaultJudgment _ _ _ h_req => simp [State.emptyCollection.def] at h_req
  | pretrial _ _ _ h_ok h' => simp [State.emptyCollection.def] at h_ok
  | trial _ _ _ h_ok h' =>   simp [State.emptyCollection.def] at h_ok
  | appeal _ _ _ h_ok h' => simp [State.emptyCollection.def] at h_ok
  | enforcement _ _ _ h_ok h' => simp [State.emptyCollection.def] at h_ok
  | fileMotion _ _ _ h_case => simp [State.emptyCollection.def] at h_case
  | grantMotion _ _ _ h_mem => simp [State.emptyCollection.def] at h_mem
  | dismissMotion _ _ h_mem => simp [State.emptyCollection.def] at h_mem

section «4(a)(1)»  
variable (s : CompletedSummons) 

/- Miscellaneous parts of rule 4 which dictate the contents of a summons. -/

theorem FRCP.«4(a)(1)(A)» : Σ' x : (Court.DistrictCourt × Option String), s.court = x ∧ (s.complaint.court, s.complaint.courtDivision) = x := 
  ⟨s.court, ⟨rfl, rfl⟩⟩

theorem FRCP.«4(a)(1)(B)» : Σ' x, s.addressedTo = x ∧ x = s.complaint.defendant := ⟨s.addressedTo, ⟨rfl, rfl⟩⟩
theorem FRCP.«4(a)(1)(C)» : 
  Σ' (x : List String × List String), (s.plaintiffAttorneyNames, s.plaintiffAttorneyAddrs) = x 
  ∧ x = (s.complaint.plaintiffAttorneyInfo.map AttorneyInfo.name, s.complaint.plaintiffAttorneyInfo.map AttorneyInfo.address) := 
    ⟨(s.plaintiffAttorneyNames, s.plaintiffAttorneyAddrs), ⟨rfl, rfl⟩⟩

theorem FRCP.«4(a)(1)(D)» : Σ' w, s.appearanceWindow = w := ⟨s.appearanceWindow, rfl⟩ 
theorem FRCP.«4(a)(1)(E)» : Σ' w, s.defaultWarning = w := ⟨s.defaultWarning, rfl⟩
theorem FRCP.«4(a)(1)(F)» : Σ' b, b = s.hasClerkSignature ∧ b = true := ⟨s.hasClerkSignature, ⟨rfl, s.h_sig⟩⟩
theorem FRCP.«4(a)(1)(G)» : Σ' b, b = s.hasCourtSeal ∧ b = true := ⟨s.hasCourtSeal, ⟨rfl, s.h_seal⟩⟩
end «4(a)(1)»  
