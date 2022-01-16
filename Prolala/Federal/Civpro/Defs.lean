import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
import Prolala.Federal.Civpro.Pleading.Defs
import Prolala.Federal.Civpro.Pretrial.Defs
import Prolala.Federal.Civpro.Trial.Defs
import Prolala.Federal.Civpro.Appeal.Defs
import Prolala.Federal.Civpro.Enforcement.Defs
import Prolala.Federal.Civpro.Motion.Defs

open Time

/--
The status of the dispute. Some procedural maneuvers are limited to specific
stages of a dispute, or move the dispute between stages.
-/
inductive Civpro.Status
| complaintUnfiled
| complaintFiled 
| serviceWaiverSent
| servedOrWaived
| answered
| pleadingsClosed
| pretrialClosed
| finalJudgmentEntered
| appealClosed
| enforcementComplete
| dismissedWithoutPrejudice
| dismissedWithPrejudice
--| transferred
| settled
deriving Repr, DecidableEq, Ord

instance : LE Civpro.Status := leOfOrd
instance : LT Civpro.Status := ltOfOrd
instance (t₁ t₂ : Civpro.Status) : Decidable (t₁ <= t₂) := inferInstance
instance (t₁ t₂ : Civpro.Status) : Decidable (t₁ < t₂) := inferInstance

abbrev Civpro.Status.pleadingOk (s : Status) := s < pleadingsClosed
abbrev Civpro.Status.pretrialOk (s : Status) := pleadingsClosed <= s ∧ s < pretrialClosed
abbrev Civpro.Status.trialOk (s : Status) := pretrialClosed <= s ∧ s < finalJudgmentEntered
abbrev Civpro.Status.appealOk (s : Status) := finalJudgmentEntered <= s ∧ s < appealClosed
abbrev Civpro.Status.enforcementOk (s : Status) := finalJudgmentEntered <= s ∧ s < enforcementComplete

/-
An incomplete representation of the state of a civil action. As the proceeding
continues, the `Option _` fields are populated. When making use of `State` elsewhere,
appropriate invariants are enforced using proofs/hypotheses. For example, the procedural
step of sending a request to waive service cannot be taken unless a proof
is provided which shows that the `complaint` field is populated, and the status of the
proceeding is appropriate to allow such a request to be sent.
-/
structure Civpro.State where
  status : Status
  date : Option Date
  complaint : Option FiledComplaint
  summons : Option CompletedSummons
  serviceWaiver : Option ServiceWaiverResponse
  answer : Option Answer
  deadlines : List (String × Date)
  pendingMotions : List Motion
  grantedMotions : List Motion
  deniedMotions : List Motion
deriving Repr, DecidableEq

instance : EmptyCollection Civpro.State where
  emptyCollection := ⟨Civpro.Status.complaintUnfiled, none, none, none, none, none, [], [], [], []⟩ 

theorem Civpro.State.emptyCollection.def : 
  (∅ : Civpro.State) = ⟨Status.complaintUnfiled, none, none, none, none, none, [], [], [], []⟩ := rfl

