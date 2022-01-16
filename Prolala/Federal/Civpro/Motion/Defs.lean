import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
import Prolala.Federal.Civpro.Pleading.Defs

open Time

inductive Rule12 where
| lackOfSubjectMatterJurisdiction
| lackOfPersonalJurisdiction
| improperVenue
| insufficientProcess
| insufficientService
| failureToStateAClaim
| failureToJoinUnderRule19
deriving DecidableEq, Repr

/- The "favored defenses" of rule 12. -/
def Rule12.favored : Rule12 → Prop
| Rule12.lackOfSubjectMatterJurisdiction => True
| Rule12.failureToStateAClaim => True
| Rule12.failureToJoinUnderRule19 => True
| _ => False

instance : ∀ (m : Rule12), Decidable m.favored
| Rule12.lackOfSubjectMatterJurisdiction => isTrue trivial
| Rule12.lackOfPersonalJurisdiction => isFalse False.elim
| Rule12.improperVenue => isFalse False.elim
| Rule12.insufficientProcess => isFalse False.elim
| Rule12.insufficientService => isFalse False.elim
| Rule12.failureToStateAClaim => isTrue trivial
| Rule12.failureToJoinUnderRule19 => isTrue trivial

inductive Motion 
| rule12 : List Rule12 → Motion
| amendComplaint (newComplaint : Complaint) (courtApproval : Option String) : Motion 
| amendSummons (summons : CompletedSummons) (courtApproval : String) : Motion
| summaryJudgment (contents : String) : Motion
deriving DecidableEq, Repr

