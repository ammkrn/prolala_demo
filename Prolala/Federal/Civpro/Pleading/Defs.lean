import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources

open Time

structure AttorneyInfo where
  name : String
  qual : String
  title : String
  address : String
  phone : String
deriving DecidableEq, Repr

structure Count where
  causeOfAction : String
  explanation : List String
deriving DecidableEq, Repr

structure Complaint where
  court : Court.DistrictCourt
  courtDivision : Option String
  -- Name, Addr, Phone, Email
  plaintiff : String
  -- Name, Addr, Phone, Email
  defendant : String
  intro : String
  /- Either Federal Question or Diversity -/
  jurisdictionStatement : String
  venueStatement : String
  facts : List String
  claims : { l : List Count // ¬l.isEmpty }
  prayerForRelief : { l : List String // l.length = claims.val.length }
  requestingJuryTrial : Bool
  plaintiffAttorneyInfo : List AttorneyInfo
deriving DecidableEq, Repr

structure FiledComplaint extends Complaint where
  caseNum : Nat
  filedOn : Date
deriving Repr, DecidableEq

def FiledComplaint.from (c : Complaint) (caseNum : Nat) (filedOn : Date) : FiledComplaint := { c with caseNum, filedOn }

def Complaint.courtName (c : Complaint) : String := 
  let base := s!"{ToString.toString c.court}"
  match c.courtDivision with
  | none => base
  | some d => base ++ s!" {d.toUpper}"

structure ServiceWaiverRequest where
  complaint : FiledComplaint
  recipientIfDifferent : Option String
  defInUsJudicialDistrict : Bool
  date : Date
  address : String
  email : String
  phone : String
deriving DecidableEq, Repr

def ServiceWaiverRequest.formNum : String := "AO 398"

--def ServiceWaiverRequest.text (req : ServiceWaiverRequest) : String :=
instance : ToString ServiceWaiverRequest where
  toString req := 
    s!"UNITED STATES DISTRICT COURT FOR THE {req.complaint.court}\n"++
    s!"Civil Action No. {req.complaint.caseNum}\n\n"++
    s!"To {req.recipientIfDifferent.getD req.complaint.defendant}:\n" ++
    "Why are you getting this?\n" ++
    "A lawsuit has been filed against you, or the entity you represent, in this court under the number shown above. A copy of the complaint is attached.\n" ++
    s!"This is not a summons, or an official notice from the court. It is a request that, to avoid expenses, you waive formal service of a summons by signing and returning the enclosed waiver. To avoid these expenses, you must return the signed waiver within {if req.defInUsJudicialDistrict then 30 else 60} days from the date shown below, which is the date this notice was sent. Two copies of the waiver form are enclosed, along with a stamped, self-addressed envelope or other prepaid means for returning one copy. You may keep the other copy.\n" ++
    "What happens next?\n" ++
    "If you return the signed waiver, I will file it with the court. The action will then proceed as if you had been served on the date the waiver is filed, but no summons will be served on you and you will have 60 days from the date this notice is sent (see the date below) to answer the complaint (or 90 days if this notice is sent to you outside any judicial district of the United States).\n" ++
    "If you do not return the signed waiver within the time indicated, I will arrange to have the summons and complaint served on you. And I will ask the court to require you, or the entity you represent, to pay the expenses of making service.\n" ++
    "Please read the enclosed statement about the duty to avoid unnecessary expenses.\n" ++
    "I certify that this request is being sent to you on the date below.\n\n" ++
    s!"Date: {req.date}\n" ++
    s!"{req.complaint.plaintiff}\n" ++
    s!"{req.address}\n" ++
    s!"{req.email}\n" ++
    s!"{req.phone}"

/-
recipient must return within 30/60 days of the date on the request to avoid the expenses

If the return the signed waiver... 
  it gets filed
  it's as if def had been served on the date of filing
  60/90 days from day the notice was sent to answer the complaint or file a rule12 motion.
  *and they waive objections to service of process*

If the signed waiver is not returned, P has to arrange for process to be served.

If D waives and fails to do their stuff (answer or rule 12) within 60/90 days, a default judgment is entered.
-/


structure ServiceWaiverResponse where
  req : ServiceWaiverRequest
  date : { d : Date // d <= req.date + (Duration.fromDays <| if req.defInUsJudicialDistrict then 60 else 90) }
  address : String
  email : String
  phone : String
deriving DecidableEq, Repr

def ServiceWaiverResponse.formNum : String := "AO 399"

instance : ToString ServiceWaiverResponse where
  toString res := 
    s!"UNITED STATES DISTRICT COURT FOR THE {res.req.complaint.court}\n"++
    s!"Civil Action No. {res.req.complaint.caseNum}\n\n"++
    s!"To {res.req.complaint.plaintiff}:\n" ++
    s!"I have received your request to waive service of a summons in this action along with a copy of the complaint, two copies of this waiver form, and a prepaid means of returning one signed copy of the form to you.\n" ++
    s!"I, or the entity I represent, agree to save the expense of serving a summons and complaint in this case.\n" ++
    s!"I understand that I, or the entity I represent, will keep all defenses or objections to the lawsuit, the court’s jurisdiction, and the venue of the action, but that I waive any objections to the absence of a summons or of service.\n" ++
    s!"I also understand that I, or the entity I represent, must file and serve an answer or a motion under Rule 12 within 60 days from {res.req.date}, the date when this request was sent (or 90 days if it was sent outside the United States). If I fail to do so, a default judgment will be entered against me or the entity I represent.\n\n" ++
    s!"Date: {res.date}\n" ++
    s!"{res.req.complaint.defendant}\n" ++
    s!"{res.address}\n" ++
    s!"{res.email}\n" ++
    s!"{res.phone}"

/- Service is proper for a Federal complaint IFF you have one of these three,
   AND the constitutional analysis is fulfilled 

   ** What is the source for each of these?
   
   -/
inductive Us.Federal.ProperServiceSideCondition where
| rule4 : ProperServiceSideCondition
| stateLawWhereCourtSits : ProperServiceSideCondition
| stateLawWhereServiceMade : ProperServiceSideCondition

/- Was process "reasonably calculated" under all the circumstances
   to inform the defendant of the lawsuit and afford the defendant
   an opportunity to appear and be heard (Mullane)? -/
structure Us.Federal.ProperServiceConstitutional where
  inner : Unit

-- This source is Supreme Court sourced.
--instance : Sourced Us.Federal.ProperServiceConstitutional where
--  source := "Mullane v. Central Hanover Bank & Trust Co., 339 U.S. 306 (1950)"

/- Product of the two -/
def Us.Federal.ProperService := (Us.Federal.ProperServiceSideCondition × Us.Federal.ProperServiceConstitutional)

/- (m) Time Limit for Service. *If a defendant is not served within 90 days 
   after the complaint is filed, the court—on motion or on its own after 
   notice to the plaintiff—must dismiss the action without prejudice against 
   that defendant or order that service be made within a specified time.* But 
   if the plaintiff shows good cause for the failure, the court must extend 
   the time for service for an appropriate period. This subdivision (m) does 
   not apply to service in a foreign country under Rule 4(f), 4(h)(2), or 
   4(j)(1), or to service of a notice under Rule 71.1(d)(3)(A).

   Rule 71.1 is condemnation. -/
inductive ServiceTimeLimit
| standard : ServiceTimeLimit
| serviceInForeignCountry : ServiceTimeLimit
| condemnation : ServiceTimeLimit

open Us.Federal

structure Summons where
  complaint : FiledComplaint
  appearanceWindow : DateRange
  defaultWarning : String
deriving Repr, DecidableEq

def Summons.court (s : Summons) : (Court.DistrictCourt × Option String) := (s.complaint.court, s.complaint.courtDivision)
def Summons.addressedTo (s : Summons) : String := s.complaint.defendant
def Summons.plaintiffAttorneyNames (s : Summons) : List String := s.complaint.plaintiffAttorneyInfo.map AttorneyInfo.name
def Summons.plaintiffAttorneyAddrs (s : Summons) : List String := s.complaint.plaintiffAttorneyInfo.map AttorneyInfo.address

structure CompletedSummons extends Summons where
  hasCourtSeal : Bool
  hasClerkSignature : Bool
  h_seal : hasCourtSeal = true
  h_sig : hasClerkSignature = true
  servedOn : Date
deriving Repr

theorem CompletedSummons.eq_of_val_eq : 
  ∀ {s₁ s₂ : CompletedSummons} (h_su : s₁.toSummons = s₂.toSummons) (h_on : s₁.servedOn = s₂.servedOn), s₁ = s₂
| ⟨su, se, si, h_se, h_si, on⟩, ⟨su', se', si', h_se', h_si', on'⟩, h_su, h_on => by 
  simp at h_on
  rw [h_on]
  simp [h_su, h_se, h_si, h_se', h_si']
  
instance : DecidableEq CompletedSummons
| ⟨su, se, si, h_se, h_si, on⟩, ⟨su', se', si', h_se', h_si', on'⟩ =>
  if h0: su = su' ∧ on = on'
  then isTrue (CompletedSummons.eq_of_val_eq h0.left h0.right)
  else by
    apply isFalse
    intro hf
    rw [CompletedSummons.mk.injEq] at hf
    exact h0 (And.intro hf.left hf.right.right.right)





  --else isFalse (fun hf => ClockTime.noConfusion hf (fun hh => absurd hh h))  


/-
(b) Defenses; Admissions and Denials.

(1) In General. In responding to a pleading, a party must:

(A) state in short and plain terms its defenses to each claim asserted against it; and

(B) admit or deny the allegations asserted against it by an opposing party.

(2) Denials—Responding to the Substance. A denial must fairly respond to the substance of the allegation.

(3) General and Specific Denials. A party that intends in good faith to deny all the allegations of a pleading—including the jurisdictional grounds—may do so by a general denial. A party that does not intend to deny all the allegations must either specifically deny designated allegations or generally deny all except those specifically admitted.

(4) Denying Part of an Allegation. A party that intends in good faith to deny only part of an allegation must admit the part that is true and deny the rest.

(5) Lacking Knowledge or Information. A party that lacks knowledge or information sufficient to form a belief about the truth of an allegation must so state, and the statement has the effect of a denial.

(6) Effect of Failing to Deny. An allegation—other than one relating to the amount of damages—is admitted if a responsive pleading is required and the allegation is not denied. If a responsive pleading is not required, an allegation is considered denied or avoided.

• accord and satisfaction;

• arbitration and award;

• assumption of risk;

• contributory negligence;

• duress;

• estoppel;

• failure of consideration;

• fraud;

• illegality;

• injury by fellow servant;

• laches;

• license;

• payment;

• release;

• res judicata;

• statute of frauds;

• statute of limitations; and

• waiver.
-/
structure Answer where
  contents : String
  servedOn : Date
  admissionsDenials : List String
  /- Rule 8 has a list of affirmative defenses -/
  affirmativeDefenses : List String
deriving Repr, DecidableEq

/- Rule 7 lists the "allowed pleadings" -/
inductive Pleading
| complaint
| answerToComplaint
| answerToCounterclaim
| answerToCrossclaim
| thirdPartyComplaint
| answerToThirdPartyComplaint
| courtOrderedReplyToAnswer
deriving DecidableEq, Repr

abbrev Rule7a := Pleading

