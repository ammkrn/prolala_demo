import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic
import Prolala.Federal.Sources
import Prolala.Util

@[reducible]
def amtInControversyReq (n : Money) := n > 75000

inductive Tag
| state : StateTag -> Tag
| foreignPerm : StateTag -> Tag
| foreignNonperm : Tag
| foreignState : Tag
deriving Repr, DecidableEq

@[reducible] 
def Tag.getState : Tag -> Option StateTag 
| Tag.state s => some s
| Tag.foreignPerm s => some s
| _ => none

@[reducible] 
def Tag.sameState (t₁ t₂ : Tag) := t₁.getState.isSome ∧ t₁.getState = t₂.getState

instance {t₁ t₂ : Tag} : Decidable <| t₁.sameState t₂ := inferInstance

@[reducible] 
def Tag.stateCitizen : Tag -> Prop
| Tag.state _ => True
| _ => False

instance : ∀ {t : Tag}, Decidable t.stateCitizen
| Tag.state _ => instDecidableTrue
| Tag.foreignPerm _ => instDecidableFalse
| Tag.foreignNonperm => instDecidableFalse
| Tag.foreignState => instDecidableFalse

@[reducible] 
def Tag.foreignCitizen : Tag -> Prop
| Tag.foreignPerm _ => True
| Tag.foreignNonperm => True
| _ => False

instance : ∀ {t : Tag}, Decidable <| t.foreignCitizen
| Tag.state _ => instDecidableFalse
| Tag.foreignPerm _ => instDecidableTrue
| Tag.foreignNonperm => instDecidableTrue
| Tag.foreignState => instDecidableFalse

@[reducible] 
def diverseStateCitizens (p1 p2 : Tag) := p1.stateCitizen ∧ p2.stateCitizen ∧ p1 ≠ p2

instance (p1 p2) : Decidable <| diverseStateCitizens p1 p2 := inferInstance

section Alts

variable (xs ys : { l : List Tag // ¬ l.isEmpty })

@[reducible] 
def stateDiversity := ∀ x ∈ xs, ∀ y ∈ ys, x.stateCitizen ∧ y.stateCitizen -> ¬x.sameState y

/- Diversity up to the kind described in (a)(2), where a state citizen and a permanent
   resident domiciled in the same state cannot be members of opposing parties. -/
@[reducible] 
def completeDiversity := ∀ x ∈ xs, ∀ y ∈ ys, ¬x.sameState y

@[reducible] 
def a1 := ∀ x ∈ xs, ∀ y ∈ ys, diverseStateCitizens x y

@[reducible] 
def a2 :=
  let aux (xs ys) := ∀ x ∈ xs, x.stateCitizen ∧ ∀ y ∈ ys, y.foreignCitizen
  (aux xs ys ∨ aux ys xs) ∧ completeDiversity xs ys

@[reducible] 
def a3 := 
    ∃ x ∈ xs, x.stateCitizen
  ∧ ∃ y ∈ ys, y.stateCitizen
  ∧ ∀ x ∈ xs, x.stateCitizen ∨ x.foreignCitizen
  ∧ ∀ y ∈ ys, y.stateCitizen ∨ y.foreignCitizen
  ∧ stateDiversity xs ys

/- 
It's unclear (to me) whether the diversity described in (a)(2) extends to (a)(3).
The language in (a)(2) scopes the provision with "this subsection", so we implement
both. 
-/
@[reducible] 
def a3Alt := 
    ∃ x ∈ xs, x.stateCitizen
  ∧ ∃ y ∈ ys, y.stateCitizen
  ∧ ∀ x ∈ xs, x.stateCitizen ∨ x.foreignCitizen
  ∧ ∀ y ∈ ys, y.stateCitizen ∨ y.foreignCitizen
  ∧ completeDiversity xs ys

@[reducible] 
def a4 := xs = [Tag.foreignState] ∧ ∀ y ∈ ys, y.stateCitizen

@[reducible] 
def s1332Ok :=
    a1 xs ys
  ∨ a2 xs ys
  ∨ a3 xs ys
  ∨ a4 xs ys

@[reducible] 
def s1332OkAlt :=
    a1 xs ys
  ∨ a2 xs ys
  ∨ a3Alt xs ys
  ∨ a4 xs ys

instance : Decidable <| stateDiversity xs ys := inferInstance
instance : Decidable <| completeDiversity xs ys := inferInstance
instance : Decidable <| a1 xs ys := inferInstance
instance : Decidable <| a2 xs ys := inferInstance
instance : Decidable <| a3 xs ys := inferInstance
instance : Decidable <| a3Alt xs ys := inferInstance
instance : Decidable <| a4 xs ys := inferInstance
instance : Decidable <| s1332Ok xs ys := inferInstance
instance : Decidable <| s1332OkAlt xs ys := inferInstance

inductive DiversityResult where
| a1 (ps ds) : a1 ps ds -> DiversityResult
| a2 (ps ds) : a2 ps ds -> DiversityResult
| a3 (ps ds) : a3 ps ds -> DiversityResult
| a3Alt (ps ds) : a3Alt ps ds -> DiversityResult
| a4 (ps ds) : a4 ps ds -> DiversityResult

/- 1332 DiversityResult indexed by the p/d lists -/
inductive IndexedDiversityResult (ps ds : { l : List Tag // ¬l.isEmpty }) where
| a1 : a1 ps ds -> IndexedDiversityResult ps ds
| a2 : a2 ps ds -> IndexedDiversityResult ps ds
| a3 : a3 ps ds -> IndexedDiversityResult ps ds
| a3Alt : a3Alt ps ds -> IndexedDiversityResult ps ds
| a4 : a4 ps ds -> IndexedDiversityResult ps ds


def tryDiversityResult (amtInControversy : Money ) : Option DiversityResult :=
  if amtInControversyReq amtInControversy
  then
    if h1 : a1 xs ys then DiversityResult.a1 xs ys h1
    else if h2 : a2 xs ys then DiversityResult.a2 xs ys h2
    else if h3 : a3 xs ys then DiversityResult.a3 xs ys h3
    else if h4 : a4 xs ys then DiversityResult.a4 xs ys h4
    else none
  else none

def DiversityResult.statement (r : DiversityResult) : String :=
  let diversity := "there is diversity of citizenship"
  let base := fun s1 s2 => s!"This Court has subject matter jurisdiction pursuant to 28 U.S.C. § 1332(a)({s1}), because {s2}, and this is a civil action involving, exclusive of interest and costs, a sum in excess of $75,000."
  match r with
  | a1 _ _ _ => base "1" diversity
  | a2 _ _ _ => base "2" diversity
  | a3 _ _ _ => base "3" diversity
  | a3Alt _ _ _ => base "4" diversity
  | a4 _ _ _ => base "4" "the Plaintiff is a foreign state, the Defendants are citizens of a State"

def jurisdictionStatement (amt : Money) : Option String := (tryDiversityResult xs ys amt).map DiversityResult.statement

open Tag StateTag

def xs1 : { l : List Tag // ¬l.isEmpty } := ⟨[foreignPerm Texas, state Texas], by decide⟩ 
def ys1 : { l : List Tag // ¬l.isEmpty } := ⟨[foreignPerm Alaska, state Washington], by decide⟩ 
#eval jurisdictionStatement xs1 ys1 100000
#eval jurisdictionStatement xs1 ys1 1

def xs2 : { l : List Tag // ¬l.isEmpty } := ⟨[foreignPerm Texas, state Texas], by decide⟩ 
def ys2 : { l : List Tag // ¬l.isEmpty } := ⟨[foreignPerm Alaska], by decide⟩ 
#eval jurisdictionStatement xs2 ys2 100000
#eval jurisdictionStatement xs2 ys2 75000

def xs3 : { l : List Tag // ¬l.isEmpty } := ⟨[state Texas], by decide⟩ 
def ys3 : { l : List Tag // ¬l.isEmpty } := ⟨[state Washington], by decide⟩ 
#eval jurisdictionStatement xs3 ys3 75001

def xs4 : { l : List Tag // ¬l.isEmpty } := ⟨[state Texas, state Georgia], by decide⟩ 
def ys4 : { l : List Tag // ¬l.isEmpty } := ⟨[state Washington, state Michigan], by decide⟩ 
#eval jurisdictionStatement xs3 ys3 75001

def xs5 : { l : List Tag // ¬l.isEmpty } := ⟨[state Texas, state Georgia, state Georgia, state Alaska], by decide⟩ 
def ys5 : { l : List Tag // ¬l.isEmpty } := ⟨[foreignPerm Colorado, foreignNonperm, foreignPerm NewYork], by decide⟩ 
#eval jurisdictionStatement xs5 ys5 75001

def xs6 : { l : List Tag // ¬l.isEmpty } := ⟨[foreignState], by decide⟩ 
def ys6 : { l : List Tag // ¬l.isEmpty } := ⟨[foreignPerm Colorado, foreignNonperm, foreignPerm NewYork], by decide⟩ 
#eval jurisdictionStatement xs6 ys6 75001

def xs7 : { l : List Tag // ¬l.isEmpty } := ⟨[foreignState], by decide⟩ 
def ys7 : { l : List Tag // ¬l.isEmpty } := ⟨[state Illinois, state California], by decide⟩ 
#eval jurisdictionStatement xs7 ys7 75001
#eval jurisdictionStatement ys7 xs7 75001

end Alts
