import Mathlib.Init.SetNotation
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Int.Order
import Mathlib.Algebra.Ring.Basic

abbrev NonnegMoney := { x : Int // 0 <= x }

instance {n : Nat} : OfNat NonnegMoney n where
  ofNat := ⟨Int.ofNat n, Int.ofNat_nonneg _⟩ 

abbrev Money := Int

def unCamelCase (s : String) : String := 
  s.foldl (fun sink next => sink ++ if next.isUpper then s!" {next}" else s!"{next}") ""
  
def endOnly (s : String) : String :=
  s.foldl (fun sink next => if next = '.' then "" else sink ++ s!"{next}") ""

inductive Either (A : Type u) (B : Type v)
| left : A → Either A B
| right : B → Either A B
deriving DecidableEq, Repr

def sum' (l : List Int) : Int := l.foldr (fun sink next => sink + next) 0
def sum (l : List NonnegMoney) : NonnegMoney := l.foldr (fun (sink : NonnegMoney) next => ⟨sink + next.val, Int.add_nonneg sink.property next.property⟩) ⟨0, le_refl 0⟩ 

theorem sum_zero_of_empty {l : List NonnegMoney} (h : l.isEmpty) : sum l = ⟨0, le_refl 0⟩ :=
  match h':l with
  | [] => rfl
  | hd::tl => by cases h

lemma ne_symm {A : Sort u} (p q : Sort u) : (p ≠ q) = (q ≠ p) := by
  apply propext
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro h h'
    exact h h'.symm
  case mpr =>
    intro h h'
    exact h h'.symm

theorem not_eq_true_eq_false (p : Bool) : (¬p = true) = (p = false) := by
  apply propext
  refine Iff.intro ?mp ?mpr
  case mp =>
    cases p with
    | true => exact absurd rfl 
    | false => exact fun _ => rfl
  case mpr =>
    cases p with
    | true => intro h; cases h
    | false => intro h1 h2; cases h2

lemma ne_flip {A : Sort u} {p q : A} (h : p ≠ q) : (q ≠ p) := fun hqp => absurd hqp.symm h

inductive ReflTransGen {A : Sort u} (r : A -> A -> Prop) (a : A) : A -> Prop
| refl {}    : ReflTransGen r a a
| tail {b c} : ReflTransGen r a b -> r b c -> ReflTransGen r a c

instance {p : List α -> Prop} : Mem α { l : List α // p l } where
  mem x l := x ∈ l.val

instance {p : List α → Prop} : Coe { l : List α // p l } (List α) where
  coe x := x.val

instance (p : α → Prop) (q : List α -> Prop) [DecidablePred p] (l : { x : List α // q x }) : Decidable (∃ x ∈ l, p x) := 
  inferInstanceAs (Decidable (∃ x ∈ l.val, p x))

instance (p : α → Prop) (q : List α -> Prop) [DecidablePred p] (l : { x : List α  // q x }) : Decidable (∀ x ∈ l, p x) := 
  inferInstanceAs (Decidable (∀ x ∈ l.val, p x))
  
theorem add_cancel_mid (a b: Int) : a + (b + -a) = b := by
  have h0 : a + (b + -a) = (a + b) + -a := (add_assoc a b (-a)).symm
  rw [add_comm a]
  rw [add_assoc b]
  simp

theorem sub_comm_right (a c d : Int) : a - c - d = a - d - c := by
  have h0 : a - c - d = a + -c + -d := rfl
  have h1 : a - d - c = a + -d + -c := rfl
  rw [h0, h1, add_assoc a, add_comm (-c), add_assoc a]

theorem sub_add_eq_add_sub (a b d : Int) : (a - d) + b = (a + b) - d := by
  have h0 : a - d = a + -d := rfl
  have h1 : (a + b) - d = (a + b) + -d := rfl
  rw [h0, h1, add_assoc a b, add_comm b, add_assoc]

@[simp] theorem sub_zero (a : Int) : a - 0 = a := by
  have h1 : (a - 0) = (a + -0) := rfl
  have h2 : (-0 : Int) = 0 := rfl
  simp [h1, h2, add_zero]

@[simp] theorem NonnegMoney.zero_def : (0 : NonnegMoney).val = (0 : Int) := rfl

theorem subtype_eq {A : Type u} {p : A -> Prop} {a a' : A} {h : p a} {h' : p a'} : a = a' -> Subtype.mk a h = Subtype.mk a' h' := by
  intro h
  simp [h]

theorem is_empty_iff_length_eq_zero {A : Type u} : ∀ (l : List A), l.isEmpty <-> l.length = 0
| [] => by simp
| hd::tl => by
  refine Iff.intro ?mp ?mpr
  case mp => intro hh; cases hh
  case mpr =>intro hh; cases hh

theorem empty_iff_empty {A : Type u} {l₁ l₂ : List A} (h : l₁.length = l₂.length) : l₁.isEmpty <-> l₂.isEmpty := by
  rw [is_empty_iff_length_eq_zero l₁, is_empty_iff_length_eq_zero _, h]


@[simp] theorem max_double (a b : Int) : max a (max a b) = max a b := by
  byCases hm : a <= b
  case inl => simp only [max_eq_right hm]
  case inr => simp only [max_eq_left <| le_of_lt <| lt_of_not_ge hm]; exact max_self _

theorem sub_add_eq_sub_sub (a b c : Int) : a - (b + c) = a - b - c := by
  have h0 : a - b - c = a + -b + -c := rfl
  have h1 : a - (b + c) = a + -(b + c) := rfl
  rw [Int.neg_add] at h1
  rw [h0, add_assoc]
  assumption

theorem max_zero_min_zero (a : Int) : max 0 (min 0 a) = 0 := by
  byCases hx : 0 <= a
  case inl => rw [min_eq_left]; simp; assumption
  case inr =>
    have hle := le_of_lt (lt_of_not_ge hx)
    rw [min_eq_right hle]
    exact max_eq_left hle

lemma predSuccLem (x y : Nat) (h0 : 0 < x) : x.pred + y.succ = x + y := by
  cases x with
  | zero => exact False.elim (Nat.not_lt_zero _ h0)
  | succ x => simp [Nat.add_succ, Nat.succ_add]

theorem lt_plus {n x : Nat} : ¬(n + x < x) := by
  intro hf
  induction n with
  | zero => simp at hf; exact Nat.lt_irrefl x hf
  | succ n ih => rw [Nat.succ_add] at hf; exact (ih (Nat.lt_of_succ_lt hf : (n + x) < x))

theorem le_plus {a b c : Nat} (h0 : a <= b) : (a <= b + c) := by
  induction c with
  | zero => simp; assumption
  | succ c ih => simp [Nat.add_succ]; exact Nat.le_succ_of_le ih

theorem ne_zero_helper : ∀ {n : Nat}, n ≠ 0 -> 0 < n
| 0 => fun h => absurd rfl h
| n+1 => fun _ => Nat.zero_lt_succ _

lemma lt_of_add_sub {a b c : Nat} (h0 : 0 < a) (h1 : b <= a) (h2 : c < b) : (a - b) + c < a := by
  induction b generalizing a c with
  | zero =>
    exact False.elim (Nat.not_lt_zero _ h2)
  | succ b ih =>
    cases c with
    | zero =>
      simp
      exact Nat.sub_lt h0 (Nat.succ_pos b)
    | succ c =>
      simp [Nat.sub_succ]
      specialize @ih a c h0 (Nat.le_of_succ_le h1) (Nat.lt_of_succ_lt_succ h2)
      have hsetup : b < a := Nat.lt_of_succ_le h1
      have hsetup' := Nat.sub_pos_of_lt hsetup
      have hhhh := predSuccLem (a - b) c hsetup'
      rw [hhhh]
      exact ih

/- From mathlib3. -/
theorem Nat.div_le_div_right {a b c : Nat} (h : a <= b) : a / c <= b / c := sorry
  
structure Rat where
  num : Int
  den : Nat
  pos : den > 0

instance (n : Nat) : OfNat Rat n where
  ofNat := {
    num := n
    den := 1
    pos := by decide
  }

instance : HMul Int Rat Int where
  hMul i r := (i * r.num) / r.den

theorem eq_zero_of_add_zero {a b : Int} (h0 : 0 <= a) (h1 : 0 <= b) (h2 : a + b = 0) : a = 0 ∧ b = 0 := 
  match Decidable.eq_or_lt_of_le h0 with
  | Or.inl hl =>
    match Decidable.eq_or_lt_of_le h1 with
    | Or.inl hl' => And.intro hl.symm hl'.symm
    | Or.inr hr' => by
      refine And.intro hl.symm ?r
      rw [<- hl, zero_add] at h2
      exact h2
  | Or.inr hr =>
    match Decidable.eq_or_lt_of_le h1 with
    | Or.inl hl' => by
      refine And.intro ?l hl'.symm 
      rw [<- hl', add_zero] at h2
      rw [h2]
      done
    | Or.inr hr' => by
      have hx := Int.add_pos hr hr'
      rw [h2] at hx
      exact absurd hx (lt_irrefl 0)
      
theorem add_eq_zero_right {a b : Int} (h0 : 0 <= a) (h1 : 0 <= b) (h2 : a + b = 0) : b = 0 := 
  (eq_zero_of_add_zero h0 h1 h2).right

theorem add_eq_zero_left {a b : Int} (h0 : 0 <= a) (h1 : 0 <= b) (h2 : a + b = 0) : a = 0 := 
  (eq_zero_of_add_zero h0 h1 h2).left

theorem mul_le_of_le_one_right {a b c : Int} (ha : 0 ≤ a) (hb1 : b ≤ 1) : a * b ≤ a := by
  have h0 := Int.mul_le_mul_of_nonneg_left hb1 ha
  rw [Int.mul_one] at h0
  assumption

/- From mathlib3. -/
theorem int_rat_hMul_le (i : Int) {r : Rat} (h0 : 0 <= i) (h1 : r.num <= r.den) : i * r <= i := sorry
  
theorem right_or_of_not_left {a b c : Prop} (h : a ∨ b ∨ c) (h' : ¬a) : b ∨ c := 
   match h with
   | Or.inl hl => absurd hl h'
   | Or.inr hr => hr

theorem casesmin {α : Type u} [LinearOrder α] (a b : α) : min a b = a ∨ min a b = b := 
  if h : a <= b
  then Or.inl (min_eq_left h)
  else Or.inr (min_eq_right (le_of_lt (lt_of_not_ge h)))

theorem casesmin2 {α : Type u} [LinearOrder α] {a b : α} (h : min a b = a) : a <= b := 
  if h' : a <= b 
  then h'
  else by simp [min, h'] at h; exact absurd (h ▸ (lt_of_not_ge h' : b < a)) (lt_irrefl a)

lemma Bool.not_eq_true_eq_false {b : Bool} : b = true -> b = false -> False := 
  fun h1 h2 => Bool.noConfusion (h1 ▸ h2 : true = false)

lemma Bool.not_eq_false_eq_true {b : Bool} : b = false -> b = true -> False := flip Bool.not_eq_true_eq_false

def Option.get_h {A : Type u} {a : Option A} (h : a.isSome) : { a' : A // a = some a' } :=
  match h':a with
  | some a' => ⟨a', rfl⟩ 
  | none => by rw [h'] at h; cases h

def Option.eq_none_of_nexi {A : Type u} {x : Option A} (nexi : ¬∃ (a : A), x = some a) : x = none :=
  match x with
  | none => rfl
  | some a => False.elim <| nexi ⟨a, rfl⟩

theorem Decidable.not_and_imp_nor {p q : Prop} [Decidable p] (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  if hp : p then Or.inr (fun hq => absurd ⟨hp, hq⟩ h) else Or.inl hp

theorem Decidable.not_and_imp_nor3 {p q r : Prop} [Decidable p] [Decidable q] (h : ¬(p ∧ q ∧ r)) : ¬p ∨ ¬q ∨ ¬r :=
  if hp : p 
  then 
    if hq : q
    then Or.inr <| Or.inr <| fun hr => absurd ⟨hp, hq, hr⟩ h
    else Or.inr <| Or.inl hq
  else Or.inl hp

theorem Decidable.not_and_imp_nor4 {p q r s : Prop} [Decidable p] [Decidable q] [Decidable r] (h : ¬(p ∧ q ∧ r ∧ s)) : ¬p ∨ ¬q ∨ ¬r ∨ ¬s :=
  if hp : p 
  then 
    if hq : q
    then 
      if hr : r
      then Or.inr <| Or.inr <| Or.inr <| fun hs => absurd ⟨hp, hq, hr, hs⟩ h
      else Or.inr <| Or.inr <| Or.inl hr
    else Or.inr <| Or.inl hq
  else Or.inl hp

partial def qsort {A : Type u} [LT A] [DecidableRel (.<. : A -> A -> Prop)] : List A -> List A 
| [] => []
| h :: t =>
  let (xs, ys) := t.partition (fun x => x < h)
  qsort xs ++ [h] ++ qsort ys

partial def List.qsortBy {A : Type u} {B : Type v} [LT B] [DecidableRel (.<. : B -> B -> Prop)] (f : A → B) : List A → List A 
| [] => []
| h :: t =>
  let (xs, ys) := t.partition (fun x => f x < f h)
  qsortBy f xs ++ [h] ++ qsortBy f ys

-- mathlib 3 group.
theorem eq_add_of_sub_eq {a b c : Int} (h : a - c = b) : a = b + c := sorry

-- linarith closes this.
theorem linarith0 (a z x q : Int) : a - (z + x - q) = q + a - z - x := sorry

theorem linarith1 (a b c d e : Int) : a + b + c + d - (b + c + d + e) = a - e := by
  rw [(show a + b + c + d = a + (b + c + d) by repeat rw [add_assoc]), Int.add_sub_assoc a (b + c + d)]
  simp [sub_add_eq_sub_sub, Int.sub_self, <- Int.add_sub_assoc]