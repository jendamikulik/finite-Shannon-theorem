/-
Unchecked sketch of `questions_structure_causal_simulation.pdf`.

Status: NOT a certificate. This file is outside `CausalSeed` and is not
imported by `Main.lean`. It was not built in the environment that added it.
Run `lake env lean sketch/QuestionsStructure.lean` on
`leanprover/lean4:v4.35.0-rc3` before citing it.

Formalized: observable quotient, future behavioral quotient, the
three-state counterexample, reachability invariants, the support bound
for exact selection, empty input versus a specified point, the swap
obstruction, generation from the empty set, hidden extensions.

Not formalized: stochastic lumpability (Theorem 4.1), the entropy form
of Theorem 6.1, the `m - 1` refinement bound, and the entropy cost of
a symmetric seed.
-/

import Mathlib.Data.Fintype.Card

namespace QuestionsStructure

/-! ## Observable quotient -/

def Obs.setoid {Ω α : Type*} (A : Ω → α) : Setoid Ω where
  r x y := A x = A y
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def Obs.factor {Ω α : Type*} (A : Ω → α) : Quotient (Obs.setoid A) → α :=
  Quotient.lift A (fun _ _ h => h)

theorem Obs.factor_mk {Ω α : Type*} (A : Ω → α) (x : Ω) :
    Obs.factor A (Quotient.mk (Obs.setoid A) x) = A x :=
  rfl

theorem Obs.factor_injective {Ω α : Type*} (A : Ω → α) :
    Function.Injective (Obs.factor A) := by
  intro q1 q2 h
  induction q1 using Quotient.ind with
  | mk x =>
    induction q2 using Quotient.ind with
    | mk y =>
      apply Quotient.sound
      have hxy :
          Obs.factor A (Quotient.mk (Obs.setoid A) x) =
            Obs.factor A (Quotient.mk (Obs.setoid A) y) := h
      rw [Obs.factor_mk, Obs.factor_mk] at hxy
      exact hxy

theorem Obs.factorsThrough {Ω α β : Type*} (A : Ω → α) (f : Ω → β)
    (h : ∀ x y, A x = A y → f x = f y) :
    ∃ fbar : Quotient (Obs.setoid A) → β,
      ∀ x, fbar (Quotient.mk (Obs.setoid A) x) = f x := by
  refine ⟨Quotient.lift f (fun x y hxy => h x y hxy), fun _ => rfl⟩

theorem Obs.refines {Ω α β : Type*} (A : Ω → α) (B : Ω → β)
    (h : ∀ x y, B x = B y → A x = A y) :
    ∃ ρ : Quotient (Obs.setoid B) → Quotient (Obs.setoid A),
      Function.Surjective ρ ∧ ∀ x, ρ (Quotient.mk (Obs.setoid B) x) =
        Quotient.mk (Obs.setoid A) x := by
  refine ⟨Quotient.lift (fun x => Quotient.mk (Obs.setoid A) x)
      (fun x y hxy => Quotient.sound (h x y hxy)), ?_, fun _ => rfl⟩
  intro q
  induction q using Quotient.ind with
  | mk x =>
    exact ⟨Quotient.mk (Obs.setoid B) x, rfl⟩

theorem Obs.separates_iff_injective {Ω α : Type*} (A : Ω → α) :
    Function.Injective A ↔ ∀ x y, (Obs.setoid A).r x y → x = y := by
  constructor
  · intro h x y hr
    exact h hr
  · intro h x y hr
    exact h x y hr

instance piEmpty_subsingleton {Y : Empty → Type*} :
    Subsingleton ((i : Empty) → Y i) :=
  ⟨fun f g => funext fun i => i.elim⟩

theorem Obs.emptyQuestions_oneClass {Ω : Type*} {Y : Empty → Type*} [Nonempty Ω]
    (A : Ω → ((i : Empty) → Y i)) :
    ∃ q : Quotient (Obs.setoid A), ∀ q', q' = q := by
  obtain ⟨x0⟩ := ‹Nonempty Ω›
  refine ⟨Quotient.mk (Obs.setoid A) x0, ?_⟩
  intro q'
  induction q' using Quotient.ind with
  | mk x =>
    exact (Quotient.sound (Subsingleton.elim (A x) (A x0))).symm

def agrees {Ω α : Type*} : List (Ω → α) → List α → Ω → Prop
  | [], [], _ => True
  | q :: qs, y :: ys, x => q x = y ∧ agrees qs ys x
  | _, _, _ => False

theorem agrees_tail {Ω α : Type*} (q : Ω → α) (qs : List (Ω → α))
    (y : α) (ys : List α) (x : Ω) :
    agrees (q :: qs) (y :: ys) x → agrees qs ys x := by
  intro h
  exact h.2

/-! ## Future questions -/

def wordStep {S A : Type*} (step : A → S → S) : List A → S → S
  | [], s => s
  | a :: w, s => wordStep step w (step a s)

def relK {S A Y : Type*} (o : S → Y) (step : A → S → S) : Nat → S → S → Prop
  | 0, x, x' => o x = o x'
  | k + 1, x, x' =>
      relK o step k x x' ∧ ∀ a, relK o step k (step a x) (step a x')

theorem relK_zero {S A Y : Type*} (o : S → Y) (step : A → S → S) :
    ∀ k x x', relK o step k x x' → relK o step 0 x x' := by
  intro k x x' h
  induction k with
  | zero => exact h
  | succ k ih => exact ih h.1

theorem words_of_relK {S A Y : Type*} (o : S → Y) (step : A → S → S) :
    ∀ k x x', relK o step k x x' →
      ∀ w, w.length ≤ k → o (wordStep step w x) = o (wordStep step w x')
  | 0, x, x', h, [], _ => h
  | 0, _, _, _, _ :: _, hw => by omega
  | k + 1, x, x', h, [], _ => relK_zero o step (k + 1) x x' h
  | k + 1, x, x', h, a :: w, hw =>
      words_of_relK o step k (step a x) (step a x') (h.2 a) w
        (Nat.le_of_succ_le_succ hw)

theorem relK_of_words {S A Y : Type*} (o : S → Y) (step : A → S → S) :
    ∀ k x x',
      (∀ w, w.length ≤ k → o (wordStep step w x) = o (wordStep step w x')) →
        relK o step k x x'
  | 0, _, _, h => h [] (Nat.zero_le _)
  | k + 1, x, x', h => by
      constructor
      · exact relK_of_words o step k x x'
          (fun w hw => h w (Nat.le_trans hw (Nat.le_succ k)))
      · intro a
        apply relK_of_words o step k
        intro w hw
        exact h (a :: w) (Nat.succ_le_succ hw)

def behSetoid {S A Y : Type*} (o : S → Y) (step : A → S → S) : Setoid S where
  r x y := ∀ w, o (wordStep step w x) = o (wordStep step w y)
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h w => (h w).symm
    trans := fun h1 h2 w => (h1 w).trans (h2 w)
  }

structure DynCong {S A Y : Type*} (o : S → Y) (step : A → S → S) where
  r : S → S → Prop
  refl : ∀ x, r x x
  symm : ∀ x y, r x y → r y x
  trans : ∀ x y z, r x y → r y z → r x z
  obs_eq : ∀ x y, r x y → o x = o y
  step_ok : ∀ a x y, r x y → r (step a x) (step a y)

theorem beh_is_cong {S A Y : Type*} (o : S → Y) (step : A → S → S) :
    DynCong o step := {
  r := (behSetoid o step).r
  refl := fun _ _ => rfl
  symm := fun h w => (h w).symm
  trans := fun h1 h2 w => (h1 w).trans (h2 w)
  obs_eq := fun x y h => h []
  step_ok := fun a x y h w => h (a :: w)
}

theorem dynCong_le_beh {S A Y : Type*} (o : S → Y) (step : A → S → S)
    (C : DynCong o step) {x y : S} (h : C.r x y) :
    (behSetoid o step).r x y := by
  intro w
  induction w generalizing x y with
  | nil =>
    exact C.obs_eq x y h
  | cons a w ih =>
    exact ih (C.step_ok a x y h)

def quotObs {S A Y : Type*} (o : S → Y) (step : A → S → S) :
    Quotient (behSetoid o step) → Y :=
  Quotient.lift o (fun x y h => h [])

def quotStep {S A Y : Type*} (o : S → Y) (step : A → S → S) (a : A) :
    Quotient (behSetoid o step) → Quotient (behSetoid o step) :=
  Quotient.lift (fun x => Quotient.mk (behSetoid o step) (step a x))
    (fun x y h => Quotient.sound (fun w => h (a :: w)))

def quotWord {S A Y : Type*} (o : S → Y) (step : A → S → S) :
    List A → Quotient (behSetoid o step) → Quotient (behSetoid o step)
  | [], q => q
  | a :: w, q => quotWord o step w (quotStep o step a q)

theorem quotWord_mk {S A Y : Type*} (o : S → Y) (step : A → S → S) :
    ∀ (w : List A) (x : S),
      quotWord o step w (Quotient.mk (behSetoid o step) x) =
        Quotient.mk (behSetoid o step) (wordStep step w x)
  | [], _ => rfl
  | a :: w, x => by
      rw [quotWord, wordStep]
      rw [show quotStep o step a (Quotient.mk (behSetoid o step) x) =
          Quotient.mk (behSetoid o step) (step a x) from rfl]
      exact quotWord_mk o step w (step a x)

theorem quot_reproduces {S A Y : Type*} (o : S → Y) (step : A → S → S)
    (w : List A) (x : S) :
    quotObs o step (quotWord o step w (Quotient.mk (behSetoid o step) x)) =
      o (wordStep step w x) := by
  rw [quotWord_mk]
  rfl

inductive Three where
  | zero
  | one
  | two
  deriving DecidableEq

def obs3 : Three → Bool
  | .zero => false
  | .one => false
  | .two => true

def step3 : Three → Three
  | .zero => .zero
  | .one => .two
  | .two => .two

theorem present_not_enough :
    obs3 .zero = obs3 .one ∧ obs3 (step3 .zero) ≠ obs3 (step3 .one) := by
  constructor
  · rfl
  · decide

/-! ## Reachability and invariants -/

def Reaches {S A : Type*} (step : A → S → S) (x y : S) : Prop :=
  ∃ w, wordStep step w x = y

theorem reaches_preserves_invariant {S A V : Type*} {step : A → S → S} {I : S → V}
    (hI : ∀ a x, I (step a x) = I x) {x y : S} (h : Reaches step x y) :
    I x = I y := by
  rcases h with ⟨w, hw⟩
  induction w generalizing x with
  | nil =>
    rw [show wordStep step [] x = x from rfl] at hw
    rw [hw]
  | cons a w ih =>
    rw [show wordStep step (a :: w) x = wordStep step w (step a x) from rfl] at hw
    calc
      I x = I (step a x) := (hI a x).symm
      _ = I y := ih (step a x) hw

theorem universal_reachability_const {S A V : Type*}
    {step : A → S → S} {I : S → V}
    (hreach : ∀ x y, Reaches step x y)
    (hI : ∀ a x, I (step a x) = I x) (x y : S) :
    I x = I y :=
  reaches_preserves_invariant hI (hreach x y)

def stepStuck : Unit → Bool → Bool := fun _ _ => true

theorem word_stuck_true (w : List Unit) : wordStep stepStuck w true = true := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [show wordStep stepStuck (a :: w) true =
        wordStep stepStuck w (stepStuck a true) from rfl, stepStuck, ih]

theorem stuck_invariants_constant {V : Type*} (I : Bool → V)
    (hI : ∀ a x, I (stepStuck a x) = I x) :
    I false = I true :=
  (hI () false).symm

theorem stuck_not_universal : ¬ Reaches stepStuck true false := by
  intro h
  rcases h with ⟨w, hw⟩
  have ht := word_stuck_true w
  rw [hw] at ht
  cases ht

/-! ## Selection, support bound -/

theorem selection_support {k n : Nat} (f : Fin k → Fin n)
    (hf : Function.Surjective f) : n ≤ k := by
  simpa using Fintype.card_le_of_surjective f hf

/-! ## Empty input, a specified point, symmetry -/

theorem empty_fun_unique {S : Type*} (f g : Empty → S) : f = g :=
  funext fun i => i.elim

theorem empty_fun_image_empty {S : Type*} (f : Empty → S) (s : S) :
    ¬ ∃ i, f i = s := by
  intro ⟨i, _⟩
  exact i.elim

def fromUnit {α : Type*} (f : Unit → α) : α := f ()

def toUnit {α : Type*} (s : α) : Unit → α := fun _ => s

theorem unit_left {α : Type*} (f : Unit → α) : toUnit (fromUnit f) = f :=
  funext fun u => by cases u; rfl

theorem unit_right {α : Type*} (s : α) : fromUnit (toUnit s) = s :=
  rfl

def swap2 : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

theorem fin2_eq (i : Fin 2) : i = 0 ∨ i = 1 := by
  by_cases h : i.val = 0
  · exact Or.inl (Fin.ext h)
  · right
    have : i.val = 1 := by
      have hv : i.val < 2 := i.isLt
      omega
    exact Fin.ext this

theorem swap2_swap2 (i : Fin 2) : swap2 (swap2 i) = i := by
  rcases fin2_eq i with rfl | rfl
  · rfl
  · rfl

theorem swap2_injective : Function.Injective swap2 := by
  intro i j h
  have h' := congrArg swap2 h
  rw [swap2_swap2, swap2_swap2] at h'
  exact h'

theorem swap2_surjective : Function.Surjective swap2 :=
  fun i => ⟨swap2 i, swap2_swap2 i⟩

theorem swap2_ne (i : Fin 2) : swap2 i ≠ i := by
  rcases fin2_eq i with rfl | rfl
  · decide
  · decide

theorem no_bijection_fixed_point :
    ¬ ∃ c : Fin 2, ∀ f : Fin 2 → Fin 2,
      Function.Injective f → Function.Surjective f → f c = c := by
  intro ⟨c, h⟩
  exact swap2_ne c (h swap2 swap2_injective swap2_surjective)

/-! ## Generation -/

def grow {S : Type*} (R : S → S → Prop) : Nat → S → Prop
  | 0, _ => False
  | n + 1, y => grow R n y ∨ ∃ x, grow R n x ∧ R x y

theorem grow_empty {S : Type*} (R : S → S → Prop) :
    ∀ n y, ¬ grow R n y := by
  intro n
  induction n with
  | zero =>
    intro y h
    exact h
  | succ n ih =>
    intro y h
    rcases h with h | ⟨x, hx, _⟩
    · exact ih y h
    · exact ih x hx

def growFrom {S : Type*} (R : S → S → Prop) (B : S → Prop) : Nat → S → Prop
  | 0, _ => False
  | n + 1, y => growFrom R B n y ∨ (∃ x, growFrom R B n x ∧ R x y) ∨ B y

theorem growFrom_uses_base {S : Type*} (R : S → S → Prop) (B : S → Prop)
    {y : S} (hy : B y) : growFrom R B 1 y :=
  Or.inr (Or.inr hy)

/-! ## Hidden extensions -/

def extStep {S E A : Type*} (step : A → S → S) (G : A → S → E → E) :
    A → S × E → S × E :=
  fun a p => (step a p.1, G a p.1 p.2)

def extObs {S E Y : Type*} (o : S → Y) : S × E → Y :=
  fun p => o p.1

def run {S A Y : Type*} (step : A → S → S) (o : S → Y) (π : List Y → A) :
    Nat → S → List Y → List Y
  | 0, _, hist => hist
  | n + 1, s, hist =>
      let hist' := hist ++ [o s]
      run step o π n (step (π hist') s) hist'

theorem hidden_run {S E A Y : Type*} (step : A → S → S) (G : A → S → E → E)
    (o : S → Y) (π : List Y → A) :
    ∀ n (s : S) (e : E) (hist : List Y),
      run (extStep step G) (extObs o) π n (s, e) hist =
        run step o π n s hist := by
  intro n
  induction n with
  | zero =>
    intro s e hist
    rfl
  | succ n ih =>
    intro s e hist
    rw [run, run]
    have hobs : extObs o (s, e) = o s := rfl
    rw [hobs]
    have hstep : extStep step G (π (hist ++ [o s])) (s, e) =
        (step (π (hist ++ [o s])) s, G (π (hist ++ [o s])) s e) := rfl
    rw [hstep]
    exact ih (step (π (hist ++ [o s])) s)
      (G (π (hist ++ [o s])) s e) (hist ++ [o s])

end QuestionsStructure
