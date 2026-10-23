/-
Typechecked formalization of the note on relative rest.

Scope: deterministic system, behavioral quotient (Věta 1), the three
notions of rest and the failure of the converse implications, the
characterization of observable rest (Věta 2), a live hidden coordinate
(oddíl 4), monotonicity under more interventions (Věta 3), and the
box that is frozen for `F` and separated by `R`. The support forms of
the seed-cost jump and of target selection are included. Shannon
entropy, stochastic lumpability and `Cₙ` as an entropy infimum are not.

Checked by `lake env lean sketch/RelativeRest.lean` on
`leanprover/lean4:v4.35.0-rc3`. Not part of `CausalSeed`.
-/

import Mathlib.Data.Fintype.Card

namespace RelativeRest

def wordStep {X A : Type*} (step : A → X → X) : List A → X → X
  | [], x => x
  | a :: w, x => wordStep step w (step a x)

structure Sys (X A Y : Type*) where
  step : A → X → X
  obs : X → Y

def Beh {X A Y : Type*} (S : Sys X A Y) (x x' : X) : Prop :=
  ∀ w : List A, S.obs (wordStep S.step w x) = S.obs (wordStep S.step w x')

def behSetoid {X A Y : Type*} (S : Sys X A Y) : Setoid X where
  r := Beh S
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h w => (h w).symm
    trans := fun h1 h2 w => (h1 w).trans (h2 w)
  }

/-! ## Věta 1: přesná redukce -/

def quotObs {X A Y : Type*} (S : Sys X A Y) : Quotient (behSetoid S) → Y :=
  Quotient.lift S.obs (fun _ _ h => h [])

def quotStep {X A Y : Type*} (S : Sys X A Y) (a : A) :
    Quotient (behSetoid S) → Quotient (behSetoid S) :=
  Quotient.lift (fun x => Quotient.mk (behSetoid S) (S.step a x))
    (fun _ _ h => Quotient.sound (fun w => h (a :: w)))

theorem quotObs_mk {X A Y : Type*} (S : Sys X A Y) (x : X) :
    quotObs S (Quotient.mk (behSetoid S) x) = S.obs x :=
  rfl

theorem quotStep_mk {X A Y : Type*} (S : Sys X A Y) (a : A) (x : X) :
    quotStep S a (Quotient.mk (behSetoid S) x) =
      Quotient.mk (behSetoid S) (S.step a x) :=
  rfl

theorem quotStep_unique {X A Y : Type*} (S : Sys X A Y) (a : A)
    (F : Quotient (behSetoid S) → Quotient (behSetoid S))
    (hF : ∀ x, F (Quotient.mk (behSetoid S) x) =
      Quotient.mk (behSetoid S) (S.step a x)) :
    F = quotStep S a := by
  funext q
  refine Quotient.inductionOn q (fun x => ?_)
  rw [hF, quotStep_mk]

theorem quotObs_unique {X A Y : Type*} (S : Sys X A Y)
    (O : Quotient (behSetoid S) → Y)
    (hO : ∀ x, O (Quotient.mk (behSetoid S) x) = S.obs x) :
    O = quotObs S := by
  funext q
  refine Quotient.inductionOn q (fun x => ?_)
  rw [hO, quotObs_mk]

/-! ## Tři významy klidu -/

def RealRest {X A Y : Type*} (S : Sys X A Y) (x : X) : Prop :=
  ∀ a, S.step a x = x

def ObsRest {X A Y : Type*} (S : Sys X A Y) (x : X) : Prop :=
  ∀ a, Beh S (S.step a x) x

def InstAgree {X A Y : Type*} (S : Sys X A Y) (x : X) : Prop :=
  ∀ a, S.obs (S.step a x) = S.obs x

theorem realRest_obsRest {X A Y : Type*} (S : Sys X A Y) {x : X}
    (h : RealRest S x) : ObsRest S x := by
  intro a w
  rw [h a]

theorem obsRest_instAgree {X A Y : Type*} (S : Sys X A Y) {x : X}
    (h : ObsRest S x) : InstAgree S x := by
  intro a
  exact h a []

/-- Okamžitá shoda bez pozorovatelného klidu. -/
inductive Z3 where
  | x
  | y
  | z
  deriving DecidableEq

def zSys : Sys Z3 Unit Bool where
  step := fun _ s =>
    match s with
    | .x => .y
    | .y => .z
    | .z => .z
  obs := fun s =>
    match s with
    | .x => false
    | .y => false
    | .z => true

theorem inst_not_obs : InstAgree zSys .x ∧ ¬ ObsRest zSys .x := by
  constructor
  · intro _
    rfl
  · intro h
    have hcontr := h () [()]
    simp [zSys, wordStep] at hcontr

/-! ## Věta 2 -/

theorem obsRest_const {X A Y : Type*} (S : Sys X A Y) {x : X}
    (h : ObsRest S x) : ∀ w, S.obs (wordStep S.step w x) = S.obs x := by
  intro w
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [show wordStep S.step (a :: w) x = wordStep S.step w (S.step a x) from rfl]
    rw [h a w, ih]

theorem const_obsRest {X A Y : Type*} (S : Sys X A Y) {x : X}
    (h : ∀ w, S.obs (wordStep S.step w x) = S.obs x) : ObsRest S x := by
  intro a v
  rw [show wordStep S.step v (S.step a x) = wordStep S.step (a :: v) x from rfl]
  rw [h (a :: v), h v]

theorem obsRest_iff {X A Y : Type*} (S : Sys X A Y) (x : X) :
    ObsRest S x ↔ ∀ w, S.obs (wordStep S.step w x) = S.obs x :=
  ⟨fun h => obsRest_const S h, fun h => const_obsRest S h⟩

/-! ## Oddíl 4: živá skrytá souřadnice -/

def hiddenStep {M E A : Type*} (G : A → M → E → E) : A → M × E → M × E :=
  fun a p => (p.1, G a p.1 p.2)

def hiddenSys {M E A : Type*} (G : A → M → E → E) : Sys (M × E) A M where
  step := hiddenStep G
  obs := fun p => p.1

theorem hidden_obs_word {M E A : Type*} (G : A → M → E → E) :
    ∀ (w : List A) (m : M) (e : E),
      (hiddenSys G).obs (wordStep (hiddenSys G).step w (m, e)) = m := by
  intro w m e
  induction w generalizing e with
  | nil => rfl
  | cons a w ih =>
    exact ih (G a m e)

theorem hidden_same_visible {M E A : Type*} (G : A → M → E → E)
    (m : M) (e e' : E) : Beh (hiddenSys G) (m, e) (m, e') := by
  intro w
  rw [hidden_obs_word G w m e, hidden_obs_word G w m e']

theorem hidden_obsRest {M E A : Type*} (G : A → M → E → E) (m : M) (e : E) :
    ObsRest (hiddenSys G) (m, e) := by
  intro a
  exact hidden_same_visible G m (G a m e) e

def flipG : Unit → Unit → Bool → Bool := fun _ _ b => !b

theorem hidden_not_realRest (b : Bool) :
    ¬ RealRest (hiddenSys flipG) ((), b) := by
  intro h
  have hb := h ()
  cases b <;> cases hb

/-! ## Věta 3: víc zásahů, jemnější ekvivalence -/

def mapWord {A B : Type*} (f : A → B) : List A → List B :=
  List.map f

theorem wordStep_map {X A B : Type*} (step : B → X → X) (f : A → B) :
    ∀ (w : List A) (x : X),
      wordStep (fun a => step (f a)) w x = wordStep step (mapWord f w) x := by
  intro w x
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    exact ih (step (f a) x)

theorem beh_mono {X A B Y : Type*} (step : B → X → X) (obs : X → Y) (f : A → B)
    {x x' : X}
    (h : Beh (Sys.mk step obs) x x') :
    Beh (Sys.mk (fun a => step (f a)) obs) x x' := by
  intro w
  rw [wordStep_map step f w x, wordStep_map step f w x']
  exact h (mapWord f w)

/-- `false` je `F`, `true` je `R`. -/
def boxStep : Bool → Bool × Bool → Bool × Bool
  | false, p => (p.1, !p.2)
  | true, p => (p.2, p.1)

def sysF : Sys (Bool × Bool) Unit Bool where
  step := fun _ p => boxStep false p
  obs := fun p => p.1

def sysFR : Sys (Bool × Bool) Bool Bool where
  step := boxStep
  obs := fun p => p.1

theorem word_fst_F : ∀ (w : List Unit) (p : Bool × Bool),
    (wordStep sysF.step w p).1 = p.1 := by
  intro w p
  induction w generalizing p with
  | nil => rfl
  | cons _ w ih =>
    exact ih (sysF.step () p)

theorem beh_F : Beh sysF (false, false) (false, true) := by
  intro w
  have h1 := word_fst_F w (false, false)
  have h2 := word_fst_F w (false, true)
  calc
    sysF.obs (wordStep sysF.step w (false, false))
        = (wordStep sysF.step w (false, false)).1 := rfl
    _ = false := h1
    _ = (wordStep sysF.step w (false, true)).1 := h2.symm
    _ = sysF.obs (wordStep sysF.step w (false, true)) := rfl

theorem obsRest_F (p : Bool × Bool) : ObsRest sysF p := by
  rw [obsRest_iff]
  intro w
  calc
    sysF.obs (wordStep sysF.step w p) = (wordStep sysF.step w p).1 := rfl
    _ = p.1 := word_fst_F w p
    _ = sysF.obs p := rfl

theorem not_beh_FR : ¬ Beh sysFR (false, false) (false, true) := by
  intro h
  have hcontr := h [true]
  simp [sysFR, boxStep, wordStep] at hcontr

/-! ## Nosičová cena: klid má cenu 0, odkrytí potřebuje dvě semínka -/

/-- Pod samotným `F` je každý výstup roven počáteční první souřadnici. -/
theorem f_transcript_constant (p : Bool × Bool) (w : List Unit) :
    sysF.obs (wordStep sysF.step w p) = p.1 :=
  word_fst_F w p

/-- Jedno konstantní semínko realizuje transkript, který je stále `false`. -/
def decodeFrozen : Unit → Bool := fun _ => false

theorem decodeFrozen_ok :
    decodeFrozen () = sysF.obs (wordStep sysF.step [()] (false, true)) := by
  rw [f_transcript_constant]
  rfl

/-- Po `R` první výstup oddělí obě hodnoty skrytého bitu. -/
theorem reveal_separates :
    sysFR.obs (wordStep sysFR.step [true] (false, false)) = false ∧
      sysFR.obs (wordStep sysFR.step [true] (false, true)) = true := by
  constructor <;> rfl

theorem no_singleton_reveal (d : Unit → Bool) : ¬ Function.Surjective d := by
  intro h
  rcases h false with ⟨_, hf⟩
  rcases h true with ⟨_, ht⟩
  have : d () = false ∧ d () = true := by
    constructor
    · simpa using hf
    · simpa using ht
  rcases this with ⟨h1, h2⟩
  rw [h1] at h2
  cases h2

def decodeReveal : Bool → Bool := id

theorem decodeReveal_surjective : Function.Surjective decodeReveal :=
  fun b => ⟨b, rfl⟩

/-! ## Věta 8, nosičová forma: výběr `n` cílů potřebuje aspoň `n` řízení. -/

theorem selection_support {k n : Nat} (f : Fin k → Fin n)
    (hf : Function.Surjective f) : n ≤ k := by
  simpa using Fintype.card_le_of_surjective f hf

end RelativeRest
