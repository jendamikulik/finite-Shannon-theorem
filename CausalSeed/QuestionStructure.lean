/-
Finite pieces of "Questions, Structure, and Causal Simulation".

Proved here, with no `sorry`:
* an observable response map factors bijectively through its quotient, refinements
  of the question set are surjective on classes, and no questions give one class;
* future observations are the largest transition congruence, the quotient is the
  smallest exact deterministic image, observation-based policies have the same
  transcripts there, and on a finite nonempty state set the word-length
  refinement stabilizes after at most `|S| - 1` strict steps;
* a one-step counterexample where equal present observations are not a congruence;
* reachability forces transition invariants to agree, universal reachability makes
  them constant, and a sink shows the converse fails;
* reachability descends to the behavioral quotient;
* there is one map out of the empty set and it has empty image, while maps out of
  a singleton are elements;
* no point of a two-element set is fixed by every bijection;
* a permutation-invariant probability on a finite set is uniform, a deterministic
  seed of that law has entropy at least `log₂ n`, and no summable real law on `ℕ`
  is invariant under every permutation;
* generating from the empty set stays empty, while an explicit source set does not;
* an independent finite product seed has the prescribed coordinate marginals;
* exact selection of `n` targets needs at least `n` control transcripts;
* a hidden state extension does not change observation transcripts of an
  observation-based policy.

Not proved here: adaptive transcript laws for a lumpable stochastic kernel,
agreement of infinite-horizon seed existence or atomic capacity, and Fano's
inequality for inexact target selection.
-/
import CausalSeed.Identity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Relation
import Mathlib.Basic.Unique
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order

noncomputable section

open Classical Function
open scoped BigOperators

namespace QuestionStructure

/-! ### Observable quotient -/

variable {Ω Q : Type*} {Y : Q → Type*}

def resp (A : (q : Q) → Ω → Y q) (x : Ω) : (q : Q) → Y q := fun q => A q x

def obsSetoid (A : (q : Q) → Ω → Y q) : Setoid Ω where
  r x x' := resp A x = resp A x'
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def obsClass (A : (q : Q) → Ω → Y q) : Quotient (obsSetoid A) → (q : Q) → Y q :=
  Quotient.lift (resp A) fun _ _ h => h

theorem obsClass_injective (A : (q : Q) → Ω → Y q) : Injective (obsClass A) := by
  intro q q' h
  induction q using Quotient.inductionOn with
  | h x =>
    induction q' using Quotient.inductionOn with
    | h x' =>
      exact Quotient.sound h

theorem obsClass_image (A : (q : Q) → Ω → Y q) (q : Quotient (obsSetoid A)) :
    obsClass A q ∈ Set.range (resp A) := by
  induction q using Quotient.inductionOn with
  | h x => exact ⟨x, rfl⟩

theorem obs_factor {Z : Type*} (A : (q : Q) → Ω → Y q) (f : Ω → Z)
    (hf : ∀ x x', resp A x = resp A x' → f x = f x') :
    ∃! fbar : Quotient (obsSetoid A) → Z, ∀ x, fbar (Quotient.mk _ x) = f x := by
  refine ⟨Quotient.lift f hf, fun _ => rfl, ?_⟩
  intro fbar' hbar
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact hbar x

def restrict {Q' : Type*} {Y' : Q' → Type*} (ι : Q → Q')
    (A' : (q' : Q') → Ω → Y' q') : (q : Q) → Ω → Y' (ι q) :=
  fun q x => A' (ι q) x

theorem restrict_agrees {Q' : Type*} {Y' : Q' → Type*} (ι : Q → Q')
    (A' : (q' : Q') → Ω → Y' q') {x x' : Ω} (h : resp A' x = resp A' x') :
    resp (restrict ι A') x = resp (restrict ι A') x' := by
  funext q
  exact congrFun h (ι q)

def quotientRefine {Q' : Type*} {Y' : Q' → Type*} (ι : Q → Q')
    (A' : (q' : Q') → Ω → Y' q') :
    Quotient (obsSetoid A') → Quotient (obsSetoid (restrict ι A')) :=
  Quotient.lift (fun x => Quotient.mk _ x) fun _ _ h =>
    Quotient.sound (restrict_agrees ι A' h)

theorem quotientRefine_surjective {Q' : Type*} {Y' : Q' → Type*} (ι : Q → Q')
    (A' : (q' : Q') → Ω → Y' q') : Surjective (quotientRefine ι A') := by
  intro q
  induction q using Quotient.inductionOn with
  | h x => exact ⟨Quotient.mk _ x, rfl⟩

theorem separates_iff_injective (A : (q : Q) → Ω → Y q) :
    Injective (resp A) ↔ ∀ x x', resp A x = resp A x' → x = x' := Iff.rfl

theorem empty_questions_agree [IsEmpty Q] (A : (q : Q) → Ω → Y q) (x x' : Ω) :
    resp A x = resp A x' := by
  funext q
  exact isEmptyElim q

set_option warn.classDefReducibility false in
noncomputable def empty_questions_unique [IsEmpty Q] [Nonempty Ω] (A : (q : Q) → Ω → Y q) :
    Unique (Quotient (obsSetoid A)) := by
  inhabit Ω
  refine ⟨⟨Quotient.mk _ default⟩, ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | h x => exact Quotient.sound (empty_questions_agree A x default)

/-! ### Behavioral quotient -/

variable {S Act Y : Type*}

def run (F : Act → S → S) : List Act → S → S
  | [], s => s
  | a :: w, s => run F w (F a s)

def BehavRel (o : S → Y) (F : Act → S → S) (s s' : S) : Prop :=
  ∀ w, o (run F w s) = o (run F w s')

def behavSetoid (o : S → Y) (F : Act → S → S) : Setoid S where
  r := BehavRel o F
  iseqv := ⟨fun _ _ => rfl, fun h w => (h w).symm, fun h₁ h₂ w => (h₁ w).trans (h₂ w)⟩

theorem behav_succ {o : S → Y} {F : Act → S → S} {s s' : S}
    (h : BehavRel o F s s') (a : Act) : BehavRel o F (F a s) (F a s') := by
  intro w
  simpa [run] using h (a :: w)

theorem behav_present {o : S → Y} {F : Act → S → S} {s s' : S}
    (h : BehavRel o F s s') : o s = o s' := by
  simpa [run] using h []

def barO (o : S → Y) (F : Act → S → S) : Quotient (behavSetoid o F) → Y :=
  Quotient.lift o fun _ _ h => behav_present h

def barF (o : S → Y) (F : Act → S → S) (a : Act) :
    Quotient (behavSetoid o F) → Quotient (behavSetoid o F) :=
  Quotient.lift (fun s => Quotient.mk _ (F a s)) fun _ _ h => Quotient.sound (behav_succ h a)

structure ObsCong (o : S → Y) (F : Act → S → S) (R : S → S → Prop) : Prop where
  refl : ∀ s, R s s
  symm : ∀ {s s'}, R s s' → R s' s
  trans : ∀ {s t u}, R s t → R t u → R s u
  obs : ∀ {s s'}, R s s' → o s = o s'
  next : ∀ a {s s'}, R s s' → R (F a s) (F a s')

theorem behav_largest {o : S → Y} {F : Act → S → S} {R : S → S → Prop}
    (hR : ObsCong o F R) {s s' : S} (hrs : R s s') : BehavRel o F s s' := by
  intro w
  induction w generalizing s s' with
  | nil => simpa [run] using hR.obs hrs
  | cons a w ih => simpa [run] using ih (hR.next a hrs)

theorem behav_is_cong (o : S → Y) (F : Act → S → S) :
    ObsCong o F (BehavRel o F) := by
  refine ⟨fun _ _ => rfl, fun h w => (h w).symm, fun h₁ h₂ w => (h₁ w).trans (h₂ w), ?_, ?_⟩
  · intro s s' h
    exact behav_present h
  · intro a s s' h
    exact behav_succ h a

theorem run_hom {N : Type*} (F : Act → S → S) (G : Act → N → N) (e : S → N)
    (hcomm : ∀ a s, e (F a s) = G a (e s)) :
    ∀ w s, e (run F w s) = run G w (e s) := by
  intro w s
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih => simp [run, hcomm, ih]

theorem hom_preserves_behav {N : Type*} (o : S → Y) (F : Act → S → S)
    (g : N → Y) (G : Act → N → N) (e : S → N)
    (ho : ∀ s, o s = g (e s)) (hcomm : ∀ a s, e (F a s) = G a (e s))
    {s s' : S} (h : e s = e s') : BehavRel o F s s' := by
  intro w
  calc
    o (run F w s) = g (e (run F w s)) := ho _
    _ = g (run G w (e s)) := by rw [run_hom F G e hcomm]
    _ = g (run G w (e s')) := by rw [h]
    _ = g (e (run F w s')) := by rw [run_hom F G e hcomm]
    _ = o (run F w s') := (ho _).symm

noncomputable def behavFactor {N : Type*} (o : S → Y) (F : Act → S → S)
    (e : S → N) (he : Surjective e) (n : N) : Quotient (behavSetoid o F) :=
  Quotient.mk _ (Classical.choose (he n))

theorem behavFactor_apply {N : Type*} (o : S → Y) (F : Act → S → S)
    (g : N → Y) (G : Act → N → N) (e : S → N) (he : Surjective e)
    (ho : ∀ s, o s = g (e s)) (hcomm : ∀ a s, e (F a s) = G a (e s)) (s : S) :
    behavFactor o F e he (e s) = Quotient.mk _ s := by
  apply Quotient.sound
  exact hom_preserves_behav o F g G e ho hcomm (Classical.choose_spec (he (e s)))

theorem behavFactor_unique {N : Type*} (o : S → Y) (F : Act → S → S)
    (e : S → N) (he : Surjective e) (r : N → Quotient (behavSetoid o F))
    (hr : ∀ s, r (e s) = Quotient.mk (behavSetoid o F) s) (n : N) :
    r n = behavFactor o F e he n := by
  calc
    r n = r (e (Classical.choose (he n))) :=
      congrArg r (Classical.choose_spec (he n)).symm
    _ = Quotient.mk (behavSetoid o F) (Classical.choose (he n)) := hr _
    _ = behavFactor o F e he n := by simp [behavFactor]

theorem behavFactor_surjective {N : Type*} (o : S → Y) (F : Act → S → S)
    (g : N → Y) (G : Act → N → N) (e : S → N) (he : Surjective e)
    (ho : ∀ s, o s = g (e s)) (hcomm : ∀ a s, e (F a s) = G a (e s)) :
    Surjective (behavFactor o F e he) := by
  intro q
  induction q using Quotient.inductionOn with
  | h s => exact ⟨e s, behavFactor_apply o F g G e he ho hcomm s⟩

theorem behavFactor_obs {N : Type*} (o : S → Y) (F : Act → S → S)
    (g : N → Y) (e : S → N) (he : Surjective e)
    (ho : ∀ s, o s = g (e s)) (n : N) :
    barO o F (behavFactor o F e he n) = g n := by
  rw [behavFactor]
  change o (Classical.choose (he n)) = g n
  rw [ho, Classical.choose_spec (he n)]

theorem behavFactor_trans {N : Type*} (o : S → Y) (F : Act → S → S)
    (g : N → Y) (G : Act → N → N) (e : S → N) (he : Surjective e)
    (ho : ∀ s, o s = g (e s)) (hcomm : ∀ a s, e (F a s) = G a (e s))
    (a : Act) (n : N) :
    behavFactor o F e he (G a n) = barF o F a (behavFactor o F e he n) := by
  apply Quotient.sound
  exact hom_preserves_behav o F g G e ho hcomm <| by
    rw [Classical.choose_spec (he (G a n)), hcomm, Classical.choose_spec (he n)]

theorem behav_natCard_le {N : Type*} [Finite N] (o : S → Y) (F : Act → S → S)
    (g : N → Y) (G : Act → N → N) (e : S → N) (he : Surjective e)
    (ho : ∀ s, o s = g (e s)) (hcomm : ∀ a s, e (F a s) = G a (e s)) :
    Nat.card (Quotient (behavSetoid o F)) ≤ Nat.card N :=
  Nat.card_le_card_of_surjective (behavFactor o F e he)
    (behavFactor_surjective o F g G e he ho hcomm)

/-- Observation transcript of an observation-based policy. The policy reads the
observations already produced, including the observation at the current state. -/
def rollout (o : S → Y) (F : Act → S → S) (π : List Y → Act) :
    ℕ → List Y → S → List Y
  | 0, _, _ => []
  | n + 1, hist, s =>
      let y := o s
      y :: rollout o F π n (hist ++ [y]) (F (π (hist ++ [y])) s)

theorem rollout_behav (o : S → Y) (F : Act → S → S) (π : List Y → Act) :
    ∀ n hist {s s' : S}, BehavRel o F s s' →
      rollout o F π n hist s = rollout o F π n hist s' := by
  intro n
  induction n with
  | zero => intro _ _ _ _; rfl
  | succ n ih =>
    intro hist s s' h
    rw [rollout, rollout, behav_present h]
    exact congrArg (o s' :: ·)
      (ih (hist ++ [o s']) (behav_succ h (π (hist ++ [o s']))))

theorem rollout_quotient (o : S → Y) (F : Act → S → S) (π : List Y → Act) :
    ∀ n hist s,
      rollout (barO o F) (barF o F) π n hist (Quotient.mk (behavSetoid o F) s) =
        rollout o F π n hist s := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hist s
    have hy : barO o F (Quotient.mk (behavSetoid o F) s) = o s := rfl
    rw [rollout, rollout, hy]
    have hstep : barF o F (π (hist ++ [o s])) (Quotient.mk (behavSetoid o F) s) =
        Quotient.mk (behavSetoid o F) (F (π (hist ++ [o s])) s) := rfl
    rw [hstep]
    exact congrArg (o s :: ·) (ih (hist ++ [o s]) _)

/-! ### Finite word-length refinement -/

def refineRel (o : S → Y) (F : Act → S → S) : ℕ → S → S → Prop
  | 0, s, s' => o s = o s'
  | k + 1, s, s' =>
      refineRel o F k s s' ∧ ∀ a, refineRel o F k (F a s) (F a s')

noncomputable instance refineRel.decidableRel (o : S → Y) (F : Act → S → S) (k : ℕ) :
    DecidableRel (refineRel o F k) :=
  fun _ _ => Classical.propDecidable _

theorem refineRel_equivalence (o : S → Y) (F : Act → S → S) (k : ℕ) :
    Equivalence (refineRel o F k) := by
  induction k with
  | zero =>
    exact ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  | succ k ih =>
    exact ⟨fun s => ⟨ih.refl s, fun a => ih.refl (F a s)⟩,
      fun h => ⟨ih.symm h.1, fun a => ih.symm (h.2 a)⟩,
      fun h₁ h₂ => ⟨ih.trans h₁.1 h₂.1, fun a => ih.trans (h₁.2 a) (h₂.2 a)⟩⟩

def refineSetoid (o : S → Y) (F : Act → S → S) (k : ℕ) : Setoid S where
  r := refineRel o F k
  iseqv := refineRel_equivalence o F k

theorem refineRel_word (o : S → Y) (F : Act → S → S) :
    ∀ k s s', refineRel o F k s s' ↔
      ∀ w, w.length ≤ k → o (run F w s) = o (run F w s') := by
  intro k
  induction k with
  | zero =>
    intro s s'
    constructor
    · intro h w hw
      have hw0 : w.length = 0 := Nat.eq_zero_of_le_zero hw
      have : w = [] := List.length_eq_zero_iff.mp hw0
      subst this
      change o s = o s' at h
      simpa [run] using h
    · intro h
      change o s = o s'
      simpa [run] using h [] (Nat.zero_le _)
  | succ k ih =>
    intro s s'
    constructor
    · intro h w hw
      cases w with
      | nil =>
        have h0 := (ih s s').1 h.1
        simpa [run] using h0 [] (Nat.zero_le _)
      | cons a w =>
        have hw' : w.length ≤ k := by
          simp only [List.length_cons] at hw
          exact Nat.le_of_succ_le_succ hw
        have hs := (ih (F a s) (F a s')).1 (h.2 a)
        simpa [run] using hs w hw'
    · intro h
      refine ⟨(ih s s').2 fun w hw => h w (hw.trans (Nat.le_succ k)), fun a => ?_⟩
      exact (ih (F a s) (F a s')).2 fun w hw => by
        simpa [run] using h (a :: w) (Nat.succ_le_succ hw)

theorem refineRel_shift (o : S → Y) (F : Act → S → S) (k n : ℕ)
    (hstable : ∀ s s', refineRel o F (k + 1) s s' ↔ refineRel o F k s s') (s s' : S) :
    refineRel o F (k + n + 1) s s' ↔ refineRel o F (k + n) s s' := by
  induction n generalizing s s' with
  | zero => simpa using hstable s s'
  | succ n ih =>
    constructor
    · intro h
      exact h.1
    · intro h
      refine ⟨h, fun a => (ih (F a s) (F a s')).2 (h.2 a)⟩

theorem refineRel_stable_all (o : S → Y) (F : Act → S → S) (k n : ℕ)
    (hstable : ∀ s s', refineRel o F (k + 1) s s' ↔ refineRel o F k s s') (s s' : S) :
    refineRel o F (k + n) s s' ↔ refineRel o F k s s' := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc refineRel o F (k + n + 1) s s'
        ↔ refineRel o F (k + n) s s' := refineRel_shift o F k n hstable s s'
      _ ↔ refineRel o F k s s' := ih

theorem stable_eq_behav (o : S → Y) (F : Act → S → S) (k : ℕ)
    (hstable : ∀ s s', refineRel o F (k + 1) s s' ↔ refineRel o F k s s') (s s' : S) :
    refineRel o F k s s' ↔ BehavRel o F s s' := by
  constructor
  · intro hr w
    have hlen : refineRel o F (k + w.length) s s' :=
      (refineRel_stable_all o F k w.length hstable s s').2 hr
    exact ((refineRel_word o F) (k + w.length) s s').1 hlen w (Nat.le_add_left _ _)
  · intro hb
    exact ((refineRel_word o F) k s s').2 fun w _ => hb w

def refineStep (o : S → Y) (F : Act → S → S) (k : ℕ) :
    Quotient (refineSetoid o F (k + 1)) → Quotient (refineSetoid o F k) :=
  Quotient.lift (fun s => Quotient.mk (refineSetoid o F k) s) fun _ _ h =>
    Quotient.sound h.1

theorem refineStep_surjective (o : S → Y) (F : Act → S → S) (k : ℕ) :
    Surjective (refineStep o F k) := by
  intro q
  induction q using Quotient.inductionOn with
  | h s => exact ⟨Quotient.mk _ s, rfl⟩

theorem refineRel_of_step_injective (o : S → Y) (F : Act → S → S) (k : ℕ)
    (hinj : Injective (refineStep o F k)) {s s' : S} (h : refineRel o F k s s') :
    refineRel o F (k + 1) s s' := by
  have hmk : refineStep o F k (Quotient.mk _ s) = refineStep o F k (Quotient.mk _ s') := by
    change Quotient.mk (refineSetoid o F k) s = Quotient.mk (refineSetoid o F k) s'
    exact Quotient.sound h
  exact Quotient.exact (hinj hmk)

theorem card_refine_strict [Fintype S] (o : S → Y) (F : Act → S → S) (k : ℕ)
    (hneq : ¬ ∀ s s', refineRel o F (k + 1) s s' ↔ refineRel o F k s s') :
    Nat.card (Quotient (refineSetoid o F k)) <
      Nat.card (Quotient (refineSetoid o F (k + 1))) := by
  have hle := Nat.card_le_card_of_surjective (refineStep o F k) (refineStep_surjective o F k)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    apply hneq
    have hbij : Bijective (refineStep o F k) :=
      (Nat.bijective_iff_surjective_and_card (refineStep o F k)).2
        ⟨refineStep_surjective o F k, heq.symm⟩
    intro s s'
    constructor
    · exact fun h => h.1
    · exact refineRel_of_step_injective o F k hbij.1

theorem card_refine_add [Fintype S] (o : S → Y) (F : Act → S → S) (n : ℕ)
    (h : ∀ k, k < n → Nat.card (Quotient (refineSetoid o F k)) <
      Nat.card (Quotient (refineSetoid o F (k + 1)))) :
    Nat.card (Quotient (refineSetoid o F 0)) + n ≤
      Nat.card (Quotient (refineSetoid o F n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt := h n (Nat.lt_succ_self n)
    have hbase := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hstep : Nat.card (Quotient (refineSetoid o F n)) + 1 ≤
        Nat.card (Quotient (refineSetoid o F (n + 1))) := Nat.succ_le_of_lt hlt
    calc Nat.card (Quotient (refineSetoid o F 0)) + (n + 1)
        = Nat.card (Quotient (refineSetoid o F 0)) + n + 1 := by omega
      _ ≤ Nat.card (Quotient (refineSetoid o F n)) + 1 := Nat.add_le_add_right hbase 1
      _ ≤ Nat.card (Quotient (refineSetoid o F (n + 1))) := hstep

/-- On a finite nonempty state set, equality of responses to words of length at
most `k` agrees with behavioral equivalence for some `k < |S|`. That is at most
`|S| - 1` strict refinements. -/
theorem refine_stabilizes [Fintype S] [Nonempty S] (o : S → Y) (F : Act → S → S) :
    ∃ k, k < Fintype.card S ∧
      ∀ s s', refineRel o F k s s' ↔ BehavRel o F s s' := by
  have hexists : ∃ k, k < Fintype.card S ∧
      ∀ s s', refineRel o F (k + 1) s s' ↔ refineRel o F k s s' := by
    by_contra hnone
    have hneq : ∀ k, k < Fintype.card S →
        ¬ ∀ s s', refineRel o F (k + 1) s s' ↔ refineRel o F k s s' := by
      intro k hk hrel
      exact hnone ⟨k, hk, hrel⟩
    have hstrict : ∀ k, k < Fintype.card S →
        Nat.card (Quotient (refineSetoid o F k)) <
          Nat.card (Quotient (refineSetoid o F (k + 1))) :=
      fun k hk => card_refine_strict o F k (hneq k hk)
    have hgrow := card_refine_add o F (Fintype.card S) hstrict
    have hne : Nonempty (Quotient (refineSetoid o F 0)) :=
      ⟨Quotient.mk _ (Classical.choice (inferInstance : Nonempty S))⟩
    have hpos : 0 < Nat.card (Quotient (refineSetoid o F 0)) :=
      @Nat.card_pos _ hne _
    have hQle : Nat.card (Quotient (refineSetoid o F (Fintype.card S))) ≤ Fintype.card S := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_quotient_le (refineSetoid o F (Fintype.card S))
    have hlt : Fintype.card S <
        Nat.card (Quotient (refineSetoid o F 0)) + Fintype.card S :=
      Nat.lt_add_of_pos_left hpos
    exact lt_irrefl _ ((hlt.trans_le (hgrow.trans hQle)))
  obtain ⟨k, hk, hstable⟩ := hexists
  exact ⟨k, hk, fun s s' => stable_eq_behav o F k hstable s s'⟩

/-! ### Present responses need not be a congruence -/

namespace PresentNotCong

def o : Fin 3 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1

def F : Unit → Fin 3 → Fin 3
  | _, 0 => 0
  | _, 1 => 2
  | _, 2 => 2

theorem present_agree : o 0 = o 1 := rfl

theorem one_step_disagree : o (F () 0) ≠ o (F () 1) := by
  decide

theorem not_behav : ¬ BehavRel o F 0 1 := by
  intro h
  have := h [()]
  simp [run, o, F] at this

end PresentNotCong

/-! ### Reachability and transition invariants -/

def Reach (F : Act → S → S) (x y : S) : Prop :=
  ∃ w : List Act, run F w x = y

def TransitionInv (F : Act → S → S) {V : Type*} (I : S → V) : Prop :=
  ∀ a s, I (F a s) = I s

def undirectedStep (F : Act → S → S) (x y : S) : Prop :=
  ∃ a, y = F a x ∨ x = F a y

theorem reach_inv {V : Type*} {F : Act → S → S} {I : S → V}
    (hI : TransitionInv F I) {x y : S} (h : Reach F x y) : I x = I y := by
  rcases h with ⟨w, hw⟩
  induction w generalizing x with
  | nil =>
    simp [run] at hw
    rw [hw]
  | cons a w ih =>
    exact (hI a x).symm.trans (ih (by simpa [run] using hw))

theorem universal_inv_const {V : Type*} {F : Act → S → S}
    (hU : ∀ x y : S, Reach F x y) {I : S → V} (hI : TransitionInv F I) (x y : S) :
    I x = I y :=
  reach_inv hI (hU x y)

theorem inv_iff_eqvGen {V : Type*} {F : Act → S → S} {I : S → V} :
    TransitionInv F I ↔
      ∀ x y, Relation.EqvGen (undirectedStep F) x y → I x = I y := by
  constructor
  · intro hI x y h
    induction h with
    | rel a b hab =>
      rcases hab with ⟨act, hab | hab⟩
      · rw [hab, hI]
      · rw [hab, hI]
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h a s
    exact (h s (F a s) (Relation.EqvGen.rel _ _ ⟨a, Or.inl rfl⟩)).symm

theorem reach_descends (o : S → Y) (F : Act → S → S)
    (hU : ∀ x y : S, Reach F x y) :
    ∀ x y : Quotient (behavSetoid o F), Reach (barF o F) x y := by
  intro x y
  induction x using Quotient.inductionOn with
  | h s =>
    induction y using Quotient.inductionOn with
    | h t =>
      obtain ⟨w, hw⟩ := hU s t
      refine ⟨w, ?_⟩
      have hrun : ∀ w s,
          run (barF o F) w (Quotient.mk (behavSetoid o F) s) =
            Quotient.mk (behavSetoid o F) (run F w s) := by
        intro w s
        induction w generalizing s with
        | nil => simp [run]
        | cons a w ih => simp [run, barF, ih]
      rw [hrun, hw]

namespace Sink

def F : Unit → Fin 2 → Fin 2 := fun _ _ => 1

theorem only_const {V : Type*} (I : Fin 2 → V) (hI : TransitionInv F I) : I 0 = I 1 := by
  simpa [F] using (hI () 0).symm

theorem not_reach : ¬ Reach F (1 : Fin 2) 0 := by
  intro ⟨w, hw⟩
  have hstay : ∀ w, run F w (1 : Fin 2) = 1 := by
    intro w
    induction w with
    | nil => rfl
    | cons _ w ih => simp [run, F, ih]
  rw [hstay w] at hw
  exact absurd hw (by decide : (1 : Fin 2) ≠ 0)

end Sink

namespace Collapse

/-- A constant observation and an empty action set collapse two unreachable
states to one universally reachable quotient state. -/
def o : Fin 2 → Unit := fun _ => ()

def F : Empty → Fin 2 → Fin 2 := fun a => a.elim

theorem behav (s s' : Fin 2) : BehavRel o F s s' := by
  intro w
  cases w with
  | nil => rfl
  | cons a _ => exact a.elim

theorem not_reach : ¬ Reach F (0 : Fin 2) 1 := by
  intro ⟨w, hw⟩
  cases w with
  | nil => simp [run] at hw
  | cons a _ => exact a.elim

theorem quotient_reachable :
    ∀ q q' : Quotient (behavSetoid o F), Reach (barF o F) q q' := by
  intro q q'
  have hq : q = Quotient.mk (behavSetoid o F) 0 := by
    induction q using Quotient.inductionOn with
    | h s => exact Quotient.sound (behav s 0)
  have hq' : q' = Quotient.mk (behavSetoid o F) 0 := by
    induction q' using Quotient.inductionOn with
    | h s => exact Quotient.sound (behav s 0)
  refine ⟨[], ?_⟩
  simp [run, hq, hq']

end Collapse

/-! ### Exact selection, support half only -/

theorem exact_selection_bound {A : Type*} [Finite A] {n K : ℕ}
    (f : A → Fin n) (hf : Surjective f) (hK : Nat.card A ≤ K) : n ≤ K := by
  exact (Nat.card_fin n ▸ Nat.card_le_card_of_surjective f hf).trans hK

/-- Complete one-step control: the action names the target. -/
def ctrlF {N : Type*} : N → N → N := fun a _ => a

theorem ctrl_reaches {N : Type*} (x y : N) : Reach ctrlF x y :=
  ⟨[y], by simp [run, ctrlF]⟩

/-! ### Empty input, singleton input, and symmetry -/

set_option warn.classDefReducibility false in
def unique_from_empty (S : Type*) : Unique (Empty → S) where
  default := fun e => e.elim
  uniq := fun _ => funext fun e => e.elim

theorem range_from_empty (S : Type*) (f : Empty → S) : Set.range f = ∅ := by
  ext x
  constructor
  · intro ⟨e, _⟩
    exact e.elim
  · intro hx
    exact hx.elim

def unit_arrow_equiv (S : Type*) : (Unit → S) ≃ S where
  toFun f := f ()
  invFun s := fun _ => s
  left_inv f := funext fun u => by cases u; rfl
  right_inv _ := rfl

theorem swap_moves (c : Fin 2) : Equiv.swap (0 : Fin 2) 1 c ≠ c := by
  revert c
  decide

/-- No choice of a point in every nonempty type is fixed by every bijection. -/
structure EquivariantPoint where
  c : (S : Type) → [Nonempty S] → S
  equivariant : ∀ {S T : Type} [Nonempty S] [Nonempty T] (f : S ≃ T), f (c S) = c T

theorem no_equivariant_point : IsEmpty EquivariantPoint :=
  ⟨fun pc => swap_moves (pc.c (Fin 2)) (pc.equivariant (Equiv.swap (0 : Fin 2) 1))⟩

theorem perm_invariant_uniform {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hperm : ∀ (e : Fin n ≃ Fin n) (i : Fin n), p (e i) = p i)
    (hsum : ∑ i, p i = 1) (i : Fin n) : p i = 1 / (n : ℝ) := by
  let z : Fin n := ⟨0, hn⟩
  have hconst : ∀ i j : Fin n, p i = p j := by
    intro i j
    have := hperm (Equiv.swap i j) i
    simpa [Equiv.swap_apply_left] using this.symm
  have hsum0 : ∑ j : Fin n, p j = ∑ _ : Fin n, p z := by
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hconst j z
  have hmul : (n : ℝ) * p z = 1 := by
    rw [hsum0] at hsum
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using hsum
  have hpz : p z = 1 / (n : ℝ) := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [eq_div_iff hn0, mul_comm]
    exact hmul
  rw [hconst i z, hpz]

theorem uniform_entropy {n : ℕ} (hn : 0 < n) :
    CausalSpectrum.pmfEntropy (fun _ : Fin n => (1 : ℝ) / n) = Real.logb 2 n := by
  unfold CausalSpectrum.pmfEntropy
  have hpos : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hn)
  rw [Finset.sum_congr rfl fun _ _ => CausalSpectrum.entTerm_of_pos hpos]
  simp only [CausalSpectrum.infoMass]
  have hlog : (1 / (n : ℝ)) * -Real.logb 2 (1 / (n : ℝ)) =
      (1 / (n : ℝ)) * Real.logb 2 (n : ℝ) := by
    congr 1
    rw [Real.logb_div one_ne_zero (Nat.cast_ne_zero.mpr hn.ne'), Real.logb_one, zero_sub, neg_neg]
  simp only [hlog]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn0]

/-- A deterministic pushforward of a nonnegative seed onto the uniform law on
`Fin n` has entropy at least `log₂ n`. The uniform law attains the bound. -/
theorem uniform_seed_entropy {α : Type} [Fintype α] {n : ℕ} (hn : 0 < n)
    (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (φ : α → Fin n)
    (hpush : ∀ b, (∑ a, if φ a = b then μ a else 0) = 1 / (n : ℝ)) :
    Real.logb 2 n ≤ CausalSpectrum.pmfEntropy μ := by
  have hpushEnt :
      CausalSpectrum.pmfEntropy (fun b : Fin n => ∑ a, if φ a = b then μ a else 0) =
        Real.logb 2 n := by
    have hfun : (fun b : Fin n => ∑ a, if φ a = b then μ a else 0) =
        fun _ => (1 : ℝ) / n := funext hpush
    rw [hfun]
    exact uniform_entropy hn
  exact hpushEnt.symm.trans_le (CausalSpectrum.pmfEntropy_push_le μ h0 φ)

theorem no_perm_invariant_nat (p : ℕ → ℝ) (hsum : Summable p) (ht : ∑' i, p i = 1)
    (hperm : ∀ (e : ℕ ≃ ℕ) (i : ℕ), p (e i) = p i) : False := by
  have heq : ∀ i j, p i = p j := by
    intro i j
    have := hperm (Equiv.swap i j) i
    simpa [Equiv.swap_apply_left] using this.symm
  by_cases hzero : p 0 = 0
  · have hfun : p = fun _ => (0 : ℝ) := funext fun i => (heq i 0).trans hzero
    rw [hfun] at ht
    exact zero_ne_one ((hasSum_zero.tsum_eq).symm.trans ht)
  · have hs : Summable (fun _ : ℕ => p 0) := by
      have : (fun _ : ℕ => p 0) = p := funext fun i => (heq i 0).symm
      simpa [this] using hsum
    have hfin : Finite ℕ := by
      rcases lt_trichotomy (p 0) 0 with hlt | heq0 | hgt
      · exact Finite.of_summable_const (neg_pos.mpr hlt) hs.neg
      · exact absurd heq0 hzero
      · exact Finite.of_summable_const hgt hs
    exact (inferInstance : Infinite ℕ).not_finite hfin

/-! ### Generation from the empty set -/

def relImage (R : S → S → Prop) (X : Set S) : Set S :=
  {y | ∃ x, x ∈ X ∧ R x y}

def iterFrom (R : S → S → Prop) : Set S → ℕ → Set S
  | X0, 0 => X0
  | X0, n + 1 => iterFrom R X0 n ∪ relImage R (iterFrom R X0 n)

theorem iterFrom_empty (R : S → S → Prop) (n : ℕ) : iterFrom R ∅ n = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterFrom, ih, relImage]

theorem source_appears (b : S) : b ∈ iterFrom (fun _ _ => False) ({b} : Set S) 0 := by
  simp [iterFrom]

/-! ### Independent finite product: coordinate marginals -/

theorem product_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (K : (i : ι) → β i → ℝ)
    (hK : ∀ i, ∑ z, K i z = 1) (i0 : ι) (y : β i0) :
    (∑ f : ∀ i, β i, if f i0 = y then ∏ i, K i (f i) else 0) = K i0 y := by
  classical
  let E := {j : ι // j ≠ i0}
  let pack : β i0 × (∀ j : E, β j) → ∀ i, β i :=
    fun p i => if h : i = i0 then h ▸ p.1 else p.2 ⟨i, h⟩
  let unpack : (∀ i, β i) → β i0 × (∀ j : E, β j) :=
    fun f => (f i0, fun j => f j)
  have left_inv (f : ∀ i, β i) : pack (unpack f) = f := by
    funext i
    by_cases hi : i = i0
    · subst hi
      simp [pack, unpack]
    · simp [pack, unpack, hi]
  have right_inv (p : β i0 × (∀ j : E, β j)) : unpack (pack p) = p := by
    refine Prod.ext ?_ ?_
    · unfold unpack pack
      dsimp
      rw [dite_eq_left rfl]
    · funext j
      unfold unpack pack
      dsimp
      rw [dite_eq_right j.2]
  let e : (∀ i, β i) ≃ β i0 × (∀ j : E, β j) :=
    ⟨unpack, pack, left_inv, right_inv⟩
  have hfst (x : β i0) (z : ∀ j : E, β j) : (e.symm (x, z)) i0 = x := by
    unfold e pack
    dsimp
    rw [dite_eq_left rfl]
  have hsnd (z : ∀ j : E, β j) (j : E) : (e.symm (y, z)) (j : ι) = z j := by
    unfold e pack
    dsimp
    rw [dite_eq_right j.2]
  have hsplit (f : ∀ i, β i) :
      (∏ i, K i (f i)) = K i0 (f i0) * ∏ j : E, K j (f j) := by
    have hmul := Finset.mul_prod_erase (Finset.univ : Finset ι)
      (fun i => K i (f i)) (Finset.mem_univ i0)
    rw [← hmul]
    congr 1
    exact Finset.prod_subtype ((Finset.univ : Finset ι).erase i0)
      (fun i => by simp [Finset.mem_erase]) (fun i => K i (f i))
  rw [← (Equiv.sum_comp e.symm fun f => if f i0 = y then ∏ i, K i (f i) else 0)]
  rw [Fintype.sum_prod_type]
  have hoff (x : β i0) (hx : x ≠ y) :
      (∑ z : ∀ j : E, β j,
        if (e.symm (x, z)) i0 = y then ∏ i, K i ((e.symm (x, z)) i) else 0) = 0 := by
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [hfst x z, hx]
  rw [Finset.sum_eq_single y (fun x _ hx => hoff x hx)
    (fun hx => (hx (Finset.mem_univ y)).elim)]
  have hterm (z : ∀ j : E, β j) :
      (∏ i, K i ((e.symm (y, z)) i)) = K i0 y * ∏ j : E, K j (z j) := by
    rw [hsplit (e.symm (y, z)), hfst y z]
    apply congrArg (fun t => K i0 y * t)
    refine Finset.prod_congr rfl fun j _ => ?_
    exact congrArg (K j) (hsnd z j)
  have hsummand (z : ∀ j : E, β j) :
      (if (e.symm (y, z)) i0 = y then ∏ i, K i ((e.symm (y, z)) i) else 0) =
        K i0 y * ∏ j : E, K j (z j) := by
    simp [hfst y z, hterm z]
  have hrest : (∑ z : ∀ j : E, β j, ∏ j : E, K j (z j)) = 1 := by
    have hprod := (Finset.prod_univ_sum (fun j : E => (Finset.univ : Finset (β j)))
      (fun j t => K j t)).symm
    rw [Fintype.piFinset_univ] at hprod
    rw [hprod]
    simp [hK]
  rw [Finset.sum_congr rfl fun z _ => hsummand z, ← Finset.mul_sum, hrest, mul_one]

/-! ### Hidden extension -/

def extF {E : Type*} (F : Act → S → S) (G : Act → S → E → E) :
    Act → S × E → S × E :=
  fun a p => (F a p.1, G a p.1 p.2)

def extO {E : Type*} (o : S → Y) : S × E → Y :=
  fun p => o p.1

theorem hidden_extension_transcript {E : Type*} (o : S → Y) (F : Act → S → S)
    (G : Act → S → E → E) (π : List Y → Act) :
    ∀ n hist s e,
      rollout (extO o) (extF F G) π n hist (s, e) = rollout o F π n hist s := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro hist s e
    rw [rollout, rollout]
    exact congrArg (o s :: ·)
      (ih (hist ++ [o s]) (F (π (hist ++ [o s])) s) (G (π (hist ++ [o s])) s e))

end QuestionStructure
end
