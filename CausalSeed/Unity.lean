/-
UNITY: a conditional mathematical framework.

The note of 15 November 2026 joins components that are already proved
elsewhere in this library. Identification with consciousness, direct
mental control of outcomes, and external physical power are hypotheses.
They are not theorems here.

Proved here, with no sorry:

* three displayed phases lie on the unit circle;
* equal moduli do not force equal values, and a sum of unit values
  need not vanish;
* a trajectory that stays inside the offered set of a golden sphere
  remains in the care set (imported);
* `n` halvings cost `n · (m² / 2) · ln 2`;
* an additive information clock on dyadic depths is the bit count;
* the constant map `true` is idempotent, and that is only substitution;
* an internal charge and an external charge of the same total need
  not agree on where the cost is booked.

Not proved: Hypothesis 9. No identification of an intention with an
instrument, no external supplier, no control of an outcome.
-/
import Mathlib.Analysis.Complex.Exponential
import CausalSeed.GoldenSphere
import CausalSeed.RingEnergy

noncomputable section

open Real

namespace CausalSpectrum
namespace Unity

/-! ### Phases -/

/-- For real `θ`, `e^{iθ}` has modulus one. -/
theorem abs_exp_I (θ : ℝ) : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- The three phases of the note lie on the unit circle. -/
theorem phases_unit :
    let θ1 : ℝ := Real.pi
    let θ2 : ℝ := Real.exp 1 * Real.log Real.pi
    let θ3 : ℝ := Real.pi ^ 2 * Real.exp 1 / 2
    ‖Complex.exp (θ1 * Complex.I)‖ = 1 ∧
      ‖Complex.exp (θ2 * Complex.I)‖ = 1 ∧
        ‖Complex.exp (θ3 * Complex.I)‖ = 1 := by
  refine ⟨Complex.norm_exp_ofReal_mul_I _, Complex.norm_exp_ofReal_mul_I _,
    Complex.norm_exp_ofReal_mul_I _⟩

/-- Equal moduli do not force equal values. -/
theorem moduli_not_values :
    ‖(1 : ℂ)‖ = ‖(-1 : ℂ)‖ ∧ (1 : ℂ) ≠ -1 := by
  constructor
  · simp
  · norm_num

/-- A sum of three unit complex numbers need not vanish. -/
theorem unit_sum_not_always_zero :
    ‖(1 : ℂ)‖ = 1 ∧ (1 : ℂ) + 1 + 1 ≠ 0 := by
  constructor
  · simp
  · norm_num

/-! ### Golden sphere -/

/-- Theorem 2 of the note: an offered trajectory stays in the care set.
A permitted step exists exactly when a witness action is supplied:
opened by the wish, inside every consent boundary, landing in K.
See `GoldenSphere.step_exists_iff` and `GoldenSphere.run_step`.
The sphere does not produce the witness. -/
theorem stays {X Ω W N : Type*}
    (S : GoldenSphere.Sphere X Ω W N) (w : ℕ → W) (x : ℕ → X)
    (h0 : x 0 ∈ S.K) (hstep : ∀ t, x (t + 1) ∈ GoldenSphere.G S (w t) (x t)) :
    ∀ t, x t ∈ S.K :=
  GoldenSphere.stays_in_K S w x h0 hstep

/-- The missing premise, named. A step exists at `(w, x)` if and only if
some action is admissible and lands in the care set. -/
theorem step_iff {X Ω W N : Type*}
    (S : GoldenSphere.Sphere X Ω W N) (w : W) (x : X) :
    (∃ y, y ∈ GoldenSphere.G S w x) ↔
      ∃ a, a ∈ S.I w x ∧ (∀ i, a ∈ S.C i x) ∧ S.F x a ∈ S.K :=
  GoldenSphere.step_exists_iff S w x

/-! ### Rings -/

/-- `n` inward halvings from `R` cost exactly `n · (m² / 2) · ln 2`. -/
theorem n_halvings (m : ℝ) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    RingEnergy.E m (R / (2 : ℝ) ^ n) R =
      (n : ℝ) * (m ^ 2 / 2) * Real.log 2 := by
  unfold RingEnergy.E
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt hpow
  have hRne : R ≠ 0 := ne_of_gt hR
  have hratio : R / (R / (2 : ℝ) ^ n) = (2 : ℝ) ^ n := by field_simp
  rw [hratio, Real.log_pow]
  ring

/-- One off-`e` ring costs `m² / 2`, independently of the radius. -/
theorem off_e_ring (m : ℝ) {r : ℝ} (hr : 0 < r) :
    RingEnergy.E m r (Real.exp 1 * r) = m ^ 2 / 2 :=
  RingEnergy.off_e m hr

/-! ### Information clock on dyadic depth -/

/-- If `d` adds on depths and `d 1 = 1`, then `d` counts bits. -/
theorem info_clock (d : ℕ → ℝ) (hadd : ∀ n m, d (n + m) = d n + d m)
    (hone : d 1 = 1) : ∀ n, d n = (n : ℝ) := by
  intro n
  induction n with
  | zero =>
    have h : d 0 = d 0 + d 0 := by simpa [Nat.zero_add] using hadd 0 0
    have h2 : d 0 + 0 = d 0 + d 0 := by simpa using h.symm
    have : d 0 = (0 : ℝ) := (add_left_cancel h2).symm
    simpa using this
  | succ n ih =>
    have h := hadd n 1
    have h' : d (n + 1) = d n + d 1 := by simpa using h
    rw [h', ih, hone]
    simp

/-! ### The constant map is only substitution -/

/-- The map that always returns `true`. -/
def constantWill : Bool → Bool := fun _ => true

theorem constantWill_idem (x : Bool) :
    constantWill (constantWill x) = constantWill x := rfl

/-- Idempotence by substitution does not mention a physical carrier. -/
theorem constantWill_no_carrier (x : Bool) :
    constantWill x = true := rfl

/-! ### Where a cost is booked -/

/-- An account that charges `c` inside and nothing outside. -/
def internal (c : ℝ) : ℝ × ℝ := (c, 0)

/-- An account that charges `c` outside and nothing inside. -/
def external (c : ℝ) : ℝ × ℝ := (0, c)

theorem same_total (c : ℝ) :
    (internal c).1 + (internal c).2 = (external c).1 + (external c).2 := by
  simp [internal, external]

theorem charge_sits_elsewhere (c : ℝ) (hc : c ≠ 0) :
    (internal c).1 ≠ (external c).1 := by
  simp [internal, external, hc]

/-- A zero conditional reading entropy is a statement about a decoder.
It does not exhibit an external supplier. The ring limit is a real
divergence, not a wattage. The fateful form of Hypothesis 9 is stated
below and is not a theorem of this file. -/
theorem not_a_supplier : True := trivial

/-! ### Hypothesis 9, the fateful reading

Fate, if it were a theorem, would be an external supplier: a map that
writes the next state and thereby controls the outcome. Two readings
are not the same hypothesis.

* Inside the offer: the supplier may choose only from `G`. Then it is
  a picker. It still has to be supplied. Silence stays silence.
* Above consent: the supplier writes a state where some consent
  refuses. That is not a completion of the sphere. It deletes it.

Identifying the intention with the instrument would make the outcome
depend on the wish alone. Two nonempty offers under one wish can
demand two different states. The wish does not decide them.
An external booking of a cost is not such a supplier.
-/

/-- Hypothesis 9 in the form that still respects the sphere.
A supplier controls the next state only where an offer exists.
Nothing here constructs the supplier. -/
structure Fateful {X Ω W N : Type*} (S : GoldenSphere.Sphere X Ω W N) where
  supplier : W → X → X
  controls :
    ∀ w x, (GoldenSphere.G S w x).Nonempty →
      supplier w x ∈ GoldenSphere.G S w x

/-- A sphere that opens every action and refuses every consent. -/
def silentSphere : GoldenSphere.Sphere Unit Unit Unit Unit where
  I := fun _ _ => Set.univ
  F := fun _ a => a
  C := fun _ _ => ∅
  K := Set.univ

theorem silent_offer (w x : Unit) :
    GoldenSphere.G silentSphere w x = ∅ := by
  ext y
  constructor
  · rintro ⟨a, ha, _, _⟩
    exact (ha.2 ()).elim
  · intro hy
    exact hy.elim

/-- A fateful supplier does not fill a refusal. The controlled step
is never offered, because nothing is offered. -/
theorem fate_does_not_fill_silence (F : Fateful silentSphere) (w x : Unit) :
    F.supplier w x ∉ GoldenSphere.G silentSphere w x := by
  simpa [silent_offer] using (show F.supplier w x ∉ (∅ : Set Unit) from fun h => h.elim)

/-- Where a fateful supplier does control a step, the step lies in care.
Fate inside the offer does not leave `K`. -/
theorem fate_inside_stays {X Ω W N : Type*}
    (S : GoldenSphere.Sphere X Ω W N) (F : Fateful S) (w : W) (x : X)
    (h : (GoldenSphere.G S w x).Nonempty) :
    F.supplier w x ∈ S.K :=
  GoldenSphere.G_subset_K S w x (F.controls w x h)

/-- One wish, two required outcomes. The intention is not the instrument. -/
theorem intention_is_not_the_instrument :
    ¬ ∃ σ : Unit → Bool → Bool,
        σ () true = true ∧ σ () false = false ∧
          ∀ x, σ () x = σ () true := by
  intro ⟨σ, ht, hf, honly⟩
  have : false = true := hf.symm.trans ((honly false).trans ht)
  exact Bool.false_ne_true this

/-- Booking the same total outside does not exhibit a supplier. -/
theorem external_charge_is_not_a_supplier (c : ℝ) (hc : c ≠ 0) :
    (internal c).1 + (internal c).2 = (external c).1 + (external c).2 ∧
      (internal c).1 ≠ (external c).1 :=
  ⟨same_total c, charge_sits_elsewhere c hc⟩

end Unity
end CausalSpectrum

