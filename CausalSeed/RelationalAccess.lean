/-
Relational quantum memory and operational access.

Mathematical claims of the note of 5 November 2026. The qubit arguments are
the Bloch and amplitude identities used in the proofs. Instruments and
Hamiltonians are not formalized as operators on a Hilbert space.

Proved here, with no sorry:

* a Bloch vector with `r ^ 2 + z ^ 2 ≤ 1` has nonnegative eigenvalues;
* `(I + zZ ± rX) / 2` agree on a Z measurement, and after the Hadamard swap
  the outcome-zero probabilities differ by `r`;
* scaling the X coherence by `1 - lam` gives optimal success
  `(1 + (1 - lam) * r) / 2`;
* both Bell states have marginals `I / 2`, and `(H ⊗ I) ∘ CNOT` sends them
  to `|00⟩` and `|10⟩`;
* binary total variation is the absolute gap of the two probabilities;
* every deterministic one-bit code scores at most `3 / 4`, and sending the
  first bit attains it; mixtures do not improve the bound;
* the one-qubit score of an arbitrary preparation and an arbitrary binary
  decoding pair is at most `(1 + 1 / √2) / 2`, and the displayed encoding
  attains it on every input and query;
* isotropic depolarization of that encoding succeeds with
  `(1 + η / √2) / 2` and stays inside the Bloch ball for `|η| ≤ 1`;
* all `16 × 16` deterministic one-bit encoder/decoder pairs score at most
  `6 / 8`;
* a deterministic binary report has Shannon entropy zero and can still hide
  a bit;
* on a two-step binary transcript with full support, the expected log
  likelihood ratio splits into the marginal KL plus the expected conditional
  KL, the sum is nonnegative, and a single realized ratio can be negative;
* the Hoeffding exponent is minimized at `u = 4ε`, equals `-2 N ε ^ 2` there,
  and `N ≥ log(1 / α) / (2ε ^ 2)` yields `exp(-2 N ε ^ 2) ≤ α`;
* under depolarization the distance to the one-bit score is
  `max(0, η / (2√2) - 1 / 4)`;
* the ideal distance is `(√2 - 1) / 4`, crossed exactly when `η > 1 / √2`;
* the one-random-bit strategy scores `3 / 4` everywhere, and a mixture with
  fair guessing matches any success in `[1 / 2, 3 / 4]`;
* two classical bits, flipped with probability `1 - p`, reproduce success `p`.

Not proved: that a device, a brain, or conscious processing implements the
model; that the accessibility functional measures consciousness; existence of
God, generation of spacetime, or a clinical account of psychosis; that the
maps (2)--(5) are completely positive instruments on a Hilbert space; a sharp
entropy bound for the universal seed; the moment-generating inequality in
Hoeffding's lemma (only the resulting exponent and the sample-size threshold
are proved); the chain rule for a transcript longer than two binary steps.
-/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

namespace CausalSpectrum
namespace RelationalAccess

abbrev V := ℝ × ℝ × ℝ

def dot (a b : V) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def nsq (a : V) : ℝ := dot a a

def nrm (a : V) : ℝ := Real.sqrt (nsq a)

def vadd (a b : V) : V := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def vsub (a b : V) : V := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)

def smul (c : ℝ) (a : V) : V := (c * a.1, c * a.2.1, c * a.2.2)

theorem nsq_smul (c : ℝ) (a : V) : nsq (smul c a) = c ^ 2 * nsq a := by
  unfold nsq dot smul
  ring

theorem nrm_neg (a : V) : nrm (smul (-1) a) = nrm a := by
  simp only [nrm]
  rw [nsq_smul]
  have : (-1 : ℝ) ^ 2 * nsq a = nsq a := by ring
  rw [this]

theorem nsq_nonneg (a : V) : 0 ≤ nsq a := by
  unfold nsq dot
  nlinarith [sq_nonneg a.1, sq_nonneg a.2.1, sq_nonneg a.2.2]

theorem nrm_sq (a : V) : nrm a ^ 2 = nsq a :=
  Real.sq_sqrt (nsq_nonneg a)

theorem parallelogram (a b : V) :
    nsq (vadd a b) + nsq (vsub a b) = 2 * nsq a + 2 * nsq b := by
  unfold nsq dot vadd vsub
  ring

theorem cauchy (a b : V) : (dot a b) ^ 2 ≤ nsq a * nsq b := by
  unfold nsq dot
  nlinarith [sq_nonneg (a.1 * b.2.1 - a.2.1 * b.1),
    sq_nonneg (a.1 * b.2.2 - a.2.2 * b.1),
    sq_nonneg (a.2.1 * b.2.2 - a.2.2 * b.2.1)]

theorem abs_dot_le (a b : V) : |dot a b| ≤ nrm a * nrm b := by
  have hsqrt : |dot a b| ≤ Real.sqrt (nsq a * nsq b) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (cauchy a b)
  rw [Real.sqrt_mul (nsq_nonneg a)] at hsqrt
  simpa [nrm] using hsqrt

theorem sum_nrm_sq_le (a b : V) :
    (nrm (vadd a b) + nrm (vsub a b)) ^ 2 ≤ 4 * (nsq a + nsq b) := by
  have hx : 0 ≤ nrm (vadd a b) := Real.sqrt_nonneg _
  have hy : 0 ≤ nrm (vsub a b) := Real.sqrt_nonneg _
  have hcross :
      2 * nrm (vadd a b) * nrm (vsub a b)
        ≤ nrm (vadd a b) ^ 2 + nrm (vsub a b) ^ 2 := by
    nlinarith [sq_nonneg (nrm (vadd a b) - nrm (vsub a b))]
  calc
    (nrm (vadd a b) + nrm (vsub a b)) ^ 2
        = nrm (vadd a b) ^ 2 + nrm (vsub a b) ^ 2
          + 2 * nrm (vadd a b) * nrm (vsub a b) := by ring
    _ ≤ 2 * (nrm (vadd a b) ^ 2 + nrm (vsub a b) ^ 2) := by linarith
    _ = 2 * (nsq (vadd a b) + nsq (vsub a b)) := by rw [nrm_sq, nrm_sq]
    _ = 2 * (2 * nsq a + 2 * nsq b) := by rw [parallelogram]
    _ = 4 * (nsq a + nsq b) := by ring

theorem two_sqrt_two_sq : (2 * Real.sqrt 2) ^ 2 = 8 := by
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem sum_nrm_le (a b : V) (ha : nsq a ≤ 1) (hb : nsq b ≤ 1) :
    nrm (vadd a b) + nrm (vsub a b) ≤ 2 * Real.sqrt 2 := by
  have h8 : (nrm (vadd a b) + nrm (vsub a b)) ^ 2 ≤ 8 := by
    have hsum : nsq a + nsq b ≤ 2 := by linarith
    linarith [sum_nrm_sq_le a b]
  rw [← two_sqrt_two_sq] at h8
  exact le_of_sq_le_sq h8 (by positivity)

/-! ### Propositions 3.1 and 3.2 -/

def rhoBloch (r z s : ℝ) : V := (s * r, 0, z)

def afterH (v : V) : V := (v.2.2, v.2.1, v.1)

def pZeroZ (v : V) : ℝ := (1 + v.2.2) / 2

theorem eigenvalues_nonneg (r z : ℝ) (h : r ^ 2 + z ^ 2 ≤ 1) :
    0 ≤ (1 - Real.sqrt (r ^ 2 + z ^ 2)) / 2 ∧
      0 ≤ (1 + Real.sqrt (r ^ 2 + z ^ 2)) / 2 := by
  have hs : Real.sqrt (r ^ 2 + z ^ 2) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt h
  constructor <;> linarith [Real.sqrt_nonneg (r ^ 2 + z ^ 2)]

theorem z_statistics_agree (r z : ℝ) :
    pZeroZ (rhoBloch r z 1) = pZeroZ (rhoBloch r z (-1)) := by
  simp [pZeroZ, rhoBloch]

theorem hadamard_gap (r z : ℝ) :
    pZeroZ (afterH (rhoBloch r z 1)) - pZeroZ (afterH (rhoBloch r z (-1))) = r := by
  simp [pZeroZ, afterH, rhoBloch]
  ring

theorem binary_tv (p q : ℝ) :
    (1 / 2) * (|p - q| + |(1 - p) - (1 - q)|) = |p - q| := by
  have : (1 - p) - (1 - q) = q - p := by ring
  rw [this, abs_sub_comm q p]
  ring

theorem z_accessibility_zero (r z : ℝ) :
    |pZeroZ (rhoBloch r z 1) - pZeroZ (rhoBloch r z (-1))| = 0 := by
  simp [z_statistics_agree]

theorem hadamard_accessibility (r : ℝ) (hr : 0 ≤ r) (z : ℝ) :
    |pZeroZ (afterH (rhoBloch r z 1)) - pZeroZ (afterH (rhoBloch r z (-1)))| = r := by
  rw [hadamard_gap r z, abs_of_nonneg hr]

def dephased (lam r : ℝ) : V := ((1 - lam) * r, 0, 0)

theorem dephased_nrm (lam r : ℝ) (hlam : lam ≤ 1) (hr : 0 ≤ r) :
    nrm (dephased lam r) = (1 - lam) * r := by
  have h1 : 0 ≤ 1 - lam := by linarith
  have hmul : 0 ≤ (1 - lam) * r := mul_nonneg h1 hr
  simp only [nrm, nsq, dot, dephased]
  have : ((1 - lam) * r) * ((1 - lam) * r) + 0 * 0 + 0 * 0
      = ((1 - lam) * r) ^ 2 := by ring
  rw [this]
  exact Real.sqrt_sq hmul

theorem dephasing_attained (lam r : ℝ) (hlam : lam ≤ 1) (hr : 0 ≤ r) :
    (1 + nrm (dephased lam r)) / 2 = (1 + (1 - lam) * r) / 2 := by
  rw [dephased_nrm lam r hlam hr]

theorem dephasing_optimal (lam r : ℝ) (hlam : lam ≤ 1) (hr : 0 ≤ r) (a : V)
    (ha : nsq a ≤ 1) :
    (1 + dot a (dephased lam r)) / 2 ≤ (1 + (1 - lam) * r) / 2 := by
  have hna : nrm a ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ha
  have hn : nrm (dephased lam r) = (1 - lam) * r := dephased_nrm lam r hlam hr
  have hdot : dot a (dephased lam r) ≤ nrm a * nrm (dephased lam r) :=
    le_trans (le_abs_self _) (abs_dot_le a (dephased lam r))
  have hmul : nrm a * nrm (dephased lam r) ≤ 1 * nrm (dephased lam r) :=
    mul_le_mul_of_nonneg_right hna (Real.sqrt_nonneg _)
  rw [one_mul] at hmul
  linarith

/-! ### Proposition 3.3 -/

abbrev Amp := Fin 4 → ℝ

def invSqrt2 : ℝ := 1 / Real.sqrt 2

def phiPlus : Amp
  | 0 => invSqrt2
  | 1 => 0
  | 2 => 0
  | 3 => invSqrt2

def phiMinus : Amp
  | 0 => invSqrt2
  | 1 => 0
  | 2 => 0
  | 3 => -invSqrt2

def normSq4 (ψ : Amp) : ℝ :=
  (ψ 0) ^ 2 + (ψ 1) ^ 2 + (ψ 2) ^ 2 + (ψ 3) ^ 2

theorem invSqrt2_sq : invSqrt2 ^ 2 = 1 / 2 := by
  unfold invSqrt2
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem phiPlus_norm : normSq4 phiPlus = 1 := by
  simp [normSq4, phiPlus, invSqrt2_sq]
  norm_num

theorem phiMinus_norm : normSq4 phiMinus = 1 := by
  simp [normSq4, phiMinus, invSqrt2_sq]
  norm_num

theorem phiPlus_marginalA :
    (phiPlus 0) ^ 2 + (phiPlus 1) ^ 2 = 1 / 2 ∧
      (phiPlus 2) ^ 2 + (phiPlus 3) ^ 2 = 1 / 2 ∧
      phiPlus 0 * phiPlus 2 + phiPlus 1 * phiPlus 3 = 0 := by
  simp [phiPlus, invSqrt2_sq]

theorem phiMinus_marginalA :
    (phiMinus 0) ^ 2 + (phiMinus 1) ^ 2 = 1 / 2 ∧
      (phiMinus 2) ^ 2 + (phiMinus 3) ^ 2 = 1 / 2 ∧
      phiMinus 0 * phiMinus 2 + phiMinus 1 * phiMinus 3 = 0 := by
  simp [phiMinus, invSqrt2_sq]

theorem phiPlus_marginalB :
    (phiPlus 0) ^ 2 + (phiPlus 2) ^ 2 = 1 / 2 ∧
      (phiPlus 1) ^ 2 + (phiPlus 3) ^ 2 = 1 / 2 := by
  simp [phiPlus, invSqrt2_sq]

theorem phiMinus_marginalB :
    (phiMinus 0) ^ 2 + (phiMinus 2) ^ 2 = 1 / 2 ∧
      (phiMinus 1) ^ 2 + (phiMinus 3) ^ 2 = 1 / 2 := by
  simp [phiMinus, invSqrt2_sq]

def cnot (ψ : Amp) : Amp
  | 0 => ψ 0
  | 1 => ψ 1
  | 2 => ψ 3
  | 3 => ψ 2

def hTensor (ψ : Amp) : Amp
  | 0 => (ψ 0 + ψ 2) * invSqrt2
  | 1 => (ψ 1 + ψ 3) * invSqrt2
  | 2 => (ψ 0 - ψ 2) * invSqrt2
  | 3 => (ψ 1 - ψ 3) * invSqrt2

def ket00 : Amp
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 0

def ket10 : Amp
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0

theorem two_invSqrt_sum : (invSqrt2 + invSqrt2) * invSqrt2 = 1 := by
  have : (invSqrt2 + invSqrt2) * invSqrt2 = 2 * invSqrt2 ^ 2 := by ring
  rw [this, invSqrt2_sq]
  norm_num

theorem two_invSqrt_diff : (invSqrt2 - -invSqrt2) * invSqrt2 = 1 := by
  have : (invSqrt2 - -invSqrt2) * invSqrt2 = 2 * invSqrt2 ^ 2 := by ring
  rw [this, invSqrt2_sq]
  norm_num

theorem bell_to_computational :
    hTensor (cnot phiPlus) = ket00 ∧ hTensor (cnot phiMinus) = ket10 := by
  constructor
  · ext i
    fin_cases i
    · simp [hTensor, cnot, phiPlus, ket00, two_invSqrt_sum]
    · simp [hTensor, cnot, phiPlus, ket00]
    · simp [hTensor, cnot, phiPlus, ket00]
    · simp [hTensor, cnot, phiPlus, ket00]
  · ext i
    fin_cases i
    · simp [hTensor, cnot, phiMinus, ket10]
    · simp [hTensor, cnot, phiMinus, ket10]
    · simp [hTensor, cnot, phiMinus, ket10]
      exact two_invSqrt_sum
    · simp [hTensor, cnot, phiMinus, ket10]

/-! ### Theorem 6.1 -/

abbrev Word := Bool × Bool

def ham (x y : Word) : ℕ :=
  (if x.1 = y.1 then 0 else 1) + (if x.2 = y.2 then 0 else 1)

def minDist (x c0 c1 : Word) : ℕ := min (ham x c0) (ham x c1)

def totalErr (c0 c1 : Word) : ℕ :=
  minDist (false, false) c0 c1 + minDist (false, true) c0 c1 +
    minDist (true, false) c0 c1 + minDist (true, true) c0 c1

theorem ham_le_two (x y : Word) : ham x y ≤ 2 := by
  unfold ham
  split_ifs <;> decide

theorem minDist_le_two (x c0 c1 : Word) : minDist x c0 c1 ≤ 2 :=
  le_trans (min_le_left _ _) (ham_le_two x c0)

theorem totalErr_le_eight (c0 c1 : Word) : totalErr c0 c1 ≤ 8 := by
  unfold totalErr
  have h1 := minDist_le_two (false, false) c0 c1
  have h2 := minDist_le_two (false, true) c0 c1
  have h3 := minDist_le_two (true, false) c0 c1
  have h4 := minDist_le_two (true, true) c0 c1
  omega

theorem totalErr_ge_two (c0 c1 : Word) : 2 ≤ totalErr c0 c1 := by
  rcases c0 with ⟨a, b⟩
  rcases c1 with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem classical_score_le (c0 c1 : Word) :
    ((8 - totalErr c0 c1 : ℕ) : ℝ) / 8 ≤ (3 : ℝ) / 4 := by
  have h2 := totalErr_ge_two c0 c1
  have h8 := totalErr_le_eight c0 c1
  have h6 : 8 - totalErr c0 c1 ≤ 6 := by omega
  have hcast : ((8 - totalErr c0 c1 : ℕ) : ℝ) ≤ 6 := by exact_mod_cast h6
  have hdiv : ((8 - totalErr c0 c1 : ℕ) : ℝ) / 8 ≤ 6 / 8 :=
    div_le_div_of_nonneg_right hcast (by norm_num)
  have : (6 : ℝ) / 8 = 3 / 4 := by norm_num
  linarith

theorem classical_attained : totalErr (false, false) (true, false) = 2 := by
  decide

theorem classical_attained_score :
    ((8 - totalErr (false, false) (true, false) : ℕ) : ℝ) / 8 = (3 : ℝ) / 4 := by
  rw [classical_attained]
  norm_num

/-! The note's check of all `16 × 16` deterministic pairs is the same bound.
An encoder is four output bits and a decoder is four answer bits. Each
message determines a codeword, so the pair falls under `totalErr_ge_two`. -/

def idx (b1 b2 : Bool) : ℕ :=
  (if b1 then 2 else 0) + (if b2 then 1 else 0)

def bitAt (n : Fin 16) (i : ℕ) : Bool :=
  decide ((n.val / 2 ^ i) % 2 = 1)

def encOut (e : Fin 16) (x : Word) : Bool :=
  bitAt e (idx x.1 x.2)

def decBit (d : Fin 16) (m j : Bool) : Bool :=
  bitAt d (idx m j)

def cw (d : Fin 16) (m : Bool) : Word :=
  (decBit d m false, decBit d m true)

def inputSucc (e d : Fin 16) (x : Word) : ℕ :=
  let y := cw d (encOut e x)
  (if x.1 = y.1 then 1 else 0) + (if x.2 = y.2 then 1 else 0)

def score8 (e d : Fin 16) : ℕ :=
  inputSucc e d (false, false) + inputSucc e d (false, true) +
    inputSucc e d (true, false) + inputSucc e d (true, true)

theorem succ_add_ham (x y : Word) :
    ((if x.1 = y.1 then 1 else 0) + (if x.2 = y.2 then 1 else 0)) + ham x y = 2 := by
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> decide

theorem inputSucc_le (e d : Fin 16) (x : Word) :
    inputSucc e d x + minDist x (cw d false) (cw d true) ≤ 2 := by
  set m := encOut e x with hm
  have hadd : inputSucc e d x + ham x (cw d m) = 2 := by
    unfold inputSucc
    rw [← hm]
    exact succ_add_ham x (cw d m)
  have hpick : minDist x (cw d false) (cw d true) ≤ ham x (cw d m) := by
    unfold minDist
    cases m
    · exact min_le_left _ _
    · exact min_le_right _ _
  omega

theorem score8_add_total (e d : Fin 16) :
    score8 e d + totalErr (cw d false) (cw d true) ≤ 8 := by
  have h1 := inputSucc_le e d (false, false)
  have h2 := inputSucc_le e d (false, true)
  have h3 := inputSucc_le e d (true, false)
  have h4 := inputSucc_le e d (true, true)
  unfold score8 totalErr at *
  omega

theorem all_deterministic_scores (e d : Fin 16) : score8 e d ≤ 6 := by
  have h := score8_add_total e d
  have h2 := totalErr_ge_two (cw d false) (cw d true)
  omega

theorem enumeration_score (e d : Fin 16) :
    ((score8 e d : ℕ) : ℝ) / 8 ≤ (3 : ℝ) / 4 := by
  have h6 : score8 e d ≤ 6 := all_deterministic_scores e d
  have hcast : ((score8 e d : ℕ) : ℝ) ≤ 6 := by exact_mod_cast h6
  have hdiv : ((score8 e d : ℕ) : ℝ) / 8 ≤ 6 / 8 :=
    div_le_div_of_nonneg_right hcast (by norm_num)
  have : (6 : ℝ) / 8 = 3 / 4 := by norm_num
  linarith

theorem enumeration_attained : ∃ e d : Fin 16, score8 e d = 6 := by
  refine ⟨12, 4, ?_⟩
  decide

theorem mixture_preserves (s1 s2 t : ℝ) (h1 : s1 ≤ 3 / 4) (h2 : s2 ≤ 3 / 4)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * s1 + (1 - t) * s2 ≤ 3 / 4 := by
  nlinarith

/-! ### Theorem 6.2 -/

def pStar : ℝ := (1 + 1 / Real.sqrt 2) / 2

theorem pStar_algebra : pStar = 1 / 2 + Real.sqrt 2 / 4 := by
  unfold pStar
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hmul : 1 / (2 * Real.sqrt 2) = Real.sqrt 2 / 4 := by
    field_simp [hs]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc
    (1 + 1 / Real.sqrt 2) / 2 = 1 / 2 + 1 / (2 * Real.sqrt 2) := by
      field_simp [hs]
    _ = 1 / 2 + Real.sqrt 2 / 4 := by rw [hmul]

theorem pStar_cos : pStar = Real.cos (Real.pi / 8) ^ 2 := by
  rw [pStar_algebra, Real.cos_sq]
  rw [show (2 : ℝ) * (Real.pi / 8) = Real.pi / 4 by ring]
  rw [Real.cos_pi_div_four]
  ring

theorem quantum_beats_classical : (3 : ℝ) / 4 < pStar := by
  rw [pStar_algebra]
  have h : 1 < Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  linarith

def enc (x1 x2 : Bool) : V :=
  ((if x1 then -1 else 1) / Real.sqrt 2, 0,
    (if x2 then -1 else 1) / Real.sqrt 2)

theorem half_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem neg_half_sq : ((-1) / Real.sqrt 2) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem prod_half : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
  simpa [pow_two] using half_sq

theorem prod_neg_half : ((-1) / Real.sqrt 2) * ((-1) / Real.sqrt 2) = 1 / 2 := by
  simpa [pow_two] using neg_half_sq

theorem inv_sqrt_mul : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem neg_inv_mul : (-1 / Real.sqrt 2) * (-1 / Real.sqrt 2) = 1 / 2 := by
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem enc_unit (x1 x2 : Bool) : nsq (enc x1 x2) = 1 := by
  cases x1
  · cases x2
    · simp [enc, nsq, dot]
      rw [inv_sqrt_mul]
      norm_num
    · simp [enc, nsq, dot]
      rw [inv_sqrt_mul, neg_inv_mul]
      norm_num
  · cases x2
    · simp [enc, nsq, dot]
      rw [inv_sqrt_mul, neg_inv_mul]
      norm_num
    · simp [enc, nsq, dot]
      rw [neg_inv_mul]
      norm_num

theorem abs_invSqrt : |1 / Real.sqrt 2| = 1 / Real.sqrt 2 := by
  rw [abs_of_nonneg]
  positivity

theorem abs_neg_invSqrt : |(-1) / Real.sqrt 2| = 1 / Real.sqrt 2 := by
  rw [abs_div, abs_neg, abs_one, abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]

theorem quantum_success (x1 x2 : Bool) :
    (1 + |(enc x1 x2).1|) / 2 = pStar ∧ (1 + |(enc x1 x2).2.2|) / 2 = pStar := by
  cases x1 <;> cases x2 <;>
    simp [enc, pStar, abs_neg, abs_invSqrt, abs_neg_invSqrt]

theorem qubit_score_le (a1 a2 : V) (h1 : nsq a1 ≤ 1) (h2 : nsq a2 ≤ 1) :
    1 / 2 + (nrm (vadd a1 a2) + nrm (vsub a1 a2)) / 8 ≤ pStar := by
  rw [pStar_algebra]
  have h := sum_nrm_le a1 a2 h1 h2
  have hdiv : (nrm (vadd a1 a2) + nrm (vsub a1 a2)) / 8 ≤ (2 * Real.sqrt 2) / 8 :=
    div_le_div_of_nonneg_right h (by norm_num)
  have : (2 * Real.sqrt 2) / 8 = Real.sqrt 2 / 4 := by ring
  linarith

/-! The score in the proof of Theorem 6.2, for an arbitrary Bloch preparation. -/

def signb (b : Bool) : ℝ := if b then -1 else 1

def queryVec (a1 a2 : V) (x1 x2 : Bool) : V :=
  vadd (smul (signb x1) a1) (smul (signb x2) a2)

theorem query_ff (a1 a2 : V) : queryVec a1 a2 false false = vadd a1 a2 := by
  unfold queryVec signb smul vadd
  simp

theorem query_ft (a1 a2 : V) : queryVec a1 a2 false true = vsub a1 a2 := by
  unfold queryVec signb smul vadd vsub
  simp
  exact ⟨by ring, by ring, by ring⟩

theorem query_tf (a1 a2 : V) :
    queryVec a1 a2 true false = smul (-1) (vsub a1 a2) := by
  unfold queryVec signb smul vadd vsub
  simp
  exact ⟨by ring, by ring, by ring⟩

theorem query_tt (a1 a2 : V) :
    queryVec a1 a2 true true = smul (-1) (vadd a1 a2) := by
  unfold queryVec signb smul vadd
  simp
  exact ⟨by ring, by ring, by ring⟩

theorem nrm_queryVec (a1 a2 : V) :
    nrm (queryVec a1 a2 false false) = nrm (vadd a1 a2) ∧
      nrm (queryVec a1 a2 false true) = nrm (vsub a1 a2) ∧
      nrm (queryVec a1 a2 true false) = nrm (vsub a1 a2) ∧
      nrm (queryVec a1 a2 true true) = nrm (vadd a1 a2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [query_ff]
  · rw [query_ft]
  · rw [query_tf, nrm_neg]
  · rw [query_tt, nrm_neg]

theorem dot_le_nrm (r q : V) (hr : nsq r ≤ 1) : dot r q ≤ nrm q := by
  have hn : nrm r ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hr
  have hdot : dot r q ≤ nrm r * nrm q :=
    le_trans (le_abs_self _) (abs_dot_le r q)
  have hmul : nrm r * nrm q ≤ 1 * nrm q :=
    mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg _)
  rw [one_mul] at hmul
  linarith

/-- Mean score `1/2 + (1/16) ∑_x r_x · ((-1)^{x_1} a_1 + (-1)^{x_2} a_2)`. -/
def racScore (r00 r01 r10 r11 a1 a2 : V) : ℝ :=
  1 / 2 + (1 / 16) * (
    dot r00 (queryVec a1 a2 false false) +
    dot r01 (queryVec a1 a2 false true) +
    dot r10 (queryVec a1 a2 true false) +
    dot r11 (queryVec a1 a2 true true))

theorem racScore_le (r00 r01 r10 r11 a1 a2 : V)
    (h00 : nsq r00 ≤ 1) (h01 : nsq r01 ≤ 1) (h10 : nsq r10 ≤ 1) (h11 : nsq r11 ≤ 1)
    (ha1 : nsq a1 ≤ 1) (ha2 : nsq a2 ≤ 1) :
    racScore r00 r01 r10 r11 a1 a2 ≤ pStar := by
  have nq := nrm_queryVec a1 a2
  have d00 := dot_le_nrm r00 (queryVec a1 a2 false false) h00
  have d01 := dot_le_nrm r01 (queryVec a1 a2 false true) h01
  have d10 := dot_le_nrm r10 (queryVec a1 a2 true false) h10
  have d11 := dot_le_nrm r11 (queryVec a1 a2 true true) h11
  rw [nq.1] at d00
  rw [nq.2.1] at d01
  rw [nq.2.2.1] at d10
  rw [nq.2.2.2] at d11
  have hsum :
      dot r00 (queryVec a1 a2 false false) +
        dot r01 (queryVec a1 a2 false true) +
        dot r10 (queryVec a1 a2 true false) +
        dot r11 (queryVec a1 a2 true true)
      ≤ 2 * nrm (vadd a1 a2) + 2 * nrm (vsub a1 a2) := by
    linarith
  have h16 :
      (1 / 16) * (
        dot r00 (queryVec a1 a2 false false) +
        dot r01 (queryVec a1 a2 false true) +
        dot r10 (queryVec a1 a2 true false) +
        dot r11 (queryVec a1 a2 true true))
      ≤ (nrm (vadd a1 a2) + nrm (vsub a1 a2)) / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 16)
    have hid :
        (1 / 16) * (2 * nrm (vadd a1 a2) + 2 * nrm (vsub a1 a2))
          = (nrm (vadd a1 a2) + nrm (vsub a1 a2)) / 8 := by ring
    linarith
  have hq := qubit_score_le a1 a2 ha1 ha2
  unfold racScore
  linarith

theorem quantum_mean_score :
    ((1 + |(enc false false).1|) / 2 + (1 + |(enc false false).2.2|) / 2 +
      (1 + |(enc false true).1|) / 2 + (1 + |(enc false true).2.2|) / 2 +
      (1 + |(enc true false).1|) / 2 + (1 + |(enc true false).2.2|) / 2 +
      (1 + |(enc true true).1|) / 2 + (1 + |(enc true true).2.2|) / 2) / 8
      = pStar := by
  have h1 := quantum_success false false
  have h2 := quantum_success false true
  have h3 := quantum_success true false
  have h4 := quantum_success true true
  rw [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  ring

/-! ### Theorem 6.3 and Corollary 6.4 -/

def pEta (η : ℝ) : ℝ := (1 + η / Real.sqrt 2) / 2

/-- Depolarization `ηρ + (1-η)I/2` scales the Bloch vector by `η`. -/
def scaled (η : ℝ) (v : V) : V := smul η v

theorem depolarized_nsq (η : ℝ) (x1 x2 : Bool) :
    nsq (scaled η (enc x1 x2)) = η ^ 2 := by
  rw [scaled, nsq_smul, enc_unit, mul_one]

theorem depolarized_inside (η : ℝ) (h : |η| ≤ 1) (x1 x2 : Bool) :
    nsq (scaled η (enc x1 x2)) ≤ 1 := by
  rw [depolarized_nsq]
  calc
    η ^ 2 = |η| ^ 2 := by rw [sq_abs]
    _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg η) h 2
    _ = 1 := by norm_num

theorem depolarized_success (η : ℝ) (hη : 0 ≤ η) (x1 x2 : Bool) :
    (1 + |(scaled η (enc x1 x2)).1|) / 2 = pEta η ∧
      (1 + |(scaled η (enc x1 x2)).2.2|) / 2 = pEta η := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  cases x1 <;> cases x2
  · constructor
    · simp [scaled, smul, enc, pEta, abs_mul, abs_of_nonneg hη]
      rw [abs_of_pos hsqrt]
      ring
    · simp [scaled, smul, enc, pEta, abs_mul, abs_of_nonneg hη]
      rw [abs_of_pos hsqrt]
      ring
  · constructor
    · simp [scaled, smul, enc, pEta, abs_mul, abs_of_nonneg hη]
      rw [abs_of_pos hsqrt]
      ring
    · simp [scaled, smul, enc, pEta, abs_mul, abs_of_nonneg hη, abs_neg_invSqrt]
      ring
  · constructor
    · simp [scaled, smul, enc, pEta, abs_mul, abs_of_nonneg hη, abs_neg_invSqrt]
      ring
    · simp [scaled, smul, enc, pEta, abs_mul, abs_of_nonneg hη]
      rw [abs_of_pos hsqrt]
      ring
  · constructor
    · simp [scaled, smul, enc, pEta, abs_mul, abs_of_nonneg hη, abs_neg_invSqrt]
      ring
    · simp [scaled, smul, enc, pEta, abs_mul, abs_of_nonneg hη, abs_neg_invSqrt]
      ring

theorem pEta_sub (η : ℝ) :
    pEta η - 3 / 4 = η / (2 * Real.sqrt 2) - 1 / 4 := by
  unfold pEta
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs]
  ring

theorem distance_formula (η : ℝ) :
    max 0 (pEta η - 3 / 4) = max 0 (η / (2 * Real.sqrt 2) - 1 / 4) := by
  rw [pEta_sub]

theorem ideal_distance : pEta 1 - 3 / 4 = (Real.sqrt 2 - 1) / 4 := by
  rw [pEta_sub]
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem violates_iff (η : ℝ) : 3 / 4 < pEta η ↔ 1 / Real.sqrt 2 < η := by
  unfold pEta
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hid : 1 / Real.sqrt 2 = (1 / 2) * Real.sqrt 2 := by
    field_simp [hs.ne']
    nlinarith [hsq]
  constructor
  · intro h
    have : (1 : ℝ) / 2 < η / Real.sqrt 2 := by linarith
    have : (1 / 2) * Real.sqrt 2 < η := (lt_div_iff₀ hs).mp this
    linarith [hid]
  · intro h
    have : (1 / 2) * Real.sqrt 2 < η := by linarith [hid]
    have : (1 : ℝ) / 2 < η / Real.sqrt 2 := (lt_div_iff₀ hs).mpr this
    linarith

theorem one_bit_shared_score : (1 / 2) * (1 : ℝ) + (1 / 2) * (1 / 2) = 3 / 4 := by
  norm_num

theorem mixture_matches (p : ℝ) :
    4 * (p - 1 / 2) * (3 / 4) + (1 - 4 * (p - 1 / 2)) * (1 / 2) = p := by
  ring

theorem mixture_weight_unit (p : ℝ) (h1 : 1 / 2 ≤ p) (h2 : p ≤ 3 / 4) :
    0 ≤ 4 * (p - 1 / 2) ∧ 4 * (p - 1 / 2) ≤ 1 := by
  constructor <;> linarith

theorem list_gap (qs : List ℝ) (p d : ℝ) (_hd : 0 ≤ d)
    (h : ∀ q ∈ qs, |p - q| ≤ d) :
    p * (qs.length : ℝ) - qs.sum ≤ d * (qs.length : ℝ) := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨hq, hrest⟩ := h
    have ih' := ih hrest
    simp only [List.sum_cons, List.length_cons, Nat.cast_succ]
    have : p - q ≤ d := le_trans (le_abs_self _) hq
    nlinarith

theorem worst_gap_ge (qs : List ℝ) (p d : ℝ) (hd : 0 ≤ d)
    (hmean : qs.sum / (qs.length : ℝ) ≤ 3 / 4)
    (h : ∀ q ∈ qs, |p - q| ≤ d) (hne : qs ≠ []) :
    max 0 (p - 3 / 4) ≤ d := by
  have hlen : (0 : ℝ) < qs.length := by
    exact_mod_cast List.length_pos_iff.mpr hne
  have hsum : qs.sum ≤ (3 / 4) * (qs.length : ℝ) := by
    rwa [div_le_iff₀ hlen] at hmean
  have hgap := list_gap qs p d hd h
  have hdiff : p - 3 / 4 ≤ d := by
    have : p * (qs.length : ℝ) - (3 / 4) * (qs.length : ℝ)
        ≤ d * (qs.length : ℝ) := by linarith
    have : (p - 3 / 4) * (qs.length : ℝ) ≤ d * (qs.length : ℝ) := by
      linarith
    exact le_of_mul_le_mul_right this hlen
  exact max_le hd hdiff

/-! ### Two bits are outside the one-bit contract -/

theorem two_bit_flip (p : ℝ) : p * 1 + (1 - p) * 0 = p := by
  ring

/-! ### Theorem 5.1, the policy-independent lookup -/

variable {H A Y : Type}

def lookup (table : H → A → Y) (h : H) (a : A) : Y :=
  table h a

def transcriptProb (steps : List (H × A × Y)) (kern : H → A → Y → ℝ) : ℝ :=
  steps.foldl (fun acc t => acc * kern t.1 t.2.1 t.2.2) 1

/-! ### The Hoeffding exponent -/

theorem hoeffding_exponent (N : ℕ) (ε : ℝ) :
    -(4 * ε) * (N : ℝ) * ε + (N : ℝ) * (4 * ε) ^ 2 / 8
      = -2 * (N : ℝ) * ε ^ 2 := by
  ring

theorem tail_threshold (N : ℕ) (ε α : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hN : Real.log (1 / α) / (2 * ε ^ 2) ≤ (N : ℝ)) :
    Real.exp (-2 * (N : ℝ) * ε ^ 2) ≤ α := by
  have hε2 : 0 < 2 * ε ^ 2 := by positivity
  have hlog : Real.log (1 / α) ≤ (N : ℝ) * (2 * ε ^ 2) :=
    (div_le_iff₀ hε2).mp hN
  have hsign : Real.log (1 / α) = -Real.log α := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_one, zero_sub]
  have hexp : -2 * (N : ℝ) * ε ^ 2 ≤ Real.log α := by
    linarith
  have := Real.exp_le_exp.mpr hexp
  rwa [Real.exp_log hα] at this

theorem hoeffding_minimizer (N : ℕ) (ε u : ℝ) :
    -(4 * ε) * (N : ℝ) * ε + (N : ℝ) * (4 * ε) ^ 2 / 8
      ≤ -u * (N : ℝ) * ε + (N : ℝ) * u ^ 2 / 8 := by
  have hsq : 0 ≤ (u - 4 * ε) ^ 2 := sq_nonneg _
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hdiff :
      (-u * (N : ℝ) * ε + (N : ℝ) * u ^ 2 / 8)
        - (-(4 * ε) * (N : ℝ) * ε + (N : ℝ) * (4 * ε) ^ 2 / 8)
      = (N : ℝ) / 8 * (u - 4 * ε) ^ 2 := by ring
  nlinarith

/-! ### Section 5: report entropy and the two-step chain rule

`Real.binEntropy` is the binary entropy in nats. Division by `log 2` is the
paper's entropy in bits. The chain rule is the identity (6)--(7) for one
binary symbol of past and one binary symbol of future, on the positive
support. It is not the chain rule for an arbitrary length or alphabet.
-/

def reportEntropy (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

theorem reportEntropy_deterministic : reportEntropy 0 = 0 ∧ reportEntropy 1 = 0 := by
  simp [reportEntropy]

theorem reportEntropy_half : reportEntropy (1 / 2) = 1 := by
  have : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
  rw [reportEntropy, this, Real.binEntropy_two_inv]
  exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

/-- A constant report has equal values on two distinct internal states. -/
theorem deterministic_report_hides_a_bit :
    (fun (_ : Bool) => (false : Bool)) false = (fun _ => false) true ∧
      (false : Bool) ≠ true := by
  decide

def klBin (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

theorem klBin_nonneg (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ klBin p q := by
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hlog1 : Real.log (q / p) ≤ q / p - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
  have hlog2 : Real.log ((1 - q) / (1 - p)) ≤ (1 - q) / (1 - p) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos h1q h1p)
  have hmul1 : p * Real.log (q / p) ≤ p * (q / p - 1) :=
    mul_le_mul_of_nonneg_left hlog1 hp0.le
  have hmul2 :
      (1 - p) * Real.log ((1 - q) / (1 - p)) ≤ (1 - p) * ((1 - q) / (1 - p) - 1) :=
    mul_le_mul_of_nonneg_left hlog2 h1p.le
  have eq1 : p * (q / p - 1) = q - p := by
    field_simp [hp0.ne']
  have eq2 : (1 - p) * ((1 - q) / (1 - p) - 1) = p - q := by
    field_simp [h1p.ne']
    ring
  have hsum :
      p * Real.log (q / p) + (1 - p) * Real.log ((1 - q) / (1 - p)) ≤ 0 := by
    linarith
  have neg1 : Real.log (q / p) = -Real.log (p / q) := by
    rw [Real.log_div hq0.ne' hp0.ne', Real.log_div hp0.ne' hq0.ne']
    ring
  have neg2 :
      Real.log ((1 - q) / (1 - p)) = -Real.log ((1 - p) / (1 - q)) := by
    rw [Real.log_div h1q.ne' h1p.ne', Real.log_div h1p.ne' h1q.ne']
    ring
  unfold klBin
  rw [neg1, neg2] at hsum
  linarith

theorem kl_bits_nonneg (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ klBin p q / Real.log 2 :=
  div_nonneg (klBin_nonneg p q hp0 hp1 hq0 hq1) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem log_ratio_split (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    Real.log ((a * b) / (c * d)) = Real.log (a / c) + Real.log (b / d) := by
  rw [Real.log_div (mul_ne_zero ha hb) (mul_ne_zero hc hd),
    Real.log_mul ha hb, Real.log_mul hc hd, Real.log_div ha hc, Real.log_div hb hd]
  ring

theorem chain_two (p0 q0 a0 b0 a1 b1 : ℝ)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hq0 : 0 < q0) (hq1 : q0 < 1)
    (ha0 : 0 < a0) (ha0u : a0 < 1) (hb0 : 0 < b0) (hb0u : b0 < 1)
    (ha1 : 0 < a1) (ha1u : a1 < 1) (hb1 : 0 < b1) (hb1u : b1 < 1) :
    p0 * a0 * Real.log (p0 * a0 / (q0 * b0)) +
      p0 * (1 - a0) * Real.log (p0 * (1 - a0) / (q0 * (1 - b0))) +
      (1 - p0) * a1 * Real.log ((1 - p0) * a1 / ((1 - q0) * b1)) +
      (1 - p0) * (1 - a1) * Real.log ((1 - p0) * (1 - a1) / ((1 - q0) * (1 - b1)))
    = klBin p0 q0 + p0 * klBin a0 b0 + (1 - p0) * klBin a1 b1 := by
  have h1p : 0 < 1 - p0 := sub_pos.mpr hp1
  have h1q : 0 < 1 - q0 := sub_pos.mpr hq1
  have h1a0 : 0 < 1 - a0 := sub_pos.mpr ha0u
  have h1b0 : 0 < 1 - b0 := sub_pos.mpr hb0u
  have h1a1 : 0 < 1 - a1 := sub_pos.mpr ha1u
  have h1b1 : 0 < 1 - b1 := sub_pos.mpr hb1u
  have s1 := log_ratio_split p0 a0 q0 b0 hp0.ne' ha0.ne' hq0.ne' hb0.ne'
  have s2 := log_ratio_split p0 (1 - a0) q0 (1 - b0) hp0.ne' h1a0.ne' hq0.ne' h1b0.ne'
  have s3 := log_ratio_split (1 - p0) a1 (1 - q0) b1 h1p.ne' ha1.ne' h1q.ne' hb1.ne'
  have s4 :=
    log_ratio_split (1 - p0) (1 - a1) (1 - q0) (1 - b1) h1p.ne' h1a1.ne' h1q.ne' h1b1.ne'
  rw [s1, s2, s3, s4]
  unfold klBin
  ring

theorem expected_excess_nonneg (p0 q0 a0 b0 a1 b1 : ℝ)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hq0 : 0 < q0) (hq1 : q0 < 1)
    (ha0 : 0 < a0) (ha0u : a0 < 1) (hb0 : 0 < b0) (hb0u : b0 < 1)
    (ha1 : 0 < a1) (ha1u : a1 < 1) (hb1 : 0 < b1) (hb1u : b1 < 1) :
    0 ≤ p0 * a0 * Real.log (p0 * a0 / (q0 * b0)) +
      p0 * (1 - a0) * Real.log (p0 * (1 - a0) / (q0 * (1 - b0))) +
      (1 - p0) * a1 * Real.log ((1 - p0) * a1 / ((1 - q0) * b1)) +
      (1 - p0) * (1 - a1) * Real.log ((1 - p0) * (1 - a1) / ((1 - q0) * (1 - b1))) := by
  rw [chain_two p0 q0 a0 b0 a1 b1 hp0 hp1 hq0 hq1 ha0 ha0u hb0 hb0u ha1 ha1u hb1 hb1u]
  have h0 := klBin_nonneg p0 q0 hp0 hp1 hq0 hq1
  have h1 := klBin_nonneg a0 b0 ha0 ha0u hb0 hb0u
  have h2 := klBin_nonneg a1 b1 ha1 ha1u hb1 hb1u
  have hp : 0 ≤ p0 := hp0.le
  have hp' : 0 ≤ 1 - p0 := sub_nonneg.mpr hp1.le
  nlinarith

theorem realized_ratio_can_be_negative :
    Real.log ((1 / 10) / (9 / 10)) < 0 := by
  refine Real.log_neg ?_ ?_ <;> norm_num

end RelationalAccess
end CausalSpectrum

end
