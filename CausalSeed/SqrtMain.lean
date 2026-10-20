/-
Square-root asymptotic with rate, `b > 0`: for a stationary kernel with common entropy
`h` and positive least varentropy, the envelope mean `L_n`, the optimal exact
seed entropy `C_n` (in bits), and the greedy seed entropy all equal
`n h + √(2/π)(a - b)√n + O(n^{1/4} log n)`.
-/
import CausalSeed.SqrtBridge

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology ENNReal
namespace CausalSpectrum
namespace Kernel

variable (κ : Kernel)

theorem envelopeMean_nonneg (T : Tree) : 0 ≤ envelopeMean T := by
  rw [← integral_one_sub_Fstar]
  apply setIntegral_nonneg measurableSet_Ioi
  intro t _
  have : Fstar T t ≤ 1 := by simpa [Fstar] using policyCDF_le_one (envelopePolicy T t) t
  linarith

theorem shannonOverhead_nonneg : 0 ≤ shannonOverhead := by
  unfold shannonOverhead
  have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  positivity

/-- **Main theorem, `b > 0`, for `L_n`.** -/
theorem envelope_rate {h : ℝ} (hh : κ.EqualEntropy h) (hb : 0 < (κ.fam h).sB) :
    ∃ K : ℝ, ∀ n : ℕ, 3 ≤ n →
      |envelopeMean (κ.rounds n) - n * h -
          secondOrderCoeff (κ.fam h).sA (κ.fam h).sB * Real.sqrt n| ≤
        K * (Real.sqrt (Real.sqrt n) * Real.log n) := by
  obtain ⟨K, hK⟩ := (κ.fam h).mean_rate (κ.fam_centered hh) hb
  refine ⟨K, fun n hn => ?_⟩
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hq : 0 < Real.sqrt (Real.sqrt n) := Real.sqrt_pos.mpr hs
  have hq2 : Real.sqrt (Real.sqrt n) ^ 2 = Real.sqrt n := Real.sq_sqrt hs.le
  have hmi := κ.mean_identity hh (show 1 ≤ n by omega)
  have e : envelopeMean (κ.rounds n) - n * h -
      secondOrderCoeff (κ.fam h).sA (κ.fam h).sB * Real.sqrt n =
      Real.sqrt n * ((κ.fam h).Mn n - secondOrderCoeff (κ.fam h).sA (κ.fam h).sB) := by
    rw [← hmi]; field_simp
  rw [e, abs_mul, abs_of_pos hs]
  have := hK n hn
  calc Real.sqrt n * |(κ.fam h).Mn n - _| ≤ Real.sqrt n * (K * (Real.log n / Real.sqrt (Real.sqrt n))) :=
        mul_le_mul_of_nonneg_left this hs.le
    _ = K * (Real.sqrt (Real.sqrt n) * Real.log n) := by
        rw [← hq2]; field_simp
        rw [Real.sqrt_sq hq.le]; ring

/-- Transfer through the finite sandwich `L ≤ H ≤ L + c⋆`. -/
theorem sandwich_rate {h : ℝ} (hh : κ.EqualEntropy h) (hb : 0 < (κ.fam h).sB) :
    ∃ K : ℝ, ∀ H : ℕ → ℝ, (∀ n, envelopeMean (κ.rounds n) ≤ H n) →
      (∀ n, H n ≤ envelopeMean (κ.rounds n) + shannonOverhead) →
      ∀ n : ℕ, 3 ≤ n → |H n - n * h - secondOrderCoeff (κ.fam h).sA (κ.fam h).sB * Real.sqrt n| ≤
        K * (Real.sqrt (Real.sqrt n) * Real.log n) := by
  obtain ⟨K, hK⟩ := κ.envelope_rate hh hb
  refine ⟨|K| + shannonOverhead, fun H hlo hhi n hn => ?_⟩
  have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Sqrt.one_le_log_of_three_le h3
  have hq1 : 1 ≤ Real.sqrt (Real.sqrt n) := by
    have : 1 ≤ Real.sqrt n := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt this
  have hw : 1 ≤ Real.sqrt (Real.sqrt n) * Real.log n := by nlinarith
  have h1 := hK n hn
  have h2 := hlo n
  have h3' := hhi n
  have hc := shannonOverhead_nonneg
  have hKw : K * (Real.sqrt (Real.sqrt n) * Real.log n) ≤ |K| * (Real.sqrt (Real.sqrt n) * Real.log n) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
  have hcw : shannonOverhead ≤ shannonOverhead * (Real.sqrt (Real.sqrt n) * Real.log n) := by
    nlinarith
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith

/-- The stationary kernel as a locally finite infinite tree. -/
def toITree : ITree where
  nA := fun _ => κ.nA
  hA := fun _ => κ.hA
  nY := fun _ => κ.nY
  hY := fun _ => κ.hY
  kern := fun _ => κ.K
  kpos := fun _ => κ.Kpos
  ksum := fun _ => κ.Ksum

theorem trunc_toITree : ∀ (n : ℕ) (p : List (ℕ × ℕ)), trunc κ.toITree n p = κ.rounds n
  | 0, _ => rfl
  | n + 1, p => by
    simp only [trunc, rounds]
    congr 1
    funext a y
    exact trunc_toITree n _

/-- `C_n` in bits: the optimal exact countable-seed entropy for horizon `n`. -/
def costBits (n : ℕ) : ℝ := (Completion.finiteCost κ.toITree n).toReal / Real.log 2

theorem costBits_sandwich (n : ℕ) :
    envelopeMean (κ.rounds n) ≤ κ.costBits n ∧
      κ.costBits n ≤ envelopeMean (κ.rounds n) + shannonOverhead := by
  obtain ⟨h1, h2⟩ := Completion.finiteCost_sandwich κ.toITree n
  rw [κ.trunc_toITree] at h1 h2
  have hl := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have hL := envelopeMean_nonneg (κ.rounds n)
  have hc := shannonOverhead_nonneg
  have hfin : Completion.finiteCost κ.toITree n ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
  have a1 : Real.log 2 * envelopeMean (κ.rounds n) ≤ (Completion.finiteCost κ.toITree n).toReal := by
    have := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have a2 : (Completion.finiteCost κ.toITree n).toReal ≤ Real.log 2 * (envelopeMean (κ.rounds n) + shannonOverhead) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  unfold costBits
  constructor
  · rw [le_div_iff₀ hl]; linarith
  · rw [div_le_iff₀ hl]; linarith

/-- **Main theorem, `b > 0`, for `C_n`.** -/
theorem cost_rate {h : ℝ} (hh : κ.EqualEntropy h) (hb : 0 < (κ.fam h).sB) :
    ∃ K : ℝ, ∀ n : ℕ, 3 ≤ n →
      |κ.costBits n - n * h - secondOrderCoeff (κ.fam h).sA (κ.fam h).sB * Real.sqrt n| ≤
        K * (Real.sqrt (Real.sqrt n) * Real.log n) := by
  obtain ⟨K, hK⟩ := κ.sandwich_rate hh hb
  exact ⟨K, hK κ.costBits (fun n => (κ.costBits_sandwich n).1) (fun n => (κ.costBits_sandwich n).2)⟩

/-- **Main theorem, `b > 0`, for the greedy seed.** The constant is uniform over
any choice of the greedy seeds of `one_seed_shannon`. -/
theorem greedy_rate {h : ℝ} (hh : κ.EqualEntropy h) (hb : 0 < (κ.fam h).sB) :
    ∃ K : ℝ, ∀ n : ℕ, 3 ≤ n → ∃ atoms : List (Atom (κ.rounds n)),
      GreedyTrace (Field.p (κ.rounds n)) atoms ∧ totalWeight atoms = 1 ∧
      (∀ (π : Policy (κ.rounds n)) (ℓ : Leaf (κ.rounds n)),
        transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) ∧
      |seedShannon atoms - n * h - secondOrderCoeff (κ.fam h).sA (κ.fam h).sB * Real.sqrt n| ≤
        K * (Real.sqrt (Real.sqrt n) * Real.log n) := by
  obtain ⟨K, hK⟩ := κ.sandwich_rate hh hb
  refine ⟨K, fun n hn => ?_⟩
  choose atoms hat using fun m => one_seed_shannon (κ.rounds m)
  refine ⟨atoms n, (hat n).1, (hat n).2.2.1, (hat n).2.2.2.1, ?_⟩
  exact hK (fun m => seedShannon (atoms m)) (fun m => (hat m).2.2.2.2.1)
    (fun m => (hat m).2.2.2.2.2) n hn

end Kernel
end CausalSpectrum
