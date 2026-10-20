/-
Kernels whose output laws are deterministic images of one action's law.

If every output law `K_a` is the image `(f_a)_# K_{j₀}` of the law of one action `j₀`,
then one sample of `K_{j₀}` per round, read through the requested map, is an exact seed.
Hence `C_n = n h_max` for every `n`, and `H(K_{j₀}) = h_max`.
-/
import CausalSeed.Subadditive

noncomputable section
open Classical Finset
open scoped ENNReal

namespace CausalSpectrum.Kernel
open Completion
variable (κ : Kernel)

/-- `K_a = (f_a)_# K_{j₀}` for every action `a`. -/
def IsImage (j₀ : Fin κ.nA) (f : (a : Fin κ.nA) → Fin (κ.nY j₀) → Fin (κ.nY a)) : Prop :=
  ∀ a z, ∑ y ∈ univ.filter (fun y => f a y = z), κ.K j₀ y = κ.K a z

theorem finiteCost_le_alphabet {Ω : Type*} [Countable Ω] (S : AlphabetSeed κ.toITree Ω) (n : ℕ)
    (hS : S.ExactTo n) : finiteCost κ.toITree n ≤ S.entropy := by
  rw [← countableFiniteCost_eq, countableFiniteCost, ← S.toSeed_entropy]
  exact iInf_le_of_le ⟨S.toSeed, (S.toSeed_exactTo n).mpr hS⟩ le_rfl

/-- The one-point seed, exact to horizon `0`. -/
def unitSeed : AlphabetSeed κ.toITree Unit where
  weight _ := 1
  nonneg _ := zero_le_one
  mass := by simpa using hasSum_fintype (fun _ : Unit => (1 : ℝ))
  strategy _ := fun p => ⟨0, κ.hY p.2⟩

theorem costBits_zero : κ.costBits 0 = 0 := by
  have hex : κ.unitSeed.ExactTo 0 := by
    intro h hl
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)]
    simp [AlphabetSeed.hit, indAgree_nil, pathMass_nil, unitSeed]
  have h1 := κ.finiteCost_le_alphabet _ 0 hex
  have h0 : κ.unitSeed.entropy = 0 := by simp [AlphabetSeed.entropy, unitSeed]
  rw [h0, nonpos_iff_eq_zero] at h1
  simp [costBits, h1]

variable {κ}

/-- One sample of `K_{j₀}`, read through `f_a` at every node. -/
def imageSeed (j₀ : Fin κ.nA) (f : (a : Fin κ.nA) → Fin (κ.nY j₀) → Fin (κ.nY a)) :
    AlphabetSeed κ.toITree (Fin (κ.nY j₀)) where
  weight y := κ.K j₀ y
  nonneg y := (κ.Kpos j₀ y).le
  mass := by rw [← κ.Ksum j₀]; exact hasSum_fintype _
  strategy y := fun p => f p.2 y

theorem imageSeed_exactTo {j₀ : Fin κ.nA} {f} (hf : κ.IsImage j₀ f) :
    (imageSeed j₀ f).ExactTo 1 := by
  intro h hl
  match h, hl with
  | [], _ =>
    simp only [AlphabetSeed.hit, indAgree_nil, mul_one, tsum_fintype, pathMass_nil]
    exact κ.Ksum j₀
  | [p], _ =>
    simp only [AlphabetSeed.hit, indAgree, iAgree_iff, agreesFrom, and_true, tsum_fintype]
    by_cases ha : p.1 < κ.nA
    · by_cases hy : p.2 < κ.nY ⟨p.1, ha⟩
      · rw [pathMass, pm_cons_ok (ι := κ.toITree) ha hy, pm_nil, mul_one]
        have : ∀ y : Fin (κ.nY j₀), (∃ a : Fin κ.nA, a.val = p.1 ∧ (f a y).val = p.2) ↔
            f ⟨p.1, ha⟩ y = ⟨p.2, hy⟩ := fun y => by
          constructor
          · rintro ⟨a, h1, h2⟩
            have : a = ⟨p.1, ha⟩ := Fin.ext h1
            subst this; exact Fin.ext h2
          · intro e; exact ⟨⟨p.1, ha⟩, rfl, by rw [e]⟩
        show _ = κ.K ⟨p.1, ha⟩ ⟨p.2, hy⟩
        rw [← hf ⟨p.1, ha⟩ ⟨p.2, hy⟩, Finset.sum_filter]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases e : f ⟨p.1, ha⟩ y = ⟨p.2, hy⟩
        · rw [if_pos e]
          split_ifs with h'
          · simp [imageSeed]
          · exact absurd ((this y).2 e) h'
        · rw [if_neg e]
          split_ifs with h'
          · exact absurd ((this y).1 h') e
          · simp
      · rw [pathMass, pm_cons_out (ι := κ.toITree) ha hy]
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [ite_eq_right_iff.2 (fun h' => absurd h' ?_)]; · simp
        rintro ⟨a, h1, h2⟩
        have : a = ⟨p.1, ha⟩ := Fin.ext h1
        subst this
        exact hy (h2 ▸ (f _ y).isLt)
    · rw [pathMass, pm_cons_act (ι := κ.toITree) ha]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [ite_eq_right_iff.2 (fun h' => absurd h' ?_)]; · simp
      rintro ⟨a, h1, -⟩
      exact ha (h1 ▸ a.isLt)

theorem costBits_one_le {j₀ : Fin κ.nA} {f} (hf : κ.IsImage j₀ f) :
    κ.costBits 1 ≤ κ.actEntropy j₀ := by
  have h1 := κ.finiteCost_le_alphabet _ 1 (imageSeed_exactTo hf)
  have he : (imageSeed j₀ f).entropy = ENNReal.ofReal (Real.log 2 * κ.actEntropy j₀) := by
    simp only [AlphabetSeed.entropy, imageSeed, tsum_fintype]
    rw [← ENNReal.ofReal_sum_of_nonneg fun y _ =>
      Real.negMulLog_nonneg (κ.Kpos j₀ y).le (by
        have := κ.Ksum j₀
        exact this ▸ Finset.single_le_sum (fun y _ => (κ.Kpos j₀ y).le) (Finset.mem_univ y))]
    congr 1
    simp only [actEntropy, Finset.mul_sum, negMulLog_eq_bits]
  rw [he] at h1
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn : 0 ≤ Real.log 2 * κ.actEntropy j₀ := mul_nonneg hl.le (κ.actEntropy_nonneg j₀)
  unfold costBits
  rw [div_le_iff₀ hl]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal hn] at this
  linarith

/-- **Deterministic images.** If every output law is an image of `K_{j₀}`, then
`C_n = n · h_max` for every `n` and `H(K_{j₀}) = h_max`. -/
theorem costBits_eq_of_image {j₀ : Fin κ.nA} {f} (hf : κ.IsImage j₀ f) :
    κ.actEntropy j₀ = κ.hmax ∧ ∀ n : ℕ, κ.costBits n = n * κ.hmax := by
  have hup : ∀ n : ℕ, κ.costBits n ≤ n * κ.actEntropy j₀ := by
    intro n
    induction n with
    | zero => simp [κ.costBits_zero]
    | succ n ih =>
      have := κ.costBits_subadditive n 1
      have := costBits_one_le hf
      push_cast; linarith
  have hle : κ.actEntropy j₀ ≤ κ.hmax := Finset.le_sup' _ (Finset.mem_univ j₀)
  have heq : κ.actEntropy j₀ = κ.hmax := by
    have := κ.hmax_mul_le_costBits (n := 1) le_rfl
    have := hup 1
    push_cast at *; linarith
  refine ⟨heq, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [κ.costBits_zero]
  · have := κ.hmax_mul_le_costBits hn
    have := hup n
    rw [heq] at this
    linarith


/-! ## Superadditivity in one action: `C_{n+1} ≥ H(K_j) + C_n` -/

variable (κ)

/-- The strategy read after the first event `(a, z)`. -/
def shift (q : ℕ × ℕ) (s : IStrategy κ.toITree) : IStrategy κ.toITree :=
  fun p => s ⟨q :: p.1, p.2⟩

theorem agreesFrom_shift (q : ℕ × ℕ) (s : IStrategy κ.toITree) :
    ∀ (h pref : List (ℕ × ℕ)), agreesFrom κ.toITree s (q :: pref) h ↔
      agreesFrom κ.toITree (κ.shift q s) pref h := by
  intro h
  induction h with
  | nil => intro pref; simp [agreesFrom]
  | cons p t ih =>
    intro pref
    simp only [agreesFrom, List.cons_append, ih]
    exact Iff.rfl

theorem iAgree_cons (s : IStrategy κ.toITree) (a : Fin κ.nA) (z : Fin (κ.nY a))
    (h : List (ℕ × ℕ)) :
    iAgree κ.toITree s ((a.val, z.val) :: h) ↔
      s ⟨[], a⟩ = z ∧ iAgree κ.toITree (κ.shift (a.val, z.val) s) h := by
  rw [iAgree_iff, iAgree_iff, agreesFrom]
  constructor
  · rintro ⟨a', h1, h2, h3⟩
    have : a' = a := Fin.ext h1
    subst this
    exact ⟨Fin.ext h2, (κ.agreesFrom_shift _ _ h []).1 h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨a, rfl, by rw [h1], (κ.agreesFrom_shift _ _ h []).2 h2⟩

theorem indAgree_cons (s : IStrategy κ.toITree) (a : Fin κ.nA) (z : Fin (κ.nY a))
    (h : List (ℕ × ℕ)) :
    indAgree κ.toITree s ((a.val, z.val) :: h) =
      indAgree κ.toITree s [(a.val, z.val)] * indAgree κ.toITree (κ.shift (a.val, z.val) s) h := by
  unfold indAgree
  rw [propext (κ.iAgree_cons s a z h), propext (κ.iAgree_cons s a z [])]
  have := iAgree_nil κ.toITree (κ.shift (a.val, z.val) s)
  by_cases h1 : s ⟨[], a⟩ = z <;>
    by_cases h2 : iAgree κ.toITree (κ.shift (a.val, z.val) s) h <;> simp [h1, h2, this]

theorem indAgree_single (s : IStrategy κ.toITree) (a : Fin κ.nA) (z : Fin (κ.nY a)) :
    indAgree κ.toITree s [(a.val, z.val)] = if s ⟨[], a⟩ = z then 1 else 0 := by
  unfold indAgree
  rw [propext (κ.iAgree_cons s a z [])]
  simp [iAgree_nil]

theorem pathMass_cons (a : Fin κ.nA) (z : Fin (κ.nY a)) (h : List (ℕ × ℕ)) :
    pathMass κ.toITree ((a.val, z.val) :: h) = κ.K a z * pathMass κ.toITree h := by
  rw [pathMass, pm_cons_ok (ι := κ.toITree) a.isLt z.isLt, κ.pm_stationary]
  rfl

/-- The seed conditioned on the first output `y` of action `j`, read from round `2` on. -/
def condSeed (S : Seed κ.toITree) (j : Fin κ.nA) (y : Fin (κ.nY j))
    (hS : S.ExactTo 1) : AlphabetSeed κ.toITree ℕ where
  weight i := S.hit [(j.val, y.val)] i / κ.K j y
  nonneg i := div_nonneg (mul_nonneg (S.nonneg i) (indAgree_nonneg _ _ _)) (κ.Kpos j y).le
  mass := by
    have h1 := (S.hit_summable [(j.val, y.val)]).hasSum.div_const (κ.K j y)
    rwa [hS _ (by simp), κ.pathMass_cons j y [], pathMass_nil, mul_one,
      div_self (κ.Kpos j y).ne'] at h1
  strategy i := κ.shift (j.val, y.val) (S.strategy i)

theorem condSeed_exactTo (S : Seed κ.toITree) (j : Fin κ.nA) (y : Fin (κ.nY j)) {n : ℕ}
    (hS : S.ExactTo (n + 1)) :
    (κ.condSeed S j y (fun h hl => hS h (by omega))).ExactTo n := by
  intro h hl
  have e : ∀ i, (κ.condSeed S j y (fun h hl => hS h (by omega))).hit h i =
      S.hit ((j.val, y.val) :: h) i / κ.K j y := fun i => by
    show S.weight i * indAgree κ.toITree (S.strategy i) [(j.val, y.val)] / κ.K j y *
        indAgree κ.toITree (κ.shift (j.val, y.val) (S.strategy i)) h =
      S.weight i * indAgree κ.toITree (S.strategy i) ((j.val, y.val) :: h) / κ.K j y
    rw [κ.indAgree_cons (S.strategy i) j y h]
    ring
  rw [tsum_congr e, tsum_div_const, hS _ (by simp; omega), κ.pathMass_cons, mul_div_cancel_left₀ _ (κ.Kpos j y).ne']

theorem weight_le_one' {Ω : Type*} (G : AlphabetSeed κ.toITree Ω) (i : Ω) : G.weight i ≤ 1 :=
  G.mass.tsum_eq ▸ G.mass.summable.le_tsum i fun j _ => G.nonneg j

/-- **One-step superadditivity** (nats): `C_{n+1} ≥ H(K_j) + C_n` for every action `j`. -/
theorem finiteCost_succ_ge (j : Fin κ.nA) (n : ℕ) :
    ENNReal.ofReal (Real.log 2 * κ.actEntropy j) + finiteCost κ.toITree n ≤
      finiteCost κ.toITree (n + 1) := by
  conv_rhs => rw [← countableFiniteCost_eq, countableFiniteCost]
  refine le_iInf fun ⟨S, hS⟩ => ?_
  have hS1 : S.ExactTo 1 := fun h hl => hS h (by omega)
  set u := fun (y : Fin (κ.nY j)) => κ.condSeed S j y hS1
  have hK1 : ∀ y, κ.K j y ≤ 1 := fun y => by
    have := κ.Ksum j
    exact this ▸ Finset.single_le_sum (fun y _ => (κ.Kpos j y).le) (Finset.mem_univ y)
  -- each weight is the sum over `y` of `K_y u^y_i`, with one nonzero term
  have hw : ∀ i, ENNReal.ofReal (Real.negMulLog (S.weight i)) =
      ∑ y, ENNReal.ofReal (Real.negMulLog (κ.K j y * (u y).weight i)) := by
    intro i
    have hk : ∀ y, κ.K j y * (u y).weight i = S.hit [(j.val, y.val)] i := fun y => by
      simp only [u, condSeed]; field_simp [(κ.Kpos j y).ne']
    obtain ⟨r, hr⟩ : ∃ r : Fin (κ.nY j), S.strategy i ⟨[], j⟩ = r := ⟨_, rfl⟩
    have hh : ∀ y : Fin (κ.nY j), S.hit [(j.val, y.val)] i = if r = y then S.weight i else 0 :=
      fun y => by
        show S.weight i * indAgree κ.toITree (S.strategy i) [(j.val, y.val)] = _
        rw [κ.indAgree_single, hr]
        by_cases e : r = y <;> simp [e] <;> first | exact fun h' => absurd rfl h' | exact fun h' => absurd h' e
    simp only [hk, hh]
    rw [Finset.sum_eq_single_of_mem r (Finset.mem_univ _)]
    · simp
    · intro y _ hy
      rw [if_neg (Ne.symm hy)]; simp
  have hsplit : ∀ y, ∑' i, ENNReal.ofReal (Real.negMulLog (κ.K j y * (u y).weight i)) =
      ENNReal.ofReal (Real.negMulLog (κ.K j y)) + ENNReal.ofReal (κ.K j y) * (u y).entropy := by
    intro y
    have hK0 := (κ.Kpos j y).le
    have hN : ∀ i, 0 ≤ Real.negMulLog ((u y).weight i) := fun i =>
      Real.negMulLog_nonneg ((u y).nonneg i) (κ.weight_le_one' _ i)
    have hNK : 0 ≤ Real.negMulLog (κ.K j y) := Real.negMulLog_nonneg hK0 (hK1 y)
    have hterm : ∀ i, ENNReal.ofReal (Real.negMulLog (κ.K j y * (u y).weight i)) =
        ENNReal.ofReal ((u y).weight i) * ENNReal.ofReal (Real.negMulLog (κ.K j y)) +
          ENNReal.ofReal (κ.K j y) * ENNReal.ofReal (Real.negMulLog ((u y).weight i)) := by
      intro i
      rw [Real.negMulLog_mul, ENNReal.ofReal_add (mul_nonneg ((u y).nonneg i) hNK)
        (mul_nonneg hK0 (hN i)), ENNReal.ofReal_mul ((u y).nonneg i), ENNReal.ofReal_mul hK0]
    have h1 : ∑' i, ENNReal.ofReal ((u y).weight i) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (u y).nonneg (u y).mass.summable, (u y).mass.tsum_eq]
      simp
    simp only [hterm]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, h1, one_mul]
    rfl
  have hent : S.entropy = ∑ y, (ENNReal.ofReal (Real.negMulLog (κ.K j y)) +
      ENNReal.ofReal (κ.K j y) * (u y).entropy) := by
    simp only [CountableSeed.entropy, hw]
    rw [Summable.tsum_finsetSum fun y _ => ENNReal.summable]
    simp only [hsplit]
  have hcost : ∀ y, finiteCost κ.toITree n ≤ (u y).entropy := fun y =>
    κ.finiteCost_le_alphabet _ n (κ.condSeed_exactTo S j y hS)
  calc ENNReal.ofReal (Real.log 2 * κ.actEntropy j) + finiteCost κ.toITree n
      = ∑ y, (ENNReal.ofReal (Real.negMulLog (κ.K j y)) +
          ENNReal.ofReal (κ.K j y) * finiteCost κ.toITree n) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul,
          ← ENNReal.ofReal_sum_of_nonneg fun y _ => (κ.Kpos j y).le, κ.Ksum j, ENNReal.ofReal_one,
          one_mul, ← ENNReal.ofReal_sum_of_nonneg fun y _ =>
            Real.negMulLog_nonneg (κ.Kpos j y).le (hK1 y)]
        congr 2
        simp only [actEntropy, Finset.mul_sum, negMulLog_eq_bits]
    _ ≤ S.entropy := by
        rw [hent]
        gcongr with y
        exact hcost y

/-- **One-step superadditivity** (bits): `C_{n+1} ≥ H(K_j) + C_n`. -/
theorem costBits_succ_ge (j : Fin κ.nA) (n : ℕ) :
    κ.actEntropy j + κ.costBits n ≤ κ.costBits (n + 1) := by
  have h := κ.finiteCost_succ_ge j n
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn : 0 ≤ Real.log 2 * κ.actEntropy j := mul_nonneg hl.le (κ.actEntropy_nonneg j)
  have h2 := ENNReal.toReal_mono (κ.finiteCost_ne_top _) h
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (κ.finiteCost_ne_top _),
    ENNReal.toReal_ofReal hn] at h2
  unfold costBits
  rw [le_div_iff₀ hl, add_mul, div_mul_cancel₀ _ hl.ne']
  linarith

/-- The residual `C_n - n h_max` is nondecreasing in `n`. -/
theorem residual_mono : Monotone fun n : ℕ => κ.costBits n - n * κ.hmax := by
  obtain ⟨j, hj⟩ := κ.exists_hmax
  refine monotone_nat_of_le_succ fun n => ?_
  have := κ.costBits_succ_ge j n
  push_cast
  linarith

theorem residual_nonneg (n : ℕ) : 0 ≤ κ.costBits n - n * κ.hmax := by
  have := κ.residual_mono (Nat.zero_le n)
  simpa [κ.costBits_zero] using this

/-- If the residual is bounded, `C_n - n h_max` increases to a finite limit `ℓ ≥ 0`. -/
theorem residual_tendsto (hb : BddAbove (Set.range fun n : ℕ => κ.costBits n - n * κ.hmax)) :
    Filter.Tendsto (fun n : ℕ => κ.costBits n - n * κ.hmax) Filter.atTop
      (nhds (⨆ n : ℕ, (κ.costBits n - n * κ.hmax))) :=
  tendsto_atTop_ciSup κ.residual_mono hb

/-- A residual that vanishes at some `n ≥ 1` vanishes at every horizon up to `n`. -/
theorem residual_eq_zero_of_le {m n : ℕ} (hmn : m ≤ n) (h0 : κ.costBits n = n * κ.hmax) :
    κ.costBits m = m * κ.hmax := by
  have h1 := κ.residual_mono hmn
  have h2 := κ.residual_nonneg m
  simp only at h1
  linarith

end CausalSpectrum.Kernel
