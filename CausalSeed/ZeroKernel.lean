/-
Stationary kernels with zero entries.

A nonnegative stationary kernel `κ₀` is unrolled for `n` rounds as a `ZTree` that keeps
every branch, including the zero-probability ones. Its reduction `κ₀.red` is the positive
kernel obtained by deleting the zero entries of every output law. The envelope of the
`n`-round `ZTree` equals the envelope of the reduced positive tree, so the optimal exact
cost of the full tree is sandwiched between `L_n(κ₀.red)` and `L_n(κ₀.red) + c⋆`, and the
causal floor and the square-root asymptotics extend to nonnegative kernels.
-/
import CausalSeed.ZeroClosure
import CausalSeed.CausalFloor
import CausalSeed.SqrtMain

noncomputable section
open Classical Finset Filter Topology

namespace CausalSpectrum.Zero

open Shape

/-! ## The sum-over-leaves functional and its recursion -/

/-- `Φ(c, π, t) = Σ_ℓ [ℓ ⊨ π ∧ 2^{-t} ≤ c·m(ℓ)] · c·m(ℓ)`. -/
def Phi {S : Shape} (k : KField S) (π : Pol S) (c t : ℝ) : ℝ :=
  ∑ ℓ, if compat ℓ π ∧ (2:ℝ) ^ (-t) ≤ c * mass k ℓ then c * mass k ℓ else 0

theorem Phi_zero {S : Shape} (k : KField S) (π : Pol S) (t : ℝ) : Phi k π 0 t = 0 := by
  unfold Phi
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  have : ¬ ((2:ℝ) ^ (-t) ≤ 0 * mass k ℓ) := by
    rw [zero_mul, not_le]; positivity
  simp [this]

theorem Phi_node {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {child : (a : Fin nA) → Fin (nY a) → Shape}
    (k : KField (.node nA hA nY hY child)) (π : Pol (.node nA hA nY hY child)) (c t : ℝ) :
    Phi k π c t = ∑ y, Phi (k.2 π.1 y) (π.2 π.1 y) (c * k.1 π.1 y) t := by
  unfold Phi
  rw [show (∑ ℓ : Lf (.node nA hA nY hY child), _) =
      ∑ x : (Σ' a, Σ' y, Lf (child a y)), _ from rfl, CausalSpectrum.sum_psigma]
  simp_rw [CausalSpectrum.sum_psigma]
  rw [Finset.sum_eq_single π.1]
  · refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [compat, mass, true_and, mul_assoc]
  · intro a _ ha
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun ℓ _ => ?_
    simp [compat, ha]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Nonnegative stationary kernels -/

structure NNKernel where
  nA : ℕ
  hA : 0 < nA
  nY : Fin nA → ℕ
  hY : ∀ a, 0 < nY a
  K : (a : Fin nA) → Fin (nY a) → ℝ
  Knn : ∀ a y, 0 ≤ K a y
  Ksum : ∀ a, ∑ y, K a y = 1

namespace NNKernel
variable (κ : NNKernel)

/-- The support of the output law of action `a`. -/
def supp (a : Fin κ.nA) : Finset (Fin (κ.nY a)) := univ.filter fun y => 0 < κ.K a y

theorem supp_nonempty (a : Fin κ.nA) : (κ.supp a).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have : ∀ y, κ.K a y = 0 := fun y => by
    have hy : y ∉ κ.supp a := by simp [h]
    simp only [supp, mem_filter, mem_univ, true_and, not_lt] at hy
    exact le_antisymm hy (κ.Knn a y)
  have h1 := κ.Ksum a
  rw [Finset.sum_eq_zero (fun y _ => this y)] at h1
  norm_num at h1

/-- Enumeration of the support. -/
def emb (a : Fin κ.nA) : Fin (κ.supp a).card ≃o κ.supp a := (κ.supp a).orderIsoOfFin rfl

theorem K_emb_pos (a : Fin κ.nA) (i : Fin (κ.supp a).card) : 0 < κ.K a (κ.emb a i).1 := by
  exact (Finset.mem_filter.1 (κ.emb a i).2).2

theorem sum_emb (a : Fin κ.nA) (f : Fin (κ.nY a) → ℝ) (hf : ∀ y, κ.K a y = 0 → f y = 0) :
    ∑ i, f (κ.emb a i).1 = ∑ y, f y := by
  rw [Fintype.sum_equiv (κ.emb a).toEquiv (fun i => f (κ.emb a i).1) (fun y => f y.1)
    (fun _ => rfl), Finset.sum_coe_sort]
  refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => hf y ?_
  simp only [supp, mem_filter, mem_univ, true_and, not_lt] at hy
  exact le_antisymm hy (κ.Knn a y)

/-- The reduced positive kernel: zero entries deleted. -/
def red : Kernel where
  nA := κ.nA
  hA := κ.hA
  nY a := (κ.supp a).card
  hY a := Finset.card_pos.2 (κ.supp_nonempty a)
  K a i := κ.K a (κ.emb a i).1
  Kpos := κ.K_emb_pos
  Ksum a := by rw [κ.sum_emb a (κ.K a) (fun _ h => h)]; exact κ.Ksum a

/-- The `n`-round shape with every branch kept. -/
def shape : ℕ → Shape
  | 0 => .leaf
  | n + 1 => .node κ.nA κ.hA κ.nY κ.hY fun _ _ => shape n

def kf : (n : ℕ) → KField (κ.shape n)
  | 0 => PUnit.unit
  | n + 1 => (κ.K, fun _ _ => kf n)

theorem valid : ∀ n, Valid (κ.shape n) (κ.kf n)
  | 0 => trivial
  | n + 1 => ⟨κ.Knn, κ.Ksum, fun _ _ => valid n⟩

/-- The `n`-round tree of `κ₀`, all zero-probability branches retained. -/
def ztree (n : ℕ) : ZTree := ⟨κ.shape n, κ.kf n, κ.valid n⟩

/-! ## Restricting and extending policies -/

def restrict : (n : ℕ) → Pol (κ.shape n) → Pol (shapeOf (κ.red.rounds n))
  | 0, _ => PUnit.unit
  | n + 1, π => (π.1, fun a i => restrict n (π.2 a (κ.emb a i).1))

def extend : (n : ℕ) → Pol (shapeOf (κ.red.rounds n)) → Pol (κ.shape n)
  | 0, _ => PUnit.unit
  | n + 1, π => (π.1, fun a y =>
      if h : y ∈ κ.supp a then extend n (π.2 a ((κ.emb a).symm ⟨y, h⟩)) else defaultPol _)

theorem Phi_restrict : ∀ (n : ℕ) (π : Pol (κ.shape n)) (c t : ℝ), 0 ≤ c →
    Phi (κ.kf n) π c t = Phi (kernelOf (κ.red.rounds n)) (κ.restrict n π) c t
  | 0, π, c, t, _ => rfl
  | n + 1, π, c, t, hc => by
      refine (Phi_node (κ.kf (n+1)) π c t).trans (Eq.trans ?_
        (Phi_node (kernelOf (κ.red.rounds (n+1))) (κ.restrict (n+1) π) c t).symm)
      show ∑ y, Phi (κ.kf n) (π.2 π.1 y) (c * κ.K π.1 y) t =
        ∑ i, Phi (kernelOf (κ.red.rounds n)) (κ.restrict n (π.2 π.1 (κ.emb π.1 i).1))
          (c * κ.K π.1 (κ.emb π.1 i).1) t
      rw [← κ.sum_emb π.1 _ (fun y hy => by rw [hy, mul_zero, Phi_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Phi_restrict n _ _ t (mul_nonneg hc (κ.Knn _ _))

theorem Phi_extend : ∀ (n : ℕ) (π : Pol (shapeOf (κ.red.rounds n))) (c t : ℝ), 0 ≤ c →
    Phi (kernelOf (κ.red.rounds n)) π c t = Phi (κ.kf n) (κ.extend n π) c t
  | 0, π, c, t, _ => rfl
  | n + 1, π, c, t, hc => by
      refine (Phi_node (kernelOf (κ.red.rounds (n+1))) π c t).trans (Eq.trans ?_
        (Phi_node (κ.kf (n+1)) (κ.extend (n+1) π) c t).symm)
      show ∑ i, Phi (kernelOf (κ.red.rounds n)) (π.2 π.1 i) (c * κ.K π.1 (κ.emb π.1 i).1) t =
        ∑ y, Phi (κ.kf n) ((κ.extend (n + 1) π).2 π.1 y) (c * κ.K π.1 y) t
      rw [← κ.sum_emb π.1 _ (fun y hy => by rw [hy, mul_zero, Phi_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (κ.emb π.1 i).1 ∈ κ.supp π.1 := (κ.emb π.1 i).2
      show _ = Phi (κ.kf n) (if h : (κ.emb π.1 i).1 ∈ κ.supp π.1 then
        κ.extend n (π.2 π.1 ((κ.emb π.1).symm ⟨_, h⟩)) else defaultPol _) _ t
      rw [dif_pos hi]
      simp only [Subtype.coe_eta]
      rw [(κ.emb π.1).symm_apply_apply i]
      exact Phi_extend n _ _ t (mul_nonneg hc (κ.Knn _ _))

/-! ## The envelope of the full tree is the envelope of the reduced tree -/

theorem Sp_eq_Phi {S : Shape} (k : KField S) (π : Pol S) (t : ℝ) :
    Sp (P := Pol S) compat (mass k) π t = Phi k π 1 t := by
  unfold Sp Phi; simp only [one_mul]

theorem F_ztree (n : ℕ) (t : ℝ) : (κ.ztree n).F t = (ZTree.ofTree (κ.red.rounds n)).F t := by
  unfold ZTree.F Fenv ZTree.P
  apply le_antisymm
  · refine Finset.le_inf' _ _ fun πr _ => ?_
    refine (Finset.inf'_le _ (Finset.mem_univ (κ.extend n πr))).trans_eq ?_
    show Sp compat (mass (κ.kf n)) (κ.extend n πr) t =
      Sp compat (mass (kernelOf (κ.red.rounds n))) πr t
    exact (Sp_eq_Phi (κ.kf n) (κ.extend n πr) t).trans ((κ.Phi_extend n πr 1 t
      zero_le_one).symm.trans (Sp_eq_Phi (kernelOf (κ.red.rounds n)) πr t).symm)
  · refine Finset.le_inf' _ _ fun π _ => ?_
    refine (Finset.inf'_le _ (Finset.mem_univ (κ.restrict n π))).trans_eq ?_
    show Sp compat (mass (kernelOf (κ.red.rounds n))) (κ.restrict n π) t =
      Sp compat (mass (κ.kf n)) π t
    exact (Sp_eq_Phi (kernelOf (κ.red.rounds n)) (κ.restrict n π) t).trans
      ((κ.Phi_restrict n π 1 t zero_le_one).symm.trans (Sp_eq_Phi (κ.kf n) π t).symm)

/-- The envelope of the `n`-round tree of `κ₀` is the envelope mean `L_n` of `κ₀.red`. -/
theorem L_ztree (n : ℕ) : (κ.ztree n).L = envelopeMean (κ.red.rounds n) := by
  rw [← ZTree.L_ofTree]
  unfold ZTree.L Lenv
  congr 1
  funext t
  exact congrArg (1 - ·) (κ.F_ztree n t)

end NNKernel

/-! ## The optimal exact cost of a tree with zero branches -/

/-- `C(Z)`: the least Shannon entropy (bits) of a law on deterministic response
strategies that is exact for every deterministic adaptive policy. -/
def zcost (Z : ZTree) : ℝ :=
  sInf {x | ∃ q : Z.Str → ℝ, IsPmf q ∧
    (∀ (π : Z.Pol) (ℓ : Z.Lf),
      (∑ s, if Shape.run s π = ℓ then q s else 0) = if compat ℓ π then Z.P ℓ else 0) ∧
    x = pmfEntropy q}

theorem zcost_sandwich (Z : ZTree) : Z.L ≤ zcost Z ∧ zcost Z ≤ Z.L + shannonOverhead := by
  obtain ⟨q, hq, he, -, hup⟩ := zero_closure Z
  have hne : {x | ∃ q : Z.Str → ℝ, IsPmf q ∧
      (∀ (π : Z.Pol) (ℓ : Z.Lf),
        (∑ s, if Shape.run s π = ℓ then q s else 0) = if compat ℓ π then Z.P ℓ else 0) ∧
      x = pmfEntropy q}.Nonempty := ⟨_, q, hq, he, rfl⟩
  have hlb : ∀ x ∈ {x | ∃ q : Z.Str → ℝ, IsPmf q ∧
      (∀ (π : Z.Pol) (ℓ : Z.Lf),
        (∑ s, if Shape.run s π = ℓ then q s else 0) = if compat ℓ π then Z.P ℓ else 0) ∧
      x = pmfEntropy q}, Z.L ≤ x := by
    rintro x ⟨q', hq', he', rfl⟩; exact zero_lower Z hq' he'
  exact ⟨le_csInf hne hlb, (csInf_le ⟨Z.L, hlb⟩ ⟨q, hq, he, rfl⟩).trans hup⟩

namespace NNKernel
variable (κ : NNKernel)

/-- `C_n(κ₀)`: the optimal exact cost (bits) of the `n`-round tree of `κ₀`, zero branches kept. -/
def costBits (n : ℕ) : ℝ := zcost (κ.ztree n)

theorem costBits_sandwich (n : ℕ) :
    envelopeMean (κ.red.rounds n) ≤ κ.costBits n ∧
      κ.costBits n ≤ envelopeMean (κ.red.rounds n) + shannonOverhead := by
  rw [← κ.L_ztree]; exact zcost_sandwich _

/-- The action entropies of the reduction are those of `κ₀` (with `0 log 0 = 0`). -/
theorem red_actEntropy (a : Fin κ.nA) :
    κ.red.actEntropy a = ∑ y, κ.K a y * infoMass (κ.K a y) :=
  κ.sum_emb a (fun y => κ.K a y * infoMass (κ.K a y)) (fun y hy => by rw [hy, zero_mul])

/-- `h_max(κ₀) = max_a H(K(a, ·))` (bits). -/
def hmax : ℝ := Finset.univ.sup' κ.red.univA_nonempty fun a => ∑ y, κ.K a y * infoMass (κ.K a y)

theorem hmax_eq : κ.hmax = κ.red.hmax := by
  unfold hmax Kernel.hmax; congr 1; funext a; exact (κ.red_actEntropy a).symm

theorem cost_floor_bounds {n : ℕ} (hn : 1 ≤ n) :
    n * κ.hmax - Real.sqrt n * κ.red.floorConst κ.red.hmax ≤ κ.costBits n ∧
      κ.costBits n ≤ n * κ.hmax + Real.sqrt n * κ.red.floorConst κ.red.hmax + shannonOverhead := by
  rw [κ.hmax_eq]
  exact ⟨(κ.red.floor_le_envelope hn).trans (κ.costBits_sandwich n).1,
    (κ.costBits_sandwich n).2.trans (by linarith [κ.red.envelope_le_floor hn])⟩

/-- **Causal Shannon floor for nonnegative kernels**: `C_n(κ₀)/n → h_max(κ₀)`. -/
theorem causal_floor : Tendsto (fun n : ℕ => κ.costBits n / n) atTop (𝓝 κ.hmax) :=
  Kernel.floor_squeeze (fun n hn => (κ.cost_floor_bounds hn).1)
    (fun n hn => (κ.cost_floor_bounds hn).2)

/-- **Square-root asymptotics for nonnegative kernels.** -/
theorem cost_tendsto {h : ℝ} (hh : κ.red.EqualEntropy h) :
    Tendsto (fun n : ℕ => (κ.costBits n - n * h) / Real.sqrt n) atTop
      (𝓝 (secondOrderCoeff (κ.red.fam h).sA (κ.red.fam h).sB)) := by
  have hL := κ.red.envelope_tendsto hh
  have hc : Tendsto (fun n : ℕ => shannonOverhead / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hU := hL.add hc
  rw [add_zero] at hU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    exact div_le_div_of_nonneg_right (by linarith [(κ.costBits_sandwich n).1]) hs.le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith [(κ.costBits_sandwich n).2]) hs.le

/-- **Rate for nonnegative kernels** when `b > 0`: `O(n^{1/4} log n)`. -/
theorem cost_rate {h : ℝ} (hh : κ.red.EqualEntropy h) (hb : 0 < (κ.red.fam h).sB) :
    ∃ K : ℝ, ∀ n : ℕ, 3 ≤ n →
      |κ.costBits n - n * h - secondOrderCoeff (κ.red.fam h).sA (κ.red.fam h).sB * Real.sqrt n| ≤
        K * (Real.sqrt (Real.sqrt n) * Real.log n) := by
  obtain ⟨K, hK⟩ := κ.red.envelope_rate hh hb
  have hc0 : 0 ≤ shannonOverhead := by
    unfold shannonOverhead; positivity
  refine ⟨K + shannonOverhead, fun n hn => ?_⟩
  have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hq : 1 ≤ Real.sqrt (Real.sqrt n) := by
    rw [Real.one_le_sqrt, Real.one_le_sqrt]; linarith
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hprod : 1 ≤ Real.sqrt (Real.sqrt n) * Real.log n := by nlinarith
  have := hK n hn
  have hs := κ.costBits_sandwich n
  set E := envelopeMean (κ.red.rounds n) - n * h -
    secondOrderCoeff (κ.red.fam h).sA (κ.red.fam h).sB * Real.sqrt n
  have hsplit : κ.costBits n - n * h -
      secondOrderCoeff (κ.red.fam h).sA (κ.red.fam h).sB * Real.sqrt n =
      E + (κ.costBits n - envelopeMean (κ.red.rounds n)) := by simp only [E]; ring
  have hd : |κ.costBits n - envelopeMean (κ.red.rounds n)| ≤ shannonOverhead := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  rw [hsplit, add_mul]
  calc |E + (κ.costBits n - envelopeMean (κ.red.rounds n))| ≤ |E| + shannonOverhead :=
        (abs_add_le _ _).trans (by linarith)
    _ ≤ _ := by nlinarith

end NNKernel
end CausalSpectrum.Zero
