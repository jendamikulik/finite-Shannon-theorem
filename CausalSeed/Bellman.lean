/-
The discrete Bellman envelope.
A finite family of finite increment laws; every round all actions are
available with the same laws, and an adaptive policy may use the whole
observed history. `cdfPol π x = P(S_n^π ≤ x)`, `G n x = inf_π P(S_n^π ≤ x)`.
-/
import CausalSeed.SecondOrder

noncomputable section
open Classical Finset
namespace CausalSpectrum.Sqrt

structure IncFamily where
  nA : ℕ
  hA : 0 < nA
  nY : Fin nA → ℕ
  hY : ∀ j, 0 < nY j
  P : (j : Fin nA) → Fin (nY j) → ℝ
  Ppos : ∀ j y, 0 < P j y
  Psum : ∀ j, ∑ y, P j y = 1
  X : (j : Fin nA) → Fin (nY j) → ℝ

namespace IncFamily
variable (F : IncFamily)

theorem univ_nonempty : (Finset.univ : Finset (Fin F.nA)).Nonempty :=
  ⟨⟨0, F.hA⟩, Finset.mem_univ _⟩

/-- `E f(x - X_j)`. -/
def expect (j : Fin F.nA) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑ y, F.P j y * f (x - F.X j y)

/-- The Bellman operator `(Tf)(x) = min_j E f(x - X_j)`. -/
def T (f : ℝ → ℝ) (x : ℝ) : ℝ := Finset.univ.inf' F.univ_nonempty (fun j => F.expect j f x)

def G : ℕ → ℝ → ℝ
  | 0 => fun x => if 0 ≤ x then 1 else 0
  | n + 1 => F.T (G n)

/-! ### Adaptive policies -/

def APol : ℕ → Type
  | 0 => PUnit
  | n + 1 => Σ j : Fin F.nA, (Fin (F.nY j) → APol n)

/-- `P(S_n^π ≤ x)`: the first increment is drawn after the action, the
continuation policy may depend on its outcome. -/
def cdfPol : (n : ℕ) → F.APol n → ℝ → ℝ
  | 0, _ => fun x => if 0 ≤ x then 1 else 0
  | n + 1, π => fun x => ∑ y, F.P π.1 y * cdfPol n (π.2 y) (x - F.X π.1 y)

theorem T_le (f : ℝ → ℝ) (x : ℝ) (j : Fin F.nA) : F.T f x ≤ F.expect j f x :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem T_attained (f : ℝ → ℝ) (x : ℝ) : ∃ j, F.T f x = F.expect j f x := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' F.univ_nonempty (fun j => F.expect j f x)
  exact ⟨j, hj⟩

theorem le_T {f : ℝ → ℝ} {x c : ℝ} (h : ∀ j, c ≤ F.expect j f x) : c ≤ F.T f x :=
  Finset.le_inf' _ _ fun j _ => h j

/-- Bellman identity: `G n` is the envelope over adaptive policies, attained. -/
theorem G_envelope : ∀ (n : ℕ) (x : ℝ),
    (∀ π : F.APol n, F.G n x ≤ F.cdfPol n π x) ∧ ∃ π : F.APol n, F.cdfPol n π x = F.G n x
  | 0, x => ⟨fun _ => le_rfl, ⟨PUnit.unit, rfl⟩⟩
  | n + 1, x => by
    constructor
    · intro π
      refine (F.T_le (F.G n) x π.1).trans ?_
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left ((G_envelope n _).1 (π.2 y)) (F.Ppos _ _).le
    · obtain ⟨j, hj⟩ := F.T_attained (F.G n) x
      have hc := fun y : Fin (F.nY j) => (G_envelope n (x - F.X j y)).2
      choose k hk using hc
      refine ⟨⟨j, k⟩, ?_⟩
      change ∑ y, F.P j y * F.cdfPol n (k y) (x - F.X j y) = F.T (F.G n) x
      rw [hj]
      unfold expect
      simp only [hk]

def defaultPol : (n : ℕ) → F.APol n
  | 0 => PUnit.unit
  | n + 1 => ⟨⟨0, F.hA⟩, fun _ => defaultPol n⟩

instance (n : ℕ) : Nonempty (F.APol n) := ⟨F.defaultPol n⟩

theorem G_eq_iInf (n : ℕ) (x : ℝ) : F.G n x = ⨅ π : F.APol n, F.cdfPol n π x := by
  obtain ⟨h1, π, hπ⟩ := F.G_envelope n x
  apply le_antisymm
  · exact le_ciInf h1
  · rw [← hπ]
    exact ciInf_le ⟨F.G n x, fun _ ⟨σ, hσ⟩ => hσ ▸ h1 σ⟩ π

theorem G_succ (n : ℕ) : F.G (n + 1) = F.T (F.G n) := rfl

/-! ### Properties of `T` -/

theorem expect_mono (j) {f g : ℝ → ℝ} (h : ∀ x, f x ≤ g x) (x) :
    F.expect j f x ≤ F.expect j g x :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h _) (F.Ppos _ _).le

theorem T_mono {f g : ℝ → ℝ} (h : ∀ x, f x ≤ g x) (x : ℝ) : F.T f x ≤ F.T g x := by
  obtain ⟨j, hj⟩ := F.T_attained g x
  rw [hj]
  exact (F.T_le f x j).trans (F.expect_mono j h x)

theorem expect_const (j) (c x : ℝ) : F.expect j (fun _ => c) x = c := by
  simp [expect, ← Finset.sum_mul, F.Psum]

theorem expect_add_const (j) (f : ℝ → ℝ) (c x : ℝ) :
    F.expect j (fun z => f z + c) x = F.expect j f x + c := by
  simp only [expect, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, F.Psum, one_mul]

theorem T_add_const (f : ℝ → ℝ) (c x : ℝ) : F.T (fun z => f z + c) x = F.T f x + c := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := F.T_attained f x
    rw [hj, ← F.expect_add_const]; exact F.T_le _ x j
  · obtain ⟨j, hj⟩ := F.T_attained (fun z => f z + c) x
    rw [hj, F.expect_add_const]; linarith [F.T_le f x j]

theorem T_translate (f : ℝ → ℝ) (c x : ℝ) : F.T (fun z => f (z + c)) x = F.T f (x + c) := by
  unfold T expect
  congr 1; funext j; apply Finset.sum_congr rfl; intro y _
  simp only [show x - F.X j y + c = x + c - F.X j y by ring]

/-- Sup-norm contraction, pointwise form. -/
theorem T_contraction {f g : ℝ → ℝ} {ε : ℝ} (h : ∀ x, |f x - g x| ≤ ε) (x : ℝ) :
    |F.T f x - F.T g x| ≤ ε := by
  have h1 : ∀ z, f z ≤ g z + ε := fun z => by linarith [(abs_le.mp (h z)).2]
  have h2 : ∀ z, g z ≤ f z + ε := fun z => by linarith [(abs_le.mp (h z)).1]
  have a1 := F.T_mono h1 x
  have a2 := F.T_mono h2 x
  rw [F.T_add_const] at a1 a2
  rw [abs_le]; constructor <;> linarith

/-! ### `G n` is a distribution function -/

def M : ℝ := Finset.univ.sup' F.univ_nonempty (fun j =>
  (Finset.univ : Finset (Fin (F.nY j))).sup' ⟨⟨0, F.hY j⟩, Finset.mem_univ _⟩
    (fun y => |F.X j y|))

theorem abs_X_le (j y) : |F.X j y| ≤ F.M :=
  le_trans (Finset.le_sup' (fun y => |F.X j y|) (Finset.mem_univ y))
    (Finset.le_sup' (fun j => (Finset.univ : Finset (Fin (F.nY j))).sup'
      ⟨⟨0, F.hY j⟩, Finset.mem_univ _⟩ (fun y => |F.X j y|)) (Finset.mem_univ j))

theorem M_nonneg : 0 ≤ F.M := (abs_nonneg _).trans (F.abs_X_le ⟨0, F.hA⟩ ⟨0, F.hY _⟩)

theorem T_monotone {f : ℝ → ℝ} (hf : Monotone f) : Monotone (F.T f) := by
  intro x x' hx
  obtain ⟨j, hj⟩ := F.T_attained f x'
  rw [hj]
  refine (F.T_le f x j).trans ?_
  exact Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (hf (by linarith)) (F.Ppos _ _).le

theorem T_bounds {f : ℝ → ℝ} (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (x : ℝ) :
    0 ≤ F.T f x ∧ F.T f x ≤ 1 := by
  constructor
  · apply F.le_T; intro j
    exact Finset.sum_nonneg fun y _ => mul_nonneg (F.Ppos _ _).le (h0 _)
  · have := F.T_mono h1 x
    have hc : F.T (fun _ => (1:ℝ)) x = 1 := by
      obtain ⟨j, hj⟩ := F.T_attained (fun _ => (1:ℝ)) x
      rw [hj, F.expect_const]
    linarith

theorem T_zero_left {f : ℝ → ℝ} {c : ℝ} (hf : ∀ x, x < c → f x = 0)
    (h0 : ∀ x, 0 ≤ f x) (x : ℝ) (hx : x < c - F.M) : F.T f x = 0 := by
  apply le_antisymm _ (F.le_T fun j => Finset.sum_nonneg fun y _ =>
    mul_nonneg (F.Ppos _ _).le (h0 _))
  refine (F.T_le f x ⟨0, F.hA⟩).trans (le_of_eq ?_)
  apply Finset.sum_eq_zero; intro y _
  rw [hf, mul_zero]
  have := (abs_le.mp (F.abs_X_le ⟨0, F.hA⟩ y)).1
  linarith

theorem T_one_right {f : ℝ → ℝ} {c : ℝ} (hf : ∀ x, c ≤ x → f x = 1)
    (h1 : ∀ x, f x ≤ 1) (x : ℝ) (hx : c + F.M ≤ x) : F.T f x = 1 := by
  apply le_antisymm
  · have := F.T_mono h1 x
    obtain ⟨j, hj⟩ := F.T_attained (fun _ => (1:ℝ)) x
    rw [hj, F.expect_const] at this; exact this
  · apply F.le_T; intro j
    rw [show (1:ℝ) = ∑ y, F.P j y * 1 by simp [F.Psum]]
    apply le_of_eq; apply Finset.sum_congr rfl; intro y _
    rw [hf]
    have := (abs_le.mp (F.abs_X_le j y)).2
    linarith

theorem T_rightCont {f : ℝ → ℝ} (hf : ∀ x, ContinuousWithinAt f (Set.Ici x) x) (x : ℝ) :
    ContinuousWithinAt (F.T f) (Set.Ici x) x := by
  have he : ∀ j, ContinuousWithinAt (F.expect j f) (Set.Ici x) x := by
    intro j
    unfold expect
    apply tendsto_finsetSum
    intro y _
    apply ContinuousWithinAt.mul continuousWithinAt_const
    have hc : ContinuousWithinAt (fun z => z - F.X j y) (Set.Ici x) x :=
      (continuous_id.sub continuous_const).continuousWithinAt
    refine ContinuousWithinAt.comp (f := fun z => z - F.X j y) (hf (x - F.X j y)) hc ?_
    intro z hz; simp only [Set.mem_Ici] at hz ⊢; linarith
  unfold T
  exact ContinuousWithinAt.finset_inf'_apply F.univ_nonempty (fun j _ => he j)

/-- `G n` is a CDF: monotone, right-continuous, `[0,1]`-valued, `0` below
`-nM` and `1` from `nM` on. -/
theorem G_cdf : ∀ n : ℕ,
    Monotone (F.G n) ∧ (∀ x, ContinuousWithinAt (F.G n) (Set.Ici x) x) ∧
    (∀ x, 0 ≤ F.G n x ∧ F.G n x ≤ 1) ∧
    (∀ x, x < -(n * F.M) → F.G n x = 0) ∧ (∀ x, n * F.M ≤ x → F.G n x = 1)
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y h
      simp only [G]
      by_cases hx : 0 ≤ x
      · rw [if_pos hx, if_pos (le_trans hx h)]
      · rw [if_neg hx]; split_ifs <;> norm_num
    · intro x
      by_cases hx : 0 ≤ x
      · apply (continuousWithinAt_const (b := (1:ℝ))).congr
        · intro y hy; simp only [G, if_pos (le_trans hx (Set.mem_Ici.mp hy))]
        · simp [G, hx]
      · apply (continuousAt_const (y := (0:ℝ))).continuousWithinAt.congr_of_eventuallyEq
        · filter_upwards [(eventually_lt_nhds (not_le.mp hx)).filter_mono nhdsWithin_le_nhds]
            with y hy
          simp [G, not_le.mpr hy]
        · simp [G, hx]
    · intro x; simp only [G]; split_ifs <;> norm_num
    · intro x hx; simp only [G]; rw [if_neg]; simp at hx; linarith
    · intro x hx; simp only [G]; rw [if_pos]; simpa using hx
  | n + 1 => by
    obtain ⟨hm, hr, hb, hl, hu⟩ := G_cdf n
    refine ⟨F.T_monotone hm, F.T_rightCont hr, F.T_bounds (fun x => (hb x).1) (fun x => (hb x).2),
      ?_, ?_⟩
    · intro x hx
      exact F.T_zero_left hl (fun x => (hb x).1) x (by push_cast at hx; linarith)
    · intro x hx
      exact F.T_one_right hu (fun x => (hb x).2) x (by push_cast at hx; linarith)

#print axioms G_envelope
#print axioms T_contraction
#print axioms G_cdf

end IncFamily
end CausalSpectrum.Sqrt
