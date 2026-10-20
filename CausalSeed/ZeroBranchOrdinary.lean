/-
Ordinary sources of a tree with zero branches.

An ordinary source has, for every horizon and policy, a readout of a compatible transcript with
the exact transcript law, and no consistency between readouts. A measure space carries an
ordinary source for `T` iff it carries one for `T⁺`, with the same space and measure; the
countable version keeps the weights.
-/
import CausalSeed.ZeroBranchLeaves
import CausalSeed.ZeroBranchTransfer

noncomputable section
open Classical Finset MeasureTheory
open scoped ENNReal

namespace CausalSpectrum.ZeroBranch
open Zero Zero.Shape Completion

namespace NNTree
variable (T : NNTree)

/-- Transcripts of `T_n` compatible with a policy. -/
abbrev Tr (n : ℕ) (π : Pol (T.shapeN n [])) := {ℓ : Lf (T.shapeN n []) // compat ℓ π}

/-- An ordinary source for `T` on a measure space. -/
structure OrdSrc (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  read : ∀ n (π : Pol (T.shapeN n [])), Ω → T.Tr n π
  measurable_fiber : ∀ n π ℓ, MeasurableSet (read n π ⁻¹' {ℓ})
  exact_fiber : ∀ n π ℓ, μ (read n π ⁻¹' {ℓ}) = ENNReal.ofReal (mass (T.kfN n []) ℓ.val)

variable {T}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem mass_eq_zero_of_not_lift {n : ℕ} {π : Pol (T.shapeN n [])} (ℓ : T.Tr n π)
    (π' : Policy (trunc T.plus n [])) (hπ : π = T.extendP n [] π')
    (h : ¬ ∃ ℓp : Transcript T.plus n π', T.liftL n [] ℓp.1 = ℓ.1) :
    mass (T.kfN n []) ℓ.1 = 0 := by
  by_contra hm
  obtain ⟨ℓp, hc, hl⟩ := T.surj_extendP n [] ℓ.1 π' (hπ ▸ ℓ.2) hm
  exact h ⟨⟨ℓp, hc⟩, hl⟩

/-- Reduced ordinary source from an ordinary source of `T`. -/
def OrdSrc.red (V : T.OrdSrc Ω μ) : OrdinarySource T.plus Ω μ where
  read n π' ω :=
    if h : ∃ ℓp : Transcript T.plus n π', T.liftL n [] ℓp.1 = (V.read n (T.extendP n [] π') ω).1
    then h.choose else ⟨run (zeroStrategy _) π', run_compatible_policy _ _⟩
  measurable_fiber n π' ℓp := by
    set π := T.extendP n [] π'
    set dflt : Transcript T.plus n π' := ⟨run (zeroStrategy _) π', run_compatible_policy _ _⟩
    set Bad := ⋃ ℓ : T.Tr n π, ⋃ (_ : ¬ ∃ ℓq : Transcript T.plus n π', T.liftL n [] ℓq.1 = ℓ.1),
      V.read n π ⁻¹' {ℓ}
    have hBad : MeasurableSet Bad :=
      MeasurableSet.iUnion fun ℓ => MeasurableSet.iUnion fun _ => V.measurable_fiber n π ℓ
    set S1 := V.read n π ⁻¹' {⟨T.liftL n [] ℓp.1, T.compat_liftL_extendP n [] _ _ ℓp.2⟩}
    have hfib : (fun ω => if h : ∃ ℓq : Transcript T.plus n π',
        T.liftL n [] ℓq.1 = (V.read n π ω).1 then h.choose else dflt) ⁻¹' {ℓp} =
        S1 ∪ (if ℓp = dflt then Bad else ∅) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, S1]
      by_cases h : ∃ ℓq : Transcript T.plus n π', T.liftL n [] ℓq.1 = (V.read n π ω).1
      · rw [dif_pos h]
        have hnb : ω ∉ Bad := by
          simp only [Bad, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, not_exists]
          intro ℓ hℓ e; subst e; obtain ⟨q, hq⟩ := h; exact hℓ q hq
        constructor
        · intro e; left
          apply Subtype.ext
          rw [← h.choose_spec, e]
        · rintro (e | e)
          · apply Subtype.ext
            apply T.liftL_injective n []
            rw [h.choose_spec, e]
          · split_ifs at e
            · exact absurd e hnb
            · exact absurd e (Set.notMem_empty ω)
      · rw [dite_cond_eq_false (eq_false h)]
        have hb : ω ∈ Bad := by
          simp only [Bad, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨_, h, rfl⟩
        have hn1 : ¬ V.read n π ω = ⟨T.liftL n [] ℓp.1, T.compat_liftL_extendP n [] _ _ ℓp.2⟩ :=
          fun e => h ⟨ℓp, by rw [e]⟩
        constructor
        · intro e; right; rw [if_pos e.symm]; exact hb
        · rintro (e | e)
          · exact absurd e hn1
          · split_ifs at e with hd
            · exact hd.symm
            · exact absurd e (Set.notMem_empty ω)
    rw [hfib]
    exact (V.measurable_fiber _ _ _).union (by split_ifs; exacts [hBad, MeasurableSet.empty])
  exact_fiber n π' ℓp := by
    set π := T.extendP n [] π'
    set dflt : Transcript T.plus n π' := ⟨run (zeroStrategy _) π', run_compatible_policy _ _⟩
    set Bad := ⋃ ℓ : T.Tr n π, ⋃ (_ : ¬ ∃ ℓq : Transcript T.plus n π', T.liftL n [] ℓq.1 = ℓ.1),
      V.read n π ⁻¹' {ℓ}
    have hBad : μ Bad = 0 :=
      measure_iUnion_null fun ℓ => measure_iUnion_null fun hℓ => by
        refine (V.exact_fiber n π ℓ).trans ?_
        rw [T.mass_eq_zero_of_not_lift ℓ π' rfl hℓ, ENNReal.ofReal_zero]
    set S1 := V.read n π ⁻¹' {⟨T.liftL n [] ℓp.1, T.compat_liftL_extendP n [] _ _ ℓp.2⟩}
    set F := (fun ω => if h : ∃ ℓq : Transcript T.plus n π',
        T.liftL n [] ℓq.1 = (V.read n π ω).1 then h.choose else dflt) ⁻¹' {ℓp}
    have h1 : S1 ⊆ F := by
      intro ω hω
      simp only [S1, Set.mem_preimage, Set.mem_singleton_iff] at hω
      have h : ∃ ℓq : Transcript T.plus n π', T.liftL n [] ℓq.1 = (V.read n π ω).1 :=
        ⟨ℓp, by rw [hω]⟩
      show (if h : _ then _ else _) = ℓp
      rw [dif_pos h]
      apply Subtype.ext
      apply T.liftL_injective n []
      rw [h.choose_spec, hω]
    have h2 : F ⊆ S1 ∪ Bad := by
      intro ω hω
      simp only [F, Set.mem_preimage, Set.mem_singleton_iff] at hω
      by_cases h : ∃ ℓq : Transcript T.plus n π', T.liftL n [] ℓq.1 = (V.read n π ω).1
      · rw [dif_pos h] at hω
        left
        simp only [S1, Set.mem_preimage, Set.mem_singleton_iff]
        apply Subtype.ext
        rw [← h.choose_spec, hω]
      · right
        simp only [Bad, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨_, h, rfl⟩
    have hF : μ F = μ S1 := le_antisymm
      ((measure_mono h2).trans ((measure_union_le _ _).trans (by rw [hBad, add_zero])))
      (measure_mono h1)
    show μ F = _
    rw [hF]
    exact (V.exact_fiber n π _).trans (congrArg ENNReal.ofReal (T.mass_liftL n [] ℓp.1))

/-- Ordinary source of `T` from one of `T⁺`. -/
def ordSrcOfPlus (U : OrdinarySource T.plus Ω μ) : T.OrdSrc Ω μ where
  read n π ω := ⟨T.liftL n [] (U.read n (T.restrictP n [] π) ω).1,
    T.compat_liftL_restrictP n [] _ _ (U.read n (T.restrictP n [] π) ω).2⟩
  measurable_fiber n π ℓ := by
    by_cases h : ∃ ℓp : Transcript T.plus n (T.restrictP n [] π), T.liftL n [] ℓp.1 = ℓ.1
    · obtain ⟨ℓp, hl⟩ := h
      have : (fun ω => (⟨T.liftL n [] (U.read n (T.restrictP n [] π) ω).1,
          T.compat_liftL_restrictP n [] _ _ (U.read n (T.restrictP n [] π) ω).2⟩ : T.Tr n π)) ⁻¹'
          {ℓ} = U.read n (T.restrictP n [] π) ⁻¹' {ℓp} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro e; apply Subtype.ext; apply T.liftL_injective n []
          rw [hl]; exact congrArg Subtype.val e
        · intro e; apply Subtype.ext; simp only [e, hl]
      rw [this]; exact U.measurable_fiber _ _ _
    · have : (fun ω => (⟨T.liftL n [] (U.read n (T.restrictP n [] π) ω).1,
          T.compat_liftL_restrictP n [] _ _ (U.read n (T.restrictP n [] π) ω).2⟩ : T.Tr n π)) ⁻¹'
          {ℓ} = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro e; exact h ⟨_, congrArg Subtype.val e⟩
      rw [this]; exact MeasurableSet.empty
  exact_fiber n π ℓ := by
    by_cases h : ∃ ℓp : Transcript T.plus n (T.restrictP n [] π), T.liftL n [] ℓp.1 = ℓ.1
    · obtain ⟨ℓp, hl⟩ := h
      have : (fun ω => (⟨T.liftL n [] (U.read n (T.restrictP n [] π) ω).1,
          T.compat_liftL_restrictP n [] _ _ (U.read n (T.restrictP n [] π) ω).2⟩ : T.Tr n π)) ⁻¹'
          {ℓ} = U.read n (T.restrictP n [] π) ⁻¹' {ℓp} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro e; apply Subtype.ext; apply T.liftL_injective n []
          rw [hl]; exact congrArg Subtype.val e
        · intro e; apply Subtype.ext; simp only [e, hl]
      rw [this, U.exact_fiber]
      exact congrArg ENNReal.ofReal ((T.mass_liftL n [] ℓp.1).symm.trans (congrArg _ hl))
    · have : (fun ω => (⟨T.liftL n [] (U.read n (T.restrictP n [] π) ω).1,
          T.compat_liftL_restrictP n [] _ _ (U.read n (T.restrictP n [] π) ω).2⟩ : T.Tr n π)) ⁻¹'
          {ℓ} = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro e; exact h ⟨_, congrArg Subtype.val e⟩
      have hm : mass (T.kfN n []) ℓ.1 = 0 := by
        by_contra hm
        obtain ⟨ℓp, hc, hl⟩ := T.surj_restrictP n [] ℓ.1 π ℓ.2 hm
        exact h ⟨⟨ℓp, hc⟩, hl⟩
      rw [this, measure_empty, hm, ENNReal.ofReal_zero]

variable (T)

/-- **Theorem (seed space, ordinary sources).** A measure space carries an ordinary source for
`T` iff it carries one for `T⁺`; the space and the measure are unchanged. -/
theorem ordinary_iff : Nonempty (T.OrdSrc Ω μ) ↔ Nonempty (OrdinarySource T.plus Ω μ) :=
  ⟨fun ⟨V⟩ => ⟨V.red⟩, fun ⟨U⟩ => ⟨ordSrcOfPlus U⟩⟩

/-- **Corollary 3 (ordinary converse).** The atomic mass of any ordinary source of `T` is at most
`q`. -/
theorem ordinary_atomic_le [MeasurableSingletonClass Ω] [IsProbabilityMeasure μ]
    (V : T.OrdSrc Ω μ) : atomicMass μ ≤ ENNReal.ofReal T.q := by
  rw [q_eq]; exact ordinary_atomic_upper μ V.red

/-- **Corollary 3 (ordinary attainment).** Some ordinary source of `T` on a probability space has
atomic mass exactly `q`, so the maximal ordinary atomic capacity of `T` is `q`. -/
theorem ordinary_atomic_attained :
    ∃ μ : Measure (IStrategy T.plus), IsProbabilityMeasure μ ∧ Nonempty (T.OrdSrc _ μ) ∧
      atomicMass μ = ENNReal.ofReal T.q := by
  obtain ⟨μp, hprob, hcyl, hatom⟩ := causal_atomic_capacity_attained T.plus
  exact ⟨μp, hprob, ⟨ordSrcOfPlus (sourceOfCylinders T.plus μp hcyl)⟩, by rw [hatom, q_eq]⟩

/-! ### Countable ordinary sources -/

open RenyiInf

/-- A countable ordinary source for `T`: a probability vector and, for every horizon and index,
a readout of a compatible transcript for each policy, with exact transcript laws. -/
structure OrdSrcC where
  w : ℕ → ℝ
  law : IsLaw w
  read : (n : ℕ) → ℕ → ∀ π : Pol (T.shapeN n []), T.Tr n π
  marginal : ∀ n (π : Pol (T.shapeN n [])) (ℓ : Lf (T.shapeN n [])), compat ℓ π →
    ∑' i, (if (read n i π).1 = ℓ then w i else 0) = mass (T.kfN n []) ℓ

variable {T}

theorem mass_liftL0 (n : ℕ) (ℓ : Leaf (trunc T.plus n [])) :
    mass (T.kfN n []) (T.liftL n [] ℓ) = leafMass ℓ := T.mass_liftL n [] ℓ

theorem OrdSrcC.w_le (V : T.OrdSrcC) (n i : ℕ) (π : Pol (T.shapeN n [])) :
    V.w i ≤ mass (T.kfN n []) (V.read n i π).1 := by
  rw [← V.marginal n π _ (V.read n i π).2]
  have hs : Summable fun j => if (V.read n j π).1 = (V.read n i π).1 then V.w j else 0 :=
    Summable.of_nonneg_of_le (fun j => by split_ifs; exacts [V.law.nonneg j, le_rfl])
      (fun j => by split_ifs; exacts [le_rfl, V.law.nonneg j]) V.law.sum.summable
  have := hs.le_tsum i (fun j _ => by split_ifs; exacts [V.law.nonneg j, le_rfl])
  simpa using this

/-- Countable ordinary source of `T⁺` from one of `T`, with the same weights. -/
def OrdSrcC.red (V : T.OrdSrcC) : OrdSource T.plus where
  w := V.w
  law := V.law
  read n i π' :=
    if h : ∃ ℓp : Transcript T.plus n π',
        T.liftL n [] ℓp.1 = (V.read n i (T.extendP n [] π')).1
    then h.choose else ⟨run (zeroStrategy _) π', run_compatible_policy _ _⟩
  marginal n π' ℓp hc := by
    rw [← T.mass_liftL0 n ℓp, ← V.marginal n (T.extendP n [] π') _
      (T.compat_liftL_extendP n [] _ _ hc)]
    congr 1; funext i
    by_cases hw : V.w i = 0
    · simp [hw]
    have hm : mass (T.kfN n []) (V.read n i (T.extendP n [] π')).1 ≠ 0 := by
      intro h0; exact hw (le_antisymm (h0 ▸ V.w_le n i _) (V.law.nonneg i))
    obtain ⟨ℓq, hcq, hlq⟩ := T.surj_extendP n [] _ π' (V.read n i _).2 hm
    have h : ∃ ℓp : Transcript T.plus n π',
        T.liftL n [] ℓp.1 = (V.read n i (T.extendP n [] π')).1 := ⟨⟨ℓq, hcq⟩, hlq⟩
    rw [dif_pos h]
    have key : h.choose.1 = ℓp ↔ (V.read n i (T.extendP n [] π')).1 = T.liftL n [] ℓp := by
      have hs := h.choose_spec
      constructor
      · intro e; rw [← hs, e]
      · intro e'; exact T.liftL_injective n [] (hs.trans e')
    by_cases e : h.choose.1 = ℓp
    · exact (if_pos e).trans (if_pos (key.1 e)).symm
    · exact (if_neg e).trans (if_neg (fun e' => e (key.2 e'))).symm

/-- Countable ordinary source of `T` from one of `T⁺`, with the same weights. -/
def ordSrcCOfPlus (U : OrdSource T.plus) : T.OrdSrcC where
  w := U.w
  law := U.law
  read n i π := ⟨T.liftL n [] (U.read n i (T.restrictP n [] π)).1,
    T.compat_liftL_restrictP n [] _ _ (U.read n i (T.restrictP n [] π)).2⟩
  marginal n π ℓ hc := by
    by_cases hm : mass (T.kfN n []) ℓ = 0
    · rw [hm]
      refine (tsum_congr fun i => ?_).trans tsum_zero
      rw [if_neg]
      intro e
      have := T.mass_liftL0 n (U.read n i (T.restrictP n [] π)).1
      dsimp only at e
      rw [e, hm] at this
      exact (leafMass_pos _).ne this
    · obtain ⟨ℓp, hcp, hl⟩ := T.surj_restrictP n [] ℓ π hc hm
      have := U.marginal n (T.restrictP n [] π) ℓp hcp
      rw [← hl, T.mass_liftL0, ← this]
      congr 1; funext i
      dsimp only
      by_cases e : (U.read n i (T.restrictP n [] π)).1 = ℓp
      · exact (if_pos (by rw [e])).trans (if_pos e).symm
      · exact (if_neg (fun e' => e (T.liftL_injective n [] e'))).trans (if_neg e).symm

variable (T)

/-- Ordinary Rényi optimum of `T`, over countable ordinary sources of `T`. -/
def OalphaT (α : ℝ) : ℝ≥0∞ := ⨅ V : T.OrdSrcC, H α V.w

/-- Ordinary min-entropy optimum of `T`. -/
def OinfT : ℝ≥0∞ := ⨅ V : T.OrdSrcC, Hinf V.w

theorem ordSrcC_iff : Nonempty T.OrdSrcC ↔ Nonempty (OrdSource T.plus) :=
  ⟨fun ⟨V⟩ => ⟨V.red⟩, fun ⟨U⟩ => ⟨ordSrcCOfPlus U⟩⟩

theorem OalphaT_eq (α : ℝ) : T.OalphaT α = Oα T.plus α :=
  le_antisymm (le_iInf fun U => iInf_le_of_le (ordSrcCOfPlus U) le_rfl)
    (le_iInf fun V => iInf_le_of_le V.red le_rfl)

theorem OinfT_eq : T.OinfT = Oinf T.plus :=
  le_antisymm (le_iInf fun U => iInf_le_of_le (ordSrcCOfPlus U) le_rfl)
    (le_iInf fun V => iInf_le_of_le V.red le_rfl)

/-- **Corollary 4 (simultaneous Rényi seed), stated on `T`.** If `T` has a countable ordinary
source, one exact countable seed `S` on `T` satisfies, for every `α > 0`,
`R_α(Z) ≤ O_α(T) ≤ C_α(T) ≤ H_α(S) ≤ R_α(Z) + d_α`, and its min-entropy attains both optima. -/
theorem one_seed_all_orders_T (hV : Nonempty T.OrdSrcC) :
    ∃ S : T.Seed, S.Exact ∧
      (∀ α : ℝ, 0 < α →
        RZmeas T.plus α ≤ T.OalphaT α ∧ T.OalphaT α ≤ T.Calpha α ∧ T.Calpha α ≤ H α S.weight ∧
          H α S.weight ≤ RZmeas T.plus α + ENNReal.ofReal (dA α)) ∧
      Hinf S.weight = T.Cmin ∧ T.Cmin = T.OinfT := by
  obtain ⟨S, hS, hall, h1, h2⟩ := T.one_seed_all_orders ((T.ordSrcC_iff).1 hV)
  refine ⟨S, hS, fun α hα => ?_, h1, by rw [h2, OinfT_eq]⟩
  rw [OalphaT_eq]; exact hall α hα

end NNTree
end CausalSpectrum.ZeroBranch
