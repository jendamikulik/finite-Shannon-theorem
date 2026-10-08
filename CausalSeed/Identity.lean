/-
Exact penalty. For every coefficient at least `gapSup`,

  causalMin T = inf over couplings Γ of (H(Γ) + κ · Γ(B)).

The two endpoint masses were already in `Penalty.lean`. The intermediate mass
is the residual tree: delete the realizable atoms, prune the zero branches,
and pay `gapSup` on that tree.
-/
import CausalSeed.Transport

noncomputable section
open Classical
namespace CausalSpectrum

noncomputable instance {T : Tree} : DecidableEq (Assignment T) :=
  fun a b => Classical.propDecidable (a = b)

theorem mass_eq_zero_of_bad {T : Tree} {Γ : Coupling T} (h : Γ.badMass = 0)
    {α : Assignment T} (hr : ¬ realizable α) : Γ.mass α = 0 := by
  have hzero : ∑ β, (if realizable β then (0 : ℝ) else Γ.mass β) = 0 := by
    simpa [Coupling.badMass] using h
  have hterm : (if realizable α then (0 : ℝ) else Γ.mass α) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun β _ => by
      by_cases hb : realizable β
      · simp [hb]
      · simp [hb, Γ.nonneg β])).1 hzero α (Finset.mem_univ α)
  simpa [hr] using hterm

theorem exists_causal_entropy_lt {T : Tree} {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : Coupling T, Γ.badMass = 0 ∧ Γ.entropy < causalMin T + ε := by
  by_contra hnone
  push Not at hnone
  have : causalMin T + ε ≤ causalMin T :=
    le_csInf (causalEntropySet_nonempty T) fun x hx => by
      obtain ⟨Γ, hbad, hx⟩ := hx
      simpa [hx] using hnone Γ hbad
  linarith

theorem entTerm_sum_le {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    entTerm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, entTerm (f i) := by
  induction s using Finset.induction with
  | empty => simp [entTerm]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      linarith [entTerm_add_le (hf a (Finset.mem_insert_self a s))
        (Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem pmfEntropy_push_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (φ : α → β) :
    pmfEntropy (fun b => ∑ a, if φ a = b then μ a else 0) ≤ pmfEntropy μ := by
  unfold pmfEntropy
  have hfiber : ∀ b, entTerm (∑ a, if φ a = b then μ a else 0) ≤
      ∑ a, entTerm (if φ a = b then μ a else 0) := by
    intro b
    refine entTerm_sum_le Finset.univ _ ?_
    intro a _
    by_cases h : φ a = b
    · simp [h, h0 a]
    · simp [h]
  refine le_trans (Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hfiber b) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  have hterm : ∀ b, entTerm (if φ a = b then μ a else 0) =
      if φ a = b then entTerm (μ a) else 0 := by
    intro b
    by_cases h : φ a = b
    · simp [h]
    · simp [h, entTerm]
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_ite_eq]
  simp

theorem pmfEntropy_mix_le {α : Type} [Fintype α] (ν lam : α → ℝ) (η : ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hlam : ∀ a, 0 ≤ lam a)
    (hν1 : ∑ a, ν a = 1) (hlam1 : ∑ a, lam a = 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    pmfEntropy (fun a => (1 - η) * ν a + η * lam a) ≤
      entTerm (1 - η) + entTerm η + (1 - η) * pmfEntropy ν + η * pmfEntropy lam := by
  unfold pmfEntropy
  have hpoint : ∀ a, entTerm ((1 - η) * ν a + η * lam a) ≤
      ν a * entTerm (1 - η) + (1 - η) * entTerm (ν a) +
        (lam a * entTerm η + η * entTerm (lam a)) := by
    intro a
    have hsplit := entTerm_add_le
      (mul_nonneg (sub_nonneg.mpr hη1) (hν a)) (mul_nonneg hη0 (hlam a))
    have hmulν := entTerm_mul (sub_nonneg.mpr hη1) (hν a)
    have hmulLam := entTerm_mul hη0 (hlam a)
    have hν' : entTerm ((1 - η) * ν a) = ν a * entTerm (1 - η) + (1 - η) * entTerm (ν a) := by
      simpa [mul_comm] using hmulν
    have hlam' : entTerm (η * lam a) = lam a * entTerm η + η * entTerm (lam a) := by
      simpa [mul_comm] using hmulLam
    linarith
  refine le_trans (Finset.sum_le_sum fun a _ => hpoint a) ?_
  simp only [Finset.sum_add_distrib]
  have hA : ∑ a, ν a * entTerm (1 - η) = entTerm (1 - η) := by
    rw [← Finset.sum_mul, hν1, one_mul]
  have hB : ∑ a, (1 - η) * entTerm (ν a) = (1 - η) * ∑ a, entTerm (ν a) := by
    rw [Finset.mul_sum]
  have hC : ∑ a, lam a * entTerm η = entTerm η := by
    rw [← Finset.sum_mul, hlam1, one_mul]
  have hD : ∑ a, η * entTerm (lam a) = η * ∑ a, entTerm (lam a) := by
    rw [Finset.mul_sum]
  rw [hA, hB, hC, hD]
  apply le_of_eq
  ring

theorem goodMarginal {T : Tree} (Γ : Coupling T) (π : Policy T) (ℓ : Leaf T)
    (hc : CompatiblePolicy ℓ π) :
    ∑ α, (if realizable α ∧ (α π).1 = ℓ then Γ.mass α else 0) =
      leafMass ℓ - leafValue (residualField Γ) ℓ := by
  classical
  have hbad := residual_eq_bad Γ π ℓ hc
  have hm := Γ.marginal π ℓ hc
  have hsplit : ∀ α,
      (if (α π).1 = ℓ then Γ.mass α else 0) =
        (if realizable α ∧ (α π).1 = ℓ then Γ.mass α else 0) +
          (if ¬ realizable α ∧ (α π).1 = ℓ then Γ.mass α else 0) := by
    intro α
    by_cases hℓ : (α π).1 = ℓ
    · by_cases hr : realizable α
      · simp [hℓ, hr]
      · simp [hℓ, hr]
    · simp [hℓ]
  have hsum := Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) => hsplit α
  rw [Finset.sum_add_distrib] at hsum
  linarith

/-- `causalMin T ≤ H(Γ) + gapSup · Γ(B)`. -/
theorem causalMin_le_penalised {T : Tree} (Γ : Coupling T) :
    causalMin T ≤ penalised gapSup Γ := by
  classical
  by_cases h0 : Γ.badMass = 0
  · exact causalMin_le_penalised_of_zero h0
  by_cases h1 : Γ.badMass = 1
  · exact causalMin_le_penalised_of_one Γ h1
  have hη : 0 < Γ.badMass := lt_of_le_of_ne (badMass_nonneg Γ) (Ne.symm h0)
  have hη1 : Γ.badMass < 1 := lt_of_le_of_ne (badMass_le_one Γ) h1
  let η : ℝ := Γ.badMass
  let r : Field T := residualField Γ
  have hf : Field.IsFlow r := residual_isFlow Γ
  have hn : Field.Nonneg r := residual_nonneg Γ
  have hroot : Field.root r = η := residual_root Γ
  have hr : 0 < Field.root r := by simpa [hroot] using hη
  let S : Tree := prunedTree r hf hn hr
  let μ : Assignment T → ℝ := fun α => if ¬ realizable α then Γ.mass α / η else 0
  let ν : Assignment T → ℝ := fun α => if realizable α then Γ.mass α / (1 - η) else 0
  have hμ0 : ∀ α, 0 ≤ μ α := by
    intro α
    by_cases hrα : realizable α
    · simp [μ, hrα]
    · simpa [μ, hrα] using div_nonneg (Γ.nonneg α) hη.le
  have hν0 : ∀ α, 0 ≤ ν α := by
    intro α
    by_cases hrα : realizable α
    · simpa [ν, hrα] using div_nonneg (Γ.nonneg α) (sub_nonneg.mpr hη1.le)
    · simp [ν, hrα]
  have hμsum : ∑ α, μ α = 1 := by
    have hrew : ∀ α, μ α = (if ¬ realizable α then Γ.mass α else 0) / η := by
      intro α
      by_cases hrα : realizable α <;> simp [μ, hrα, zero_div]
    simp_rw [hrew, ← Finset.sum_div]
    have hbad : ∑ α, (if ¬ realizable α then Γ.mass α else (0 : ℝ)) = η := by
      have hsame : ∑ α, (if ¬ realizable α then Γ.mass α else (0 : ℝ)) =
          ∑ α, (if realizable α then 0 else Γ.mass α) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        by_cases hrα : realizable α <;> simp [hrα]
      rw [hsame]
      simp [Coupling.badMass, η]
    rw [hbad]
    exact div_self (ne_of_gt hη)
  have hνsum : ∑ α, ν α = 1 := by
    have hrew : ∀ α, ν α = (if realizable α then Γ.mass α else 0) / (1 - η) := by
      intro α
      by_cases hrα : realizable α <;> simp [ν, hrα, zero_div]
    simp_rw [hrew, ← Finset.sum_div]
    rw [goodMass_eq Γ]
    exact div_self (ne_of_gt (sub_pos.mpr hη1))
  have hsplit := binaryEntropy_split Γ.mass (fun α => ¬ realizable α) Γ.nonneg Γ.total η
    (by
      have hsame : ∑ α, (if ¬ realizable α then Γ.mass α else (0 : ℝ)) =
          ∑ α, (if realizable α then 0 else Γ.mass α) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        by_cases hrα : realizable α <;> simp [hrα]
      rw [hsame]
      simp [Coupling.badMass, η])
    hη hη1
  have hμEnt : pmfEntropy μ =
      pmfEntropy (fun α => if ¬ realizable α then Γ.mass α / η else 0) := rfl
  have hνEnt : pmfEntropy ν =
      pmfEntropy (fun α => if realizable α then Γ.mass α / (1 - η) else 0) := by
    unfold pmfEntropy
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases hrα : realizable α
    · simp [ν, hrα]
    · simp [ν, hrα, entTerm]
  -- Conditional law on the inconsistent atoms, pushed onto the pruned tree.
  let φ : Assignment T → Assignment S := fun α πS =>
    let πT := polOut r hf hn hr πS
    let ℓ := (α πT).1
    if hp : 0 < leafValue r ℓ then
      ⟨leafIn r hf hn hr ℓ hp, leafIn_polOut r hf hn hr ℓ hp πS (α πT).2⟩
    else
      realizes (defaultStrategy S) πS
  have hμpos : ∀ {α : Assignment T}, 0 < μ α → ¬ realizable α ∧ 0 < Γ.mass α := by
    intro α hμα
    by_cases hrα : realizable α
    · simp [μ, hrα] at hμα
    · refine ⟨hrα, ?_⟩
      have hdiv : 0 < Γ.mass α / η := by simpa [μ, hrα] using hμα
      have hmul : 0 < Γ.mass α / η * η := mul_pos hdiv hη
      rwa [div_mul_cancel₀ _ (ne_of_gt hη)] at hmul
  have hleafpos : ∀ {α : Assignment T} {πS : Policy S}, 0 < μ α →
      0 < leafValue r ((α (polOut r hf hn hr πS)).1) := by
    intro α πS hμα
    obtain ⟨hrα, hmass⟩ := hμpos hμα
    let πT := polOut r hf hn hr πS
    have hc := (α πT).2
    have hbad := residual_eq_bad Γ πT (α πT).1 hc
    have hle : Γ.mass α ≤
        ∑ β, if ¬ realizable β ∧ (β πT).1 = (α πT).1 then Γ.mass β else 0 := by
      refine le_trans ?_ (Finset.single_le_sum (fun β _ => by
        by_cases hb : ¬ realizable β ∧ (β πT).1 = (α πT).1
        · simp [hb, Γ.nonneg β]
        · simp [hb]) (Finset.mem_univ α))
      simp [hrα]
    linarith
  have hφ_pos : ∀ {α : Assignment T} {πS : Policy S} (hμα : 0 < μ α),
      (φ α πS).1 = leafIn r hf hn hr ((α (polOut r hf hn hr πS)).1) (hleafpos hμα) ∧
      CompatiblePolicy (φ α πS).1 πS := by
    intro α πS hμα
    have hp := hleafpos (πS := πS) hμα
    have hdit : φ α πS =
        ⟨leafIn r hf hn hr _ hp, leafIn_polOut r hf hn hr _ hp πS (α _).2⟩ := by
      simp [φ, hp]
    constructor
    · rw [hdit]
    · rw [hdit]
      exact leafIn_polOut r hf hn hr _ hp πS (α _).2
  let pushed : Assignment S → ℝ := fun β => ∑ α, if φ α = β then μ α else 0
  have hpush0 : ∀ β, 0 ≤ pushed β := by
    intro β
    apply Finset.sum_nonneg
    intro α _
    by_cases hφ : φ α = β
    · simp [hφ, hμ0 α]
    · simp [hφ]
  have hpushSum : ∑ β, pushed β = 1 := by
    rw [Finset.sum_comm]
    have hone : ∀ α, ∑ β, (if φ α = β then μ α else (0 : ℝ)) = μ α := by
      intro α
      rw [Finset.sum_ite_eq]
      simp
    simp_rw [hone, hμsum]
  have hpushEnt : pmfEntropy pushed ≤ pmfEntropy μ :=
    pmfEntropy_push_le μ hμ0 φ
  have hmarg : ∀ (πS : Policy S) (ℓS : Leaf S), CompatiblePolicy ℓS πS →
      ∑ β, (if (β πS).1 = ℓS then pushed β else (0 : ℝ)) = leafMass ℓS := by
    intro πS ℓS hcS
    have hswap : ∑ β, (if (β πS).1 = ℓS then pushed β else (0 : ℝ)) =
        ∑ α, (if (φ α πS).1 = ℓS then μ α else 0) := by
      have hterm : ∀ β, (if (β πS).1 = ℓS then pushed β else (0 : ℝ)) =
          ∑ α, (if (β πS).1 = ℓS then if φ α = β then μ α else 0 else 0) := by
        intro β
        by_cases hβ : (β πS).1 = ℓS
        · simp [pushed, hβ]
        · simp [hβ, pushed]
      simp_rw [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hcomb : ∀ β, (if (β πS).1 = ℓS then if φ α = β then μ α else 0 else 0) =
          if φ α = β then (if (φ α πS).1 = ℓS then μ α else 0) else 0 := by
        intro β
        by_cases hφ : φ α = β
        · simp [hφ]
        · simp [hφ]
      simp_rw [hcomb, Finset.sum_ite_eq]
      simp
    rw [hswap]
    have hiff : ∀ α, (if (φ α πS).1 = ℓS then μ α else 0) =
        if (α (polOut r hf hn hr πS)).1 = leafOut r hf hn hr ℓS then μ α else 0 := by
      intro α
      by_cases hμα : 0 < μ α
      · have hp := hleafpos (πS := πS) hμα
        have hspec := (hφ_pos (πS := πS) hμα).1
        by_cases hhit : (α (polOut r hf hn hr πS)).1 = leafOut r hf hn hr ℓS
        · have hpre : (φ α πS).1 = ℓS := by
            rw [hspec]
            have hclose (ℓ0 : Leaf T) (heq : ℓ0 = leafOut r hf hn hr ℓS)
                (hpos : 0 < leafValue r ℓ0) :
                leafIn r hf hn hr ℓ0 hpos = ℓS := by
              subst heq
              have hleafEq : leafIn r hf hn hr (leafOut r hf hn hr ℓS) hpos =
                  leafIn r hf hn hr (leafOut r hf hn hr ℓS) (leafOut_pos r hf hn hr ℓS) := by
                have hpEq : hpos = leafOut_pos r hf hn hr ℓS := Subsingleton.elim _ _
                subst hpEq
                rfl
              rw [hleafEq]
              exact leafIn_leafOut r hf hn hr ℓS
            exact hclose _ hhit hp
          simp [hhit, hpre]
        · have hpre : (φ α πS).1 ≠ ℓS := by
            intro heq
            apply hhit
            have hspec' := hspec
            rw [heq] at hspec'
            have hleaf := congrArg (leafOut r hf hn hr) hspec'.symm
            rw [leafOut_leafIn] at hleaf
            exact hleaf
          simp [hhit, hpre]
      · have hμ : μ α = 0 := le_antisymm (le_of_not_gt hμα) (hμ0 α)
        simp [hμ]
    simp_rw [hiff]
    have hμbad : ∑ α, (if (α (polOut r hf hn hr πS)).1 = leafOut r hf hn hr ℓS then μ α else 0) =
        (∑ α, if ¬ realizable α ∧ (α (polOut r hf hn hr πS)).1 = leafOut r hf hn hr ℓS
          then Γ.mass α else 0) / η := by
      have hterm : ∀ α,
          (if (α (polOut r hf hn hr πS)).1 = leafOut r hf hn hr ℓS then μ α else (0 : ℝ)) =
            (if ¬ realizable α ∧ (α (polOut r hf hn hr πS)).1 = leafOut r hf hn hr ℓS
              then Γ.mass α else 0) / η := by
        intro α
        by_cases hℓ : (α (polOut r hf hn hr πS)).1 = leafOut r hf hn hr ℓS
        · by_cases hrα : realizable α
          · simp [μ, hℓ, hrα, zero_div]
          · simp [μ, hℓ, hrα]
        · simp [hℓ, zero_div]
      simp_rw [hterm, ← Finset.sum_div]
    have hcompat : CompatiblePolicy (leafOut r hf hn hr ℓS) (polOut r hf hn hr πS) :=
      leafOut_polOut r hf hn hr ℓS πS hcS
    have hleaf := residual_eq_bad Γ (polOut r hf hn hr πS) (leafOut r hf hn hr ℓS) hcompat
    rw [hμbad, ← hleaf]
    have hsc := leafOut_scale r hf hn hr ℓS
    rw [hroot] at hsc
    calc
      leafValue r (leafOut r hf hn hr ℓS) / η = (leafMass ℓS * η) / η := by rw [hsc]
      _ = leafMass ℓS := mul_div_cancel_right₀ (leafMass ℓS) (ne_of_gt hη)
  let Δ : Coupling S :=
    { mass := pushed
      nonneg := hpush0
      total := hpushSum
      marginal := hmarg }
  have hΔent : Δ.entropy ≤ pmfEntropy μ := by
    simpa [Coupling.entropy, Δ] using hpushEnt
  have hgap : causalMin S ≤ ordinaryMin S + gapSup := by
    have := gapOf_le_gapSup S
    unfold gapOf at this
    linarith
  -- A nearly causal replacement on the pruned tree, carried back and mixed.
  have happrox : ∀ {ε : ℝ}, 0 < ε →
      ∃ Γc : Coupling T, Γc.badMass = 0 ∧
        Γc.entropy < Γ.entropy + gapSup * η + ε := by
    intro ε hε
    have hδ : 0 < ε / η := div_pos hε hη
    obtain ⟨Λ, hΛbad, hΛH⟩ := exists_causal_entropy_lt (T := S) hδ
    let embed : Assignment S → Assignment T := fun β =>
      realizes (stratOut r hf hn hr (chosenOf β))
    let lam : Assignment T → ℝ := fun α => ∑ β, if embed β = α then Λ.mass β else 0
    have hlam0 : ∀ α, 0 ≤ lam α := by
      intro α
      apply Finset.sum_nonneg
      intro β _
      by_cases h : embed β = α
      · simp [h, Λ.nonneg β]
      · simp [h]
    have hlamsum : ∑ α, lam α = 1 := by
      rw [Finset.sum_comm]
      have hone : ∀ β, ∑ α, (if embed β = α then Λ.mass β else (0 : ℝ)) = Λ.mass β := by
        intro β
        rw [Finset.sum_ite_eq]
        simp
      simp_rw [hone, Λ.total]
    have hlamEnt : pmfEntropy lam ≤ Λ.entropy := by
      simpa [Coupling.entropy] using pmfEntropy_push_le Λ.mass Λ.nonneg embed
    have hΛbound : Λ.entropy < pmfEntropy μ + gapSup + ε / η := by
      linarith [hΛH, hgap, ordinaryMin_le_entropy Δ, hΔent]
    have hlambound : pmfEntropy lam < pmfEntropy μ + gapSup + ε / η :=
      lt_of_le_of_lt hlamEnt hΛbound
    let mix : Assignment T → ℝ := fun α => (1 - η) * ν α + η * lam α
    have hmix0 : ∀ α, 0 ≤ mix α := by
      intro α
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hη1.le) (hν0 α)) (mul_nonneg hη.le (hlam0 α))
    have hmixSum : ∑ α, mix α = 1 := by
      simp only [mix, Finset.sum_add_distrib, ← Finset.mul_sum, hνsum, hlamsum]
      ring
    have hembed_real : ∀ β, realizable (embed β) := fun β =>
      ⟨stratOut r hf hn hr (chosenOf β), rfl⟩
    have hembed_leaf : ∀ {β : Assignment S} {π : Policy T}, realizable β →
        (embed β π).1 = leafOut r hf hn hr ((β (polIn r hf hn hr π)).1) := by
      intro β π hβ
      have hrun : run (chosenOf β) (polIn r hf hn hr π) = (β (polIn r hf hn hr π)).1 := by
        have hpair := congrArg Subtype.val (congrFun (chosenOf_realizes hβ) (polIn r hf hn hr π))
        simpa [realizes] using hpair
      have hcomm := run_stratOut r hf hn hr (chosenOf β) π
      calc
        (embed β π).1 = run (stratOut r hf hn hr (chosenOf β)) π := by
          simp [embed, realizes]
        _ = leafOut r hf hn hr (run (chosenOf β) (polIn r hf hn hr π)) := hcomm
        _ = leafOut r hf hn hr ((β (polIn r hf hn hr π)).1) := by rw [hrun]
    have hmixMarg : ∀ (π : Policy T) (ℓ : Leaf T), CompatiblePolicy ℓ π →
        ∑ α, (if (α π).1 = ℓ then mix α else 0) = leafMass ℓ := by
      intro π ℓ hc
      have hsplit : ∑ α, (if (α π).1 = ℓ then mix α else 0) =
          (1 - η) * ∑ α, (if (α π).1 = ℓ then ν α else 0) +
            η * ∑ α, (if (α π).1 = ℓ then lam α else 0) := by
        have hterm : ∀ α, (if (α π).1 = ℓ then mix α else 0) =
            (1 - η) * (if (α π).1 = ℓ then ν α else 0) +
              η * (if (α π).1 = ℓ then lam α else 0) := by
          intro α
          by_cases hℓ : (α π).1 = ℓ
          · simp [mix, hℓ]
          · simp [hℓ]
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hsplit]
      have hνmarg : ∑ α, (if (α π).1 = ℓ then ν α else 0) =
          (leafMass ℓ - leafValue r ℓ) / (1 - η) := by
        have hterm : ∀ α, (if (α π).1 = ℓ then ν α else (0 : ℝ)) =
            (if realizable α ∧ (α π).1 = ℓ then Γ.mass α else 0) / (1 - η) := by
          intro α
          by_cases hℓ : (α π).1 = ℓ
          · by_cases hrα : realizable α
            · simp [ν, hℓ, hrα]
            · simp [ν, hℓ, hrα, zero_div]
          · simp [hℓ, zero_div]
        simp_rw [hterm, ← Finset.sum_div]
        rw [goodMarginal Γ π ℓ hc]
      have hlammarg : ∑ α, (if (α π).1 = ℓ then lam α else 0) = leafValue r ℓ / η := by
        have hswap : ∑ α, (if (α π).1 = ℓ then lam α else 0) =
            ∑ β, (if (embed β π).1 = ℓ then Λ.mass β else 0) := by
          have hterm : ∀ α, (if (α π).1 = ℓ then lam α else (0 : ℝ)) =
              ∑ β, (if (α π).1 = ℓ then if embed β = α then Λ.mass β else 0 else 0) := by
            intro α
            by_cases hℓ : (α π).1 = ℓ
            · simp [lam, hℓ]
            · simp [hℓ]
          simp_rw [hterm]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => ?_
          have hcomb : ∀ α, (if (α π).1 = ℓ then if embed β = α then Λ.mass β else 0 else 0) =
              if α = embed β then (if (embed β π).1 = ℓ then Λ.mass β else 0) else 0 := by
            intro α
            by_cases hα : α = embed β
            · subst hα
              rw [ite_eq_left (rfl : embed β = embed β)]
              rw [ite_eq_left (rfl : embed β = embed β)]
            · have hne : embed β ≠ α := fun h => hα h.symm
              rw [ite_eq_right hα, ite_eq_right hne]
              split_ifs <;> rfl
          simp_rw [hcomb]
          exact Finset.sum_ite_eq_of_mem' Finset.univ (embed β)
            (fun _ => if (embed β π).1 = ℓ then Λ.mass β else 0) (Finset.mem_univ _)
        rw [hswap]
        by_cases hp : 0 < leafValue r ℓ
        · have hcomp : CompatiblePolicy (leafIn r hf hn hr ℓ hp) (polIn r hf hn hr π) :=
            leafIn_polIn r hf hn hr ℓ hp π hc
          have hterm : ∀ β, (if (embed β π).1 = ℓ then Λ.mass β else (0 : ℝ)) =
              if (β (polIn r hf hn hr π)).1 = leafIn r hf hn hr ℓ hp then Λ.mass β else 0 := by
            intro β
            by_cases hβ : realizable β
            · have hleaf := hembed_leaf (π := π) hβ
              by_cases hhit : (β (polIn r hf hn hr π)).1 = leafIn r hf hn hr ℓ hp
              · have heq : (embed β π).1 = ℓ := by
                  rw [hleaf, hhit, leafOut_leafIn]
                simp [heq, hhit]
              · have hne : (embed β π).1 ≠ ℓ := by
                  intro heq
                  apply hhit
                  have hout : leafOut r hf hn hr ((β (polIn r hf hn hr π)).1) = ℓ := by
                    rw [← hleaf]; exact heq
                  have htransport (ℓ1 : Leaf T)
                      (heq1 : leafOut r hf hn hr ((β (polIn r hf hn hr π)).1) = ℓ1) :
                      (β (polIn r hf hn hr π)).1 =
                        leafIn r hf hn hr ℓ1
                          (heq1 ▸ leafOut_pos r hf hn hr ((β (polIn r hf hn hr π)).1)) := by
                    subst heq1
                    exact (leafIn_leafOut r hf hn hr _).symm
                  have hsame (hpos : 0 < leafValue r ℓ)
                      (hbase : (β (polIn r hf hn hr π)).1 = leafIn r hf hn hr ℓ hpos) :
                      (β (polIn r hf hn hr π)).1 = leafIn r hf hn hr ℓ hp := by
                    have hpEq : hpos = hp := Subsingleton.elim _ _
                    subst hpEq
                    exact hbase
                  exact hsame _ (htransport ℓ hout)
                simp [hne, hhit]
            · simp [mass_eq_zero_of_bad hΛbad hβ]
          simp_rw [hterm]
          have hm := Λ.marginal (polIn r hf hn hr π) (leafIn r hf hn hr ℓ hp) hcomp
          rw [hm]
          have hsc := leafOut_scale r hf hn hr (leafIn r hf hn hr ℓ hp)
          rw [leafOut_leafIn, hroot] at hsc
          rw [← hsc]
          exact (mul_div_cancel_right₀ (leafMass (leafIn r hf hn hr ℓ hp)) (ne_of_gt hη)).symm
        · have hz : leafValue r ℓ = 0 :=
            le_antisymm (le_of_not_gt hp) (leafValue_nonneg r hn ℓ)
          have hzero : ∀ β, (if (embed β π).1 = ℓ then Λ.mass β else (0 : ℝ)) = 0 := by
            intro β
            by_cases hβ : realizable β
            · have hleaf := hembed_leaf (π := π) hβ
              have hpos := leafOut_pos r hf hn hr ((β (polIn r hf hn hr π)).1)
              have hne : (embed β π).1 ≠ ℓ := by
                intro heq
                have : 0 < leafValue r ℓ := by simpa [← heq, hleaf] using hpos
                exact hp this
              simp [hne]
            · simp [mass_eq_zero_of_bad hΛbad hβ]
          simp_rw [hzero, Finset.sum_const_zero, hz, zero_div]
      rw [hνmarg, hlammarg]
      rw [mul_div_cancel₀ (leafMass ℓ - leafValue r ℓ) (ne_of_gt (sub_pos.mpr hη1)),
        mul_div_cancel₀ (leafValue r ℓ) (ne_of_gt hη)]
      ring
    let Γc : Coupling T :=
      { mass := mix
        nonneg := hmix0
        total := hmixSum
        marginal := hmixMarg }
    have hbad : Γc.badMass = 0 := by
      unfold Coupling.badMass
      refine Finset.sum_eq_zero fun α _ => ?_
      by_cases hrα : realizable α
      · simp [hrα]
      · have hνz : ν α = 0 := by simp [ν, hrα]
        have hlamz : lam α = 0 := by
          refine Finset.sum_eq_zero fun β _ => ?_
          by_cases hβ : embed β = α
          · exact absurd (hβ ▸ hembed_real β) hrα
          · simp [hβ]
        rw [ite_eq_right hrα]
        simp [Γc, mix, hνz, hlamz]
    have hgoodFun : (fun a => if ¬ realizable a then (0 : ℝ) else Γ.mass a / (1 - η)) = ν := by
      funext a
      by_cases ha : realizable a
      · simp [ν, ha]
      · simp [ν, ha]
    have hH : Γ.entropy =
        entTerm η + entTerm (1 - η) + (1 - η) * pmfEntropy ν + η * pmfEntropy μ := by
      have hrewrite := hsplit
      simp only [hgoodFun, ← hμEnt] at hrewrite
      simpa [Coupling.entropy] using hrewrite
    have hent : Γc.entropy < Γ.entropy + gapSup * η + ε := by
      have hmixEnt := pmfEntropy_mix_le ν lam η hν0 hlam0 hνsum hlamsum hη.le hη1.le
      have hmul : η * pmfEntropy lam < η * (pmfEntropy μ + gapSup + ε / η) :=
        mul_lt_mul_of_pos_left hlambound hη
      have hstep : pmfEntropy mix <
          entTerm (1 - η) + entTerm η + (1 - η) * pmfEntropy ν +
            η * (pmfEntropy μ + gapSup + ε / η) := by
        linarith
      have hscale : η * (pmfEntropy μ + gapSup + ε / η) =
          η * pmfEntropy μ + η * gapSup + ε := by
        calc
          η * (pmfEntropy μ + gapSup + ε / η)
            = η * pmfEntropy μ + η * gapSup + η * (ε / η) := by ring
          _ = η * pmfEntropy μ + η * gapSup + ε := by
            rw [mul_div_cancel₀ _ (ne_of_gt hη)]
      calc
        Γc.entropy = pmfEntropy mix := by simp [Coupling.entropy, Γc]
        _ < entTerm (1 - η) + entTerm η + (1 - η) * pmfEntropy ν +
              η * (pmfEntropy μ + gapSup + ε / η) := hstep
        _ = Γ.entropy + gapSup * η + ε := by
          rw [hscale, hH]
          ring
    exact ⟨Γc, hbad, hent⟩
  by_contra hgt
  have hlt0 : Γ.entropy + gapSup * η < causalMin T := lt_of_not_ge hgt
  have hε : 0 < causalMin T - (Γ.entropy + gapSup * η) := by linarith
  obtain ⟨Γc, hbad, hent⟩ := happrox hε
  linarith [causalMin_le_entropy_of_badMass hbad]

/-- For every coefficient at least the gap, the penalised infimum is the causal minimum. -/
theorem penaltyMin_eq_causalMin {κ : ℝ} (hκ : gapSup ≤ κ) (T : Tree) :
    penaltyMin κ T = causalMin T := by
  have hle : penaltyMin κ T ≤ causalMin T := by
    have hsub : causalEntropySet T ⊆ penaltySet κ T := by
      intro x ⟨Γ, hbad, hx⟩
      refine ⟨Γ, ?_⟩
      simp [penalised, hbad, hx]
    have hbdd : BddBelow (penaltySet κ T) :=
      ⟨0, fun x ⟨Γ, hx⟩ => hx ▸ add_nonneg (entropy_nonneg Γ)
        (mul_nonneg (le_trans gapSup_nonneg hκ) (badMass_nonneg Γ))⟩
    exact csInf_le_csInf hbdd (causalEntropySet_nonempty T) hsub
  have hge : causalMin T ≤ penaltyMin κ T := by
    refine le_csInf (penaltySet_nonempty κ T) ?_
    intro x ⟨Γ, hx⟩
    have hpen : causalMin T ≤ penalised κ Γ := by
      have hbase := causalMin_le_penalised Γ
      have hmul : gapSup * Γ.badMass ≤ κ * Γ.badMass :=
        mul_le_mul_of_nonneg_right hκ (badMass_nonneg Γ)
      unfold penalised at hbase ⊢
      linarith
    simpa [hx] using hpen
  linarith

#print axioms causalMin_le_penalised
#print axioms penaltyMin_eq_causalMin

end CausalSpectrum

