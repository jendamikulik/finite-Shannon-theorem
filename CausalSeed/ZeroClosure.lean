/-
Zero probabilities, part 3: closure of the finite causal realization.

For a finite controlled tree whose kernels may vanish (no branch removed)
there is a finite seed — a law `q` on the finite set of total response
strategies of the whole original tree, decoded deterministically by `run` —
exact for every deterministic adaptive policy, with
`L(K) ≤ H(q) ≤ L(K) + c⋆`, `c⋆ = (1 + log₂ e)/2` (bits).
-/
import CausalSeed.ZeroTree

noncomputable section
open Classical Finset Filter
open scoped Topology
namespace CausalSpectrum.Zero
open Shape

/-! ### Merging the atoms of a positive-tree seed -/

section Merge
variable {T : Tree}

def merged (atoms : List (Atom T)) (d : Strategy T) : ℝ :=
  (atoms.map fun a => if a.2 = d then a.1 else 0).sum

theorem merged_cons (a : Atom T) (tail : List (Atom T)) (d : Strategy T) :
    merged (a :: tail) d = (if a.2 = d then a.1 else 0) + merged tail d := by
  simp [merged]

theorem merged_nonneg : ∀ (atoms : List (Atom T)), (∀ a ∈ atoms, 0 < a.1) → ∀ d,
    0 ≤ merged atoms d := by
  intro atoms
  induction atoms with
  | nil => intro _ d; simp [merged]
  | cons a tail ih =>
      intro h d
      rw [merged_cons]
      have := ih (fun b hb => h b (by simp [hb])) d
      have := h a (by simp)
      split_ifs <;> linarith

theorem merged_sum : ∀ (atoms : List (Atom T)), ∑ d, merged atoms d = totalWeight atoms := by
  intro atoms
  induction atoms with
  | nil => simp [merged, totalWeight]
  | cons a tail ih =>
      simp_rw [merged_cons]
      rw [Finset.sum_add_distrib, ih]
      simp [totalWeight]

theorem merged_exact : ∀ (atoms : List (Atom T)) (π : Policy T) (ℓ : Leaf T),
    (∑ d, if CausalSpectrum.run d π = ℓ then merged atoms d else 0) =
      transcriptWeight atoms π ℓ := by
  intro atoms π ℓ
  induction atoms with
  | nil => simp [merged, transcriptWeight]
  | cons a tail ih =>
      have ht : transcriptWeight (a :: tail) π ℓ =
          (if CausalSpectrum.run a.2 π = ℓ then a.1 else 0) + transcriptWeight tail π ℓ := by
        simp [transcriptWeight]
      rw [ht, ← ih]
      have hsplit : ∀ d, (if CausalSpectrum.run d π = ℓ then merged (a :: tail) d else 0) =
          (if CausalSpectrum.run d π = ℓ ∧ a.2 = d then a.1 else 0) +
            (if CausalSpectrum.run d π = ℓ then merged tail d else 0) := by
        intro d; rw [merged_cons]; split_ifs <;> simp_all
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single a.2]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp

theorem merged_entropy : ∀ (atoms : List (Atom T)), (∀ a ∈ atoms, 0 < a.1) →
    pmfEntropy (merged atoms) ≤ (atoms.map fun a => entTerm a.1).sum := by
  intro atoms
  induction atoms with
  | nil => intro _; simp [pmfEntropy, merged, entTerm]
  | cons a tail ih =>
      intro h
      have hT := fun b hb => h b (List.mem_cons_of_mem a hb)
      have ha := h a (by simp)
      have hstep : ∀ d, entTerm (merged (a :: tail) d) ≤
          entTerm (if a.2 = d then a.1 else 0) + entTerm (merged tail d) := fun d => by
        rw [merged_cons]
        exact entTerm_add_le (by split_ifs <;> linarith) (merged_nonneg tail hT d)
      have hhead : ∑ d, entTerm (if a.2 = d then a.1 else 0) = entTerm a.1 := by
        rw [Finset.sum_eq_single a.2]
        · simp
        · intro b _ hb; simp [Ne.symm hb, entTerm_zero]
        · simp
      have := Finset.sum_le_sum fun d (_ : d ∈ Finset.univ) => hstep d
      rw [Finset.sum_add_distrib, hhead] at this
      have := ih hT
      simp only [List.map_cons, List.sum_cons]
      unfold pmfEntropy at *
      linarith

/-- The existing finite theorem, as an exact law on strategies of an ordinary tree. -/
theorem tree_seed (T : Tree) :
    ∃ q : Strategy T → ℝ, IsPmf q ∧
      Exact CausalSpectrum.run (fun ℓ π => CompatiblePolicy ℓ π) (fun ℓ : Leaf T => leafMass ℓ) q ∧
      pmfEntropy q ≤ envelopeMean T + shannonOverhead := by
  obtain ⟨atoms, -, hpos, htot, hex, -, hup⟩ := one_seed_shannon T
  refine ⟨merged atoms, ⟨merged_nonneg atoms hpos, by rw [merged_sum, htot]⟩,
    fun π ℓ => by rw [merged_exact, hex], ?_⟩
  refine (merged_entropy atoms hpos).trans ?_
  rw [entTerm_list_eq atoms hpos]
  exact hup

end Merge

/-- Transport of `tree_seed` to the shape of a positive kernel field. -/
theorem shape_seed (S : Shape) (k : KField S) (h : PosValid S k) :
    ∃ q : Str S → ℝ, IsPmf q ∧ Exact Shape.run compat (mass k) q ∧
      pmfEntropy q ≤ Lenv (P := Pol S) compat (mass k) + shannonOverhead := by
  obtain ⟨q', hp, he, hH⟩ := tree_seed (toTree S k h)
  refine ⟨q' ∘ strE S k h, pmf_transport _ hp, ?_, ?_⟩
  · have := exact_transport (polE S k h) (strE S k h) (lfE S k h) (compat_E S k h)
      (run_E S k h) he
    convert this using 1
    funext ℓ; exact (mass_E S k h ℓ).symm
  · rw [entropy_transport, Lenv_shape_eq S k h]; exact hH

/-- **Closure of the finite causal realization under zero probabilities.**
For a finite controlled tree with kernels `K ≥ 0` (all branches kept) there is a
law `q` on the finite set of total response strategies of the whole tree, decoded
by the deterministic map `s ↦ run s π`, that is exact for every deterministic
adaptive policy and satisfies `L(K) ≤ H(q) ≤ L(K) + c⋆`. -/
theorem zero_closure (Z : ZTree) :
    ∃ q : Z.Str → ℝ, IsPmf q ∧
      (∀ (π : Z.Pol) (ℓ : Z.Lf),
        (∑ s, if Shape.run s π = ℓ then q s else 0) = if compat ℓ π then Z.P ℓ else 0) ∧
      Z.L ≤ pmfEntropy q ∧ pmfEntropy q ≤ Z.L + shannonOverhead := by
  set ε : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 2)
  have hε0 : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [ε]; rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => (n:ℝ) + 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_const_nhds.div_atTop h2
  have hpv := fun n => mix_posValid (hε0 n) (hε1 n) Z.valid
  have hlim : ∀ ℓ, Tendsto (fun n => mass (mix (ε n) Z.K) ℓ) atTop (𝓝 (Z.P ℓ)) := by
    intro ℓ
    have := ((mass_mix_continuous Z.K ℓ).tendsto 0).comp hεt
    rw [mass_mix_zero] at this
    exact this
  exact closure_of_approx (run := Shape.run) (compat := compat) run_compat hlim
    (fun n => mass_nonneg (posValid_valid (hpv n))) (mass_nonneg Z.valid)
    (fun n => shape_seed _ _ (hpv n))

/-- In particular every exact law (of any finite seed) has `H ≥ L(K)`. -/
theorem zero_lower (Z : ZTree) {q : Z.Str → ℝ} (hq : IsPmf q)
    (he : ∀ (π : Z.Pol) (ℓ : Z.Lf),
      (∑ s, if Shape.run s π = ℓ then q s else 0) = if compat ℓ π then Z.P ℓ else 0) :
    Z.L ≤ pmfEntropy q :=
  Lenv_le_entropy (run := Shape.run) run_compat (mass_nonneg Z.valid) hq he

#print axioms zero_closure
#print axioms zero_lower
#print axioms ZTree.L_ofTree

end CausalSpectrum.Zero
