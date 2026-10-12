/-
Preservation of the seed space under positive-support reduction.

For every measure space `(Ω, μ)` and every horizon, `(Ω, μ)` carries an exact causal decoder for
the nonnegative tree `T` iff it carries one for its positive reduction `T⁺ = T.plus`; the same
holds simultaneously for all horizons. The conversions are `D ↦ R ∘ D` and `D⁺ ↦ E ∘ D⁺`; they do
not change `Ω` or `μ`. The countable-seed version keeps the seed weights, so all seed costs agree.
-/
import CausalSeed.ZeroBranch

noncomputable section
open Classical Finset MeasureTheory
open scoped ENNReal

namespace CausalSpectrum.ZeroBranch
namespace NNTree
variable (T : NNTree)

/-! ### Decoders on a measure space -/

/-- A causal decoder for `T` on `Ω`: a response at every history and action, each coordinate
measurable. -/
structure Decoder (Ω : Type*) [MeasurableSpace Ω] where
  D : Ω → T.Strat
  meas : ∀ p, Measurable fun ω => D ω p

/-- A causal decoder for the reduced tree `T⁺`. -/
structure DecoderP (Ω : Type*) [MeasurableSpace Ω] where
  D : Ω → IStrategy T.plus
  meas : ∀ p, Measurable fun ω => D ω p

variable {T}
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Exactness to horizon `n`: every history of length `≤ n` is reproduced with its mass. -/
def Decoder.ExactTo (D : T.Decoder Ω) (n : ℕ) : Prop :=
  ∀ h : List (ℕ × ℕ), h.length ≤ n → μ {ω | T.Agree (D.D ω) h} = ENNReal.ofReal (T.pathMass h)

def DecoderP.ExactTo (D : T.DecoderP Ω) (n : ℕ) : Prop :=
  ∀ h : List (ℕ × ℕ), h.length ≤ n →
    μ {ω | iAgree T.plus (D.D ω) h} = ENNReal.ofReal (CausalSpectrum.pathMass T.plus h)

variable (T)

theorem R_coord (p : CausalSpectrum.NodeIdx T.plus) :
    ∃ g : Fin (T.nY (T.lift p.1) p.2) → Fin (T.plus.nY p.1 p.2),
      ∀ s : T.Strat, T.R s p = g (s ⟨T.lift p.1, p.2⟩) :=
  ⟨T.rIdx (T.lift p.1) p.2, fun _ => rfl⟩

theorem E_coord (p : T.NodeIdx) :
    (∃ c : T.nY p.1 p.2 |> Fin, ∀ s, T.E s p = c) ∨
      ∃ q : CausalSpectrum.NodeIdx T.plus, ∃ g : Fin (T.plus.nY q.1 q.2) → Fin (T.nY p.1 p.2),
        ∀ s, T.E s p = g (s q) := by
  obtain ⟨h, a⟩ := p
  by_cases hp : ∃ h', T.lift h' = h
  · right
    obtain ⟨h', rfl⟩ := hp
    exact ⟨⟨h', a⟩, fun i => (T.emb (T.lift h') a i).1, fun s => T.E_lift s h' a⟩
  · left
    exact ⟨(T.emb h a ⟨0, T.card_supp_pos h a⟩).1, fun s => by simp only [E, dif_neg hp]⟩

variable {T}

/-- The reduced decoder `R D`. -/
def Decoder.red (D : T.Decoder Ω) : T.DecoderP Ω where
  D ω := T.R (D.D ω)
  meas p := by
    obtain ⟨g, hg⟩ := T.R_coord p
    have : (fun ω => T.R (D.D ω) p) = fun ω => g (D.D ω ⟨T.lift p.1, p.2⟩) := funext fun ω => hg _
    rw [this]
    exact (measurable_of_countable g).comp (D.meas _)

/-- The extended (total) decoder `E D⁺`. -/
def DecoderP.ext (D : T.DecoderP Ω) : T.Decoder Ω where
  D ω := T.E (D.D ω)
  meas p := by
    rcases T.E_coord p with ⟨c, hc⟩ | ⟨q, g, hg⟩
    · have : (fun ω => T.E (D.D ω) p) = fun _ => c := funext fun ω => hc _
      rw [this]; exact measurable_const
    · have : (fun ω => T.E (D.D ω) p) = fun ω => g (D.D ω q) := funext fun ω => hg _
      rw [this]; exact (measurable_of_countable g).comp (D.meas _)

/-- `R E D⁺ = D⁺` pointwise. -/
theorem red_ext (D : T.DecoderP Ω) (ω : Ω) : D.ext.red.D ω = D.D ω := T.R_E _

/-- **Restriction preserves exactness.** -/
theorem Decoder.ExactTo.red {D : T.Decoder Ω} {n : ℕ} (hD : D.ExactTo μ n) :
    D.red.ExactTo μ n := by
  intro h' hl
  set A := {ω | iAgree T.plus (D.red.D ω) h'}
  set B := {ω | T.Agree (D.D ω) (T.lift h')}
  set N := ⋃ g : List (ℕ × ℕ), ⋃ (_ : g.length ≤ n ∧ T.pathMass g = 0),
    {ω | T.Agree (D.D ω) g}
  have hN : μ N = 0 :=
    measure_iUnion_null fun g => measure_iUnion_null fun hg => by
      rw [hD g hg.1, hg.2, ENNReal.ofReal_zero]
  have hBA : B ⊆ A := fun ω hω => T.agree_R _ h' hω
  have hAB : A ⊆ B ∪ N := by
    intro ω hω
    rcases T.agree_R_back _ h' hω with hl' | ⟨g, hg, h0, hag⟩
    · exact Or.inl hl'
    · exact Or.inr (Set.mem_iUnion.2 ⟨g, Set.mem_iUnion.2 ⟨⟨hg.trans hl, h0⟩, hag⟩⟩)
  have hAeq : μ A = μ B := le_antisymm
    ((measure_mono hAB).trans ((measure_union_le B N).trans (by rw [hN, add_zero])))
    (measure_mono hBA)
  show μ A = _
  rw [hAeq, hD _ (by rw [length_lift]; exact hl), pathMass_plus]

/-- **Extension preserves exactness.** -/
theorem DecoderP.ExactTo.ext {D : T.DecoderP Ω} {n : ℕ} (hD : D.ExactTo μ n) :
    D.ext.ExactTo μ n := by
  intro h hl
  by_cases hp : ∃ h', T.lift h' = h
  · obtain ⟨h', rfl⟩ := hp
    have hs : {ω | T.Agree (D.ext.D ω) (T.lift h')} = {ω | iAgree T.plus (D.D ω) h'} := by
      ext ω; exact T.agree_E_lift _ h'
    rw [hs, hD h' (by rw [length_lift] at hl; exact hl), pathMass_plus]
  · have hs : {ω | T.Agree (D.ext.D ω) h} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hA => hp (T.exists_lift_of_agree_E _ hA)
    have h0 : T.pathMass h = 0 := by
      by_contra hne; exact hp (T.exists_lift_of_pathMass_ne hne)
    rw [hs, h0, measure_empty, ENNReal.ofReal_zero]

variable (T)

/-- **Theorem (preservation of the seed space), fixed horizon.** A measure space carries an
exact causal decoder for `T` to horizon `n` iff it carries one for `T⁺`. -/
theorem seed_space_iff (n : ℕ) :
    (∃ D : T.Decoder Ω, D.ExactTo μ n) ↔ ∃ D : T.DecoderP Ω, D.ExactTo μ n :=
  ⟨fun ⟨D, hD⟩ => ⟨D.red, hD.red μ⟩, fun ⟨D, hD⟩ => ⟨D.ext, hD.ext μ⟩⟩

/-- **Theorem (preservation of the seed space), all horizons simultaneously,** by one decoder. -/
theorem seed_space_iff_all :
    (∃ D : T.Decoder Ω, ∀ n, D.ExactTo μ n) ↔ ∃ D : T.DecoderP Ω, ∀ n, D.ExactTo μ n :=
  ⟨fun ⟨D, hD⟩ => ⟨D.red, fun n => (hD n).red μ⟩,
    fun ⟨D, hD⟩ => ⟨D.ext, fun n => (hD n).ext μ⟩⟩

/-! ### Countable seeds -/

/-- A countable seed for `T`: weights on `ℕ` and a response strategy per atom. -/
structure Seed where
  weight : ℕ → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  mass : HasSum weight 1
  strategy : ℕ → T.Strat

namespace Seed
variable {T}

def entropy (S : T.Seed) : ℝ≥0∞ := ∑' i, ENNReal.ofReal (Real.negMulLog (S.weight i))

def hit (S : T.Seed) (h : List (ℕ × ℕ)) (i : ℕ) : ℝ :=
  S.weight i * if T.Agree (S.strategy i) h then 1 else 0

def ExactTo (S : T.Seed) (n : ℕ) : Prop :=
  ∀ h : List (ℕ × ℕ), h.length ≤ n → ∑' i, S.hit h i = T.pathMass h

def Exact (S : T.Seed) : Prop := ∀ n, S.ExactTo n

theorem hit_nonneg (S : T.Seed) (h) (i) : 0 ≤ S.hit h i :=
  mul_nonneg (S.nonneg i) (by split_ifs <;> norm_num)

theorem hit_summable (S : T.Seed) (h) : Summable (S.hit h) :=
  Summable.of_nonneg_of_le (S.hit_nonneg h) (fun i => by
    unfold hit; split_ifs <;> simp [S.nonneg i]) S.mass.summable

/-- The reduced seed: same weights, strategies `R ∘ s_i`. -/
def red (S : T.Seed) : Completion.Seed T.plus where
  weight := S.weight
  nonneg := S.nonneg
  mass := S.mass
  strategy i := T.R (S.strategy i)

end Seed

/-- The extended seed of a reduced seed: same weights, strategies `E ∘ s_i`. -/
def extSeed (S : Completion.Seed T.plus) : T.Seed where
  weight := S.weight
  nonneg := S.nonneg
  mass := S.mass
  strategy i := T.E (S.strategy i)

theorem extSeed_red (S : Completion.Seed T.plus) : (T.extSeed S).red = S := by
  cases S; simp only [extSeed, Seed.red, R_E]

theorem red_entropy (S : T.Seed) : S.red.entropy = S.entropy := rfl
theorem extSeed_entropy (S : Completion.Seed T.plus) : (T.extSeed S).entropy = S.entropy := rfl

variable {T}

theorem Seed.ExactTo.red {S : T.Seed} {n : ℕ} (hS : S.ExactTo n) : S.red.ExactTo n := by
  intro h' hl
  have hl' : (T.lift h').length ≤ n := by rw [length_lift]; exact hl
  rw [pathMass_plus, ← hS _ hl']
  refine tsum_congr fun i => ?_
  show S.weight i * indAgree T.plus (T.R (S.strategy i)) h' = S.hit (T.lift h') i
  unfold Seed.hit indAgree
  by_cases hw : S.weight i = 0
  · simp [hw]
  congr 1
  by_cases hA : iAgree T.plus (T.R (S.strategy i)) h'
  · rcases T.agree_R_back _ h' hA with hl'' | ⟨g, hg, h0, hag⟩
    · simp [hA, hl'']
    · exfalso
      have hle := le_hasSum (S.hit_summable g).hasSum i (fun j _ => S.hit_nonneg g j)
      rw [hS g (hg.trans hl), h0] at hle
      have : S.hit g i = S.weight i := by simp [Seed.hit, hag]
      exact hw (le_antisymm (this ▸ hle) (S.nonneg i))
  · have : ¬ T.Agree (S.strategy i) (T.lift h') := fun h => hA (T.agree_R _ h' h)
    simp [hA, this]

theorem extSeed_exactTo {S : Completion.Seed T.plus} {n : ℕ} (hS : S.ExactTo n) :
    (T.extSeed S).ExactTo n := by
  intro h hl
  by_cases hp : ∃ h', T.lift h' = h
  · obtain ⟨h', rfl⟩ := hp
    rw [← pathMass_plus, ← hS h' (by rw [length_lift] at hl; exact hl)]
    refine tsum_congr fun i => ?_
    show S.weight i * (if T.Agree (T.E (S.strategy i)) (T.lift h') then 1 else 0) =
      S.weight i * indAgree T.plus (S.strategy i) h'
    unfold indAgree
    rw [T.agree_E_lift]
  · have h0 : T.pathMass h = 0 := by
      by_contra hne; exact hp (T.exists_lift_of_pathMass_ne hne)
    rw [h0]
    refine (tsum_congr fun i => ?_).trans tsum_zero
    have : ¬ T.Agree (T.E (S.strategy i)) h := fun hA => hp (T.exists_lift_of_agree_E _ hA)
    simp [Seed.hit, extSeed, this]

variable (T)

/-- Countable-seed Shannon cost (nats) of `T` to horizon `n`. -/
def finiteCost (n : ℕ) : ℝ≥0∞ := ⨅ S : {S : T.Seed // S.ExactTo n}, S.1.entropy

/-- Countable-seed Shannon cost (nats) of `T` at all horizons simultaneously. -/
def infiniteCost : ℝ≥0∞ := ⨅ S : {S : T.Seed // S.Exact}, S.1.entropy

theorem finiteCost_eq (n : ℕ) : T.finiteCost n = Completion.countableFiniteCost T.plus n := by
  apply le_antisymm
  · refine le_iInf fun G => ?_
    exact iInf_le_of_le ⟨T.extSeed G.1, extSeed_exactTo G.2⟩ (le_of_eq (T.extSeed_entropy _))
  · refine le_iInf fun S => ?_
    exact iInf_le_of_le ⟨S.1.red, S.2.red⟩ (le_of_eq (T.red_entropy _))

theorem infiniteCost_eq : T.infiniteCost = Completion.countableInfiniteCost T.plus := by
  apply le_antisymm
  · refine le_iInf fun G => ?_
    exact iInf_le_of_le ⟨T.extSeed G.1, fun n => extSeed_exactTo (G.2 n)⟩
      (le_of_eq (T.extSeed_entropy _))
  · refine le_iInf fun S => ?_
    exact iInf_le_of_le ⟨S.1.red, fun n => (S.2 n).red⟩ (le_of_eq (T.red_entropy _))

/-- **Corollary 1 (projective identity).** `C_∞(T) = sup_n C_n(T)`. -/
theorem infiniteCost_eq_iSup : T.infiniteCost = ⨆ n, T.finiteCost n := by
  rw [infiniteCost_eq, Completion.countable_projective_entropy_identity]
  simp only [finiteCost_eq]

/-- **Corollary 1 (attainment).** If `sup_n C_n(T) < ∞`, one countable seed on the original tree,
exact at every horizon, attains `C_∞(T)`. -/
theorem infiniteCost_attained (hfin : (⨆ n, T.finiteCost n) ≠ ∞) :
    ∃ S : T.Seed, S.Exact ∧ S.entropy = T.infiniteCost := by
  simp only [finiteCost_eq] at hfin
  obtain ⟨G, hG, he⟩ := Completion.countable_entropy_attained T.plus hfin
  exact ⟨T.extSeed G, fun n => extSeed_exactTo (hG n), by rw [extSeed_entropy, he, infiniteCost_eq]⟩

end NNTree
end CausalSpectrum.ZeroBranch
