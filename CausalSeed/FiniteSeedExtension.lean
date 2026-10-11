/- Candidate, not locally compiled. Exact finite-to-infinite seed extension. -/
import CausalSeed.SeedDataProcessing

noncomputable section
open Classical Finset
open scoped ENNReal
namespace CausalSpectrum.Completion

theorem stratAgrees_append_left : ∀ {T : Tree} (d : Strategy T) (u v),
    stratAgrees d (u ++ v) → stratAgrees d u := by
  intro T
  induction T with
  | leaf =>
    intro d u v h
    simpa [stratAgrees] using (List.append_eq_nil_iff.mp h).1
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro d u v h
    cases u with
    | nil => trivial
    | cons p u =>
      obtain ⟨a, ha, hy, ht⟩ := h
      exact ⟨a, ha, hy, ih a (d.1 a) (d.2 a (d.1 a)) u v ht⟩

theorem run_mem_prefix_iff {T : Tree} (d : Strategy T) (h) :
    run d (followPol h) ∈ prefixLeaves h ↔ stratAgrees d h := by
  constructor
  · intro hm
    obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hm).2.1
    have hall : stratAgrees d (leafPath (run d (followPol h))) := by
      apply (stratAgrees_iff_compat d _).mpr
      exact ((run_eq_iff d (followPol h) _).mp rfl).1
    rw [← hv] at hall
    exact stratAgrees_append_left d h v hall
  · exact agrees_mem_prefix d h

theorem hitSum_eq_prefix {T : Tree} (atoms : List (Atom T)) (h) :
    hitSum atoms h = ∑ ℓ ∈ prefixLeaves h, transcriptWeight atoms (followPol h) ℓ := by
  induction atoms with
  | nil => simp [hitSum, transcriptWeight]
  | cons a tail ih =>
    rw [hitSum_cons, ih]
    have ht : ∀ ℓ, transcriptWeight (a :: tail) (followPol h) ℓ =
        (if run a.2 (followPol h) = ℓ then a.1 else 0) +
          transcriptWeight tail (followPol h) ℓ := by
      intro ℓ; simp [transcriptWeight]
    simp_rw [ht, Finset.sum_add_distrib]
    congr 1
    simp [run_mem_prefix_iff]

theorem finite_exact_prefix (ι : ITree) (n : ℕ)
    (atoms : List (Atom (trunc ι n [])))
    (hex : ∀ π ℓ, transcriptWeight atoms π ℓ =
      if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (h) (hh : h.length ≤ n) : hitSum atoms h = pathMass ι h := by
  rw [hitSum_eq_prefix]
  calc
    _ = ∑ ℓ ∈ prefixLeaves h, leafMass ℓ := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      rw [hex, if_pos (Finset.mem_filter.mp hℓ).2.2]
    _ = pathMass ι h := prefix_mass ι n [] h hh

namespace PaddedList

def eval {α M : Type*} [Zero M] (l : List α) (f : α → M) (i : ℕ) : M :=
  if hi : i < l.length then f (l[i]'hi) else 0

theorem sum_eval {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i ∈ range l.length, eval l f i = (l.map f).sum := by
  induction l with
  | nil => simp [eval]
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have hshift : ∀ i, eval (a :: l) f (i+1) = eval l f i := by
      intro i
      by_cases hi : i < l.length
      · simp [eval, hi, Nat.succ_lt_succ hi]
      · have hi' : ¬ i+1 < (a :: l).length := by simpa using hi
        simp [eval, hi, hi']
    simp_rw [hshift]
    rw [ih]
    simp [eval, add_comm]

theorem hasSum_eval {α M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (l : List α) (f : α → M) : HasSum (eval l f) (l.map f).sum := by
  rw [← sum_eval l f]
  apply hasSum_sum_of_ne_finset_zero
  intro i hi
  simp only [mem_range, not_lt] at hi
  simp [eval, not_lt.mpr hi]

end PaddedList

def listSeed (ι : ITree) (n : ℕ) (atoms : List (Atom (trunc ι n [])))
    (hn : ∀ a ∈ atoms, 0 ≤ a.1) (hm : totalWeight atoms = 1) : Seed ι where
  weight := PaddedList.eval atoms Prod.fst
  nonneg := by
    intro i
    unfold PaddedList.eval
    split_ifs with hi
    · exact hn _ (List.getElem_mem hi)
    · exact le_rfl
  mass := by
    have h : HasSum (PaddedList.eval atoms Prod.fst) (totalWeight atoms) :=
      PaddedList.hasSum_eval atoms Prod.fst
    rw [hm] at h
    exact h
  strategy := fun i => extend ι n
    (if hi : i < atoms.length then (atoms[i]'hi).2 else zeroStrategy _)

theorem listSeed_exact (ι : ITree) (n : ℕ) (atoms : List (Atom (trunc ι n [])))
    (hn : ∀ a ∈ atoms, 0 ≤ a.1) (hm : totalWeight atoms = 1)
    (hex : ∀ π ℓ, transcriptWeight atoms π ℓ =
      if CompatiblePolicy ℓ π then leafMass ℓ else 0) :
    (listSeed ι n atoms hn hm).ExactTo n := by
  intro h hh
  have hterm : (listSeed ι n atoms hn hm).hit h =
      PaddedList.eval atoms (fun a => if stratAgrees a.2 h then a.1 else 0) := by
    funext i
    by_cases hi : i < atoms.length
    · have hagree : iAgree ι (extend ι n (atoms[i]'hi).2) h ↔
          stratAgrees (atoms[i]'hi).2 h := by
        rw [iAgree_iff, extend]
        exact extendAbs_agreesFrom ι n [] h (atoms[i]'hi).2 hh
      simp only [Seed.hit, CountableSeed.hit, listSeed, PaddedList.eval, hi, dite_true, indAgree, hagree]
      split_ifs <;> simp
    · simp [Seed.hit, CountableSeed.hit, listSeed, PaddedList.eval, hi]
  change ∑' i, (listSeed ι n atoms hn hm).hit h i = _
  rw [hterm, (PaddedList.hasSum_eval atoms _).tsum_eq]
  exact finite_exact_prefix ι n atoms hex h hh

theorem listSeed_entropy (ι : ITree) (n : ℕ) (atoms : List (Atom (trunc ι n [])))
    (hn : ∀ a ∈ atoms, 0 ≤ a.1) (hm : totalWeight atoms = 1) :
    (listSeed ι n atoms hn hm).entropy =
      ENNReal.ofReal (seedShannon atoms * Real.log 2) := by
  let S := listSeed ι n atoms hn hm
  have hterm : (fun i => ENNReal.ofReal (Real.negMulLog (S.weight i))) =
      PaddedList.eval atoms (fun a => ENNReal.ofReal (Real.negMulLog a.1)) := by
    funext i
    by_cases hi : i < atoms.length <;>
      simp [S, listSeed, PaddedList.eval, hi, Real.negMulLog_def]
  have hle : ∀ a ∈ atoms, a.1 ≤ 1 := by
    intro a ha
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
    have := S.weight_le_one i
    simpa [S, listSeed, PaddedList.eval, hi, he] using this
  have hnat : (atoms.map (fun a => Real.negMulLog a.1)).sum =
      seedShannon atoms * Real.log 2 := by
    have hpoint : ∀ a : Atom (trunc ι n []), Real.negMulLog a.1 =
        (a.1 * infoMass a.1) * Real.log 2 := by
      intro a
      by_cases hz : a.1 = 0
      · simp [hz, Real.negMulLog_def]
      · simpa [CausalSpectrum.entTerm, hz] using (entTerm_nats a.1).symm
    simp_rw [hpoint]
    have hmul : ∀ l : List (Atom (trunc ι n [])),
        (l.map (fun a => a.1 * infoMass a.1 * Real.log 2)).sum =
          (l.map (fun a => a.1 * infoMass a.1)).sum * Real.log 2 := by
      intro l
      induction l with
      | nil => simp
      | cons b l ih => simp [ih, add_mul]
    rw [hmul, seedShannon]
  have hnn : ∀ x ∈ atoms.map (fun a => Real.negMulLog a.1), 0 ≤ x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Real.negMulLog_nonneg (hn a ha) (hle a ha)
  change (∑' i, ENNReal.ofReal (Real.negMulLog (S.weight i))) = _
  rw [hterm, (PaddedList.hasSum_eval atoms _).tsum_eq, ← hnat]
  have ofReal_list : ∀ (l : List ℝ), (∀ x ∈ l, 0 ≤ x) →
      (l.map ENNReal.ofReal).sum = ENNReal.ofReal l.sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro h
      rw [List.map_cons, List.sum_cons, List.sum_cons,
        ih (fun x hx => h x (by simp [hx]))]
      exact (ENNReal.ofReal_add (h a (by simp))
        (List.sum_nonneg (fun x hx => h x (by simp [hx])))).symm
  simpa [List.map_map, Function.comp_def] using ofReal_list _ hnn

theorem finite_envelope_upper (ι : ITree) (n : ℕ) :
    countableFiniteCost ι n ≤
      ENNReal.ofReal ((envelopeMean (trunc ι n []) + shannonOverhead) * Real.log 2) := by
  obtain ⟨atoms, _, hp, hm, hex, _, hupper⟩ := one_seed_shannon (trunc ι n [])
  let hn := fun a ha => (hp a ha).le
  let S := listSeed ι n atoms hn hm
  have hS := listSeed_exact ι n atoms hn hm hex
  calc
    countableFiniteCost ι n ≤ S.entropy := iInf_le_of_le ⟨S, hS⟩ le_rfl
    _ = ENNReal.ofReal (seedShannon atoms * Real.log 2) := listSeed_entropy ι n atoms hn hm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hupper
      (le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 2))))

end CausalSpectrum.Completion
