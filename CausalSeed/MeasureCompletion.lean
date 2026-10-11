/-
Construction of the residual probability measure and the exact mixture.
It does not assume residual realization as a hypothesis.
-/
import CausalSeed.Capacity
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn

noncomputable section
open Classical MeasureTheory Finset
open scoped ENNReal
namespace CausalSpectrum
namespace Completion

def cylinder (ι : ITree) (h : List (ℕ × ℕ)) : Set (IStrategy ι) :=
  {s | iAgree ι s h}

theorem measurable_agrees (ι : ITree) (pref todo : List (ℕ × ℕ)) :
    MeasurableSet {s : IStrategy ι | agreesFrom ι s pref todo} := by
  induction todo generalizing pref with
  | nil => simpa [agreesFrom] using (MeasurableSet.univ :
      MeasurableSet (Set.univ : Set (IStrategy ι)))
  | cons p t ih =>
      have heq : {s : IStrategy ι | agreesFrom ι s pref (p :: t)} =
          ⋃ a : Fin (ι.nA pref),
            {s : IStrategy ι | a.val = p.1 ∧ (s ⟨pref,a⟩).val = p.2} ∩
              {s | agreesFrom ι s (pref ++ [p]) t} := by
        ext s
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, agreesFrom]
        aesop
      rw [heq]
      apply MeasurableSet.iUnion
      intro a
      apply MeasurableSet.inter _ (ih _)
      by_cases ha : a.val = p.1
      · have hset : {s : IStrategy ι | a.val = p.1 ∧ (s ⟨pref, a⟩).val = p.2} =
            (fun s : IStrategy ι => (s ⟨pref, a⟩).val) ⁻¹' {p.2} := by
          ext s
          simp [ha]
        rw [hset]
        exact (measurableSet_singleton p.2).preimage
          ((measurable_of_finite (fun y : Fin (ι.nY pref a) => y.val)).comp
            (measurable_pi_apply (⟨pref, a⟩ : NodeIdx ι)))
      · have hempty : {s : IStrategy ι | a.val = p.1 ∧ (s ⟨pref, a⟩).val = p.2} = ∅ := by
          ext s
          simp [ha]
        simp [hempty]

theorem measurable_cylinder (ι : ITree) (h : List (ℕ × ℕ)) :
    MeasurableSet (cylinder ι h) := by
  simpa only [cylinder, iAgree_iff] using measurable_agrees ι [] h

theorem diag_summable (ι : ITree) : Summable (diagWeight ι) :=
  summable_of_sum_range_le (diagWeight_nonneg ι) fun M => diagPartial_le_atomQ ι M

theorem atomMeasure_univ (ι : ITree) :
    atomMeasure ι Set.univ = ENNReal.ofReal (atomQ ι) := by
  simp only [atomMeasure, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (diagWeight_nonneg ι) (diag_summable ι),
    diagMass_eq_tsum_atomQ]

theorem atomMeasure_cylinder (ι : ITree) (h : List (ℕ × ℕ)) :
    atomMeasure ι (cylinder ι h) = ENNReal.ofReal (cylMass ι h) := by
  rw [atomMeasure, Measure.sum_apply _ (measurable_cylinder ι h)]
  rw [cylMass, ENNReal.ofReal_tsum_of_nonneg (cyl_term_nonneg ι h) (cyl_summable ι h)]
  apply tsum_congr
  intro i
  by_cases hi : iAgree ι (capStrat ι i) h
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (measurable_cylinder ι h),
      cylinder, indAgree, hi]
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (measurable_cylinder ι h),
      cylinder, indAgree, hi]

def atomicSupport (ι : ITree) : Set (IStrategy ι) := Set.range (capStrat ι)

theorem atomicSupport_countable (ι : ITree) : (atomicSupport ι).Countable :=
  Set.countable_range _

theorem atomMeasure_support (ι : ITree) :
    atomMeasure ι (atomicSupport ι) = ENNReal.ofReal (atomQ ι) := by
  have hm := (atomicSupport_countable ι).measurableSet
  rw [atomMeasure, Measure.sum_apply _ hm]
  have hh : ∀ i, Measure.dirac (capStrat ι i) (atomicSupport ι) = 1 := by
    intro i
    exact Measure.dirac_apply_of_mem ⟨i, rfl⟩
  simp only [Measure.smul_apply, smul_eq_mul, hh, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (diagWeight_nonneg ι) (diag_summable ι),
    diagMass_eq_tsum_atomQ]

def residualCoordinate (ι : ITree) (p : NodeIdx ι) :
    Measure (Fin (ι.nY p.1 p.2)) :=
  Measure.sum fun y => ENNReal.ofReal (resRatioStep ι p.1 (p.2.val,y.val)) •
    Measure.dirac y

instance residualCoordinate_probability (ι : ITree) (p : NodeIdx ι) :
    IsProbabilityMeasure (residualCoordinate ι p) := by
  constructor
  rw [residualCoordinate, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg
      (fun y _ => resRatioStep_nonneg ι p.1 (p.2.val, y.val)),
    resRatioStep_sum]
  simp

theorem residualCoordinate_singleton (ι : ITree) (p : NodeIdx ι)
    (y : Fin (ι.nY p.1 p.2)) :
    residualCoordinate ι p {y} =
      ENNReal.ofReal (resRatioStep ι p.1 (p.2.val,y.val)) :=
  Measure.sum_smul_dirac_singleton

def residualMeasure (ι : ITree) : Measure (IStrategy ι) :=
  Measure.infinitePi (residualCoordinate ι)

instance residualMeasure_probability (ι : ITree) :
    IsProbabilityMeasure (residualMeasure ι) := by
  unfold residualMeasure
  infer_instance

/- A finite list of distinct coordinate constraints. -/
abbrev Assignment (ι : ITree) := Σ p : NodeIdx ι, Fin (ι.nY p.1 p.2)

def satisfies (ι : ITree) (L : List (Assignment ι)) : Set (IStrategy ι) :=
  {s | ∀ c ∈ L, s c.1 = c.2}

theorem product_constraints (ι : ITree) (L : List (Assignment ι))
    (hn : (L.map Sigma.fst).Nodup) :
    residualMeasure ι (satisfies ι L) =
      (L.map fun c => residualCoordinate ι c.1 {c.2}).prod := by
  let key : Fin L.length → NodeIdx ι := fun i => (L.get i).1
  let val : (i : Fin L.length) → Fin (ι.nY (key i).1 (key i).2) :=
    fun i => (L.get i).2
  have hinj : Function.Injective key := by
    intro i j hij
    apply Fin.ext
    have hget : (L.map Sigma.fst)[i.val] = (L.map Sigma.fst)[j.val] := by
      simpa [key, List.getElem_map] using hij
    exact (hn.getElem_inj_iff).mp hget
  let f : IStrategy ι → ((i : Fin L.length) → Fin (ι.nY (key i).1 (key i).2)) :=
    fun s i => s (key i)
  have hf : Measurable f := by fun_prop
  have hevent : satisfies ι L = f ⁻¹' {val} := by
    ext s
    simp only [satisfies, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hs
      funext i
      exact hs _ (List.get_mem _ _)
    · intro hs c hc
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
      exact congrFun hs i
  rw [hevent, ← Measure.map_apply hf (measurableSet_singleton val)]
  change (Measure.infinitePi (residualCoordinate ι)).map f {val} = _
  rw [Measure.map_infinitePi_infinitePi_of_inj hinj,
    Measure.infinitePi_singleton_of_fintype]
  rw [← List.prod_ofFn]
  congr 1
  simpa [key, val] using
    (List.ofFn_getElem_eq_map L (fun c => residualCoordinate ι c.1 {c.2}))

/- Valid histories, with the last action/output explicit. -/
inductive ValidPath (ι : ITree) : List (ℕ × ℕ) → Type
  | nil : ValidPath ι []
  | snoc {h} (t : ValidPath ι h) (a : Fin (ι.nA h)) (y : Fin (ι.nY h a)) :
      ValidPath ι (h ++ [(a.val,y.val)])

def assignments {ι : ITree} {h} : ValidPath ι h → List (Assignment ι)
  | .nil => []
  | .snoc t a y => assignments t ++ [⟨⟨_,a⟩,y⟩]

theorem assignments_short {ι : ITree} {h} (t : ValidPath ι h) :
    ∀ c ∈ assignments t, c.1.1.length < h.length := by
  induction t with
  | nil => simp [assignments]
  | @snoc h t a y ih =>
      intro c hc
      simp only [assignments, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · have := ih c hc
        simp only [List.length_append, List.length_singleton]
        omega
      · simp

theorem assignments_nodup {ι : ITree} {h} (t : ValidPath ι h) :
    ((assignments t).map Sigma.fst).Nodup := by
  induction t with
  | nil => simp [assignments]
  | @snoc h t a y ih =>
      have hnot : (⟨h,a⟩ : NodeIdx ι) ∉ (assignments t).map Sigma.fst := by
        intro hh
        obtain ⟨c,hc,he⟩ := List.mem_map.mp hh
        have hl := assignments_short t c hc
        rw [he] at hl
        exact (Nat.lt_irrefl _) hl
      rw [assignments, List.map_append]
      refine List.Nodup.append ih (by simp) ?_
      intro x hx hx2
      have he := List.mem_singleton.mp hx2
      rw [he] at hx
      exact hnot hx

theorem assignments_cylinder {ι : ITree} {h} (t : ValidPath ι h) :
    satisfies ι (assignments t) = cylinder ι h := by
  induction t with
  | nil => ext s; simp [assignments, satisfies, cylinder, iAgree_nil]
  | @snoc h t a y ih =>
      ext s
      have hp : (∀ c ∈ assignments t, s c.1 = c.2) ↔ iAgree ι s h :=
        Set.ext_iff.mp ih s
      change (∀ c ∈ assignments t ++ [⟨⟨h,a⟩,y⟩], s c.1 = c.2) ↔
        iAgree ι s (h ++ [(a.val,y.val)])
      rw [iAgree_concat, agreesFrom_singleton]
      constructor
      · intro hs
        refine ⟨hp.mp (fun c hc => hs c (List.mem_append_left _ hc)), ?_⟩
        exact hs ⟨⟨h, a⟩, y⟩ (List.mem_append_right _ (List.mem_singleton_self _))
      · rintro ⟨hh, hy⟩ c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hp.mpr hh c hc
        · have he := List.mem_singleton.mp hc
          subst he
          exact hy

theorem residualMeasure_valid {ι : ITree} {h} (t : ValidPath ι h) :
    residualMeasure ι (cylinder ι h) = ENNReal.ofReal (resCyl ι h) := by
  rw [← assignments_cylinder t, product_constraints ι _ (assignments_nodup t)]
  induction t with
  | nil => simp [assignments, resCyl_nil]
  | @snoc h t a y ih =>
      simp only [assignments, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [ih, residualCoordinate_singleton, resCyl_append]
      rw [ENNReal.ofReal_mul (resRatioStep_nonneg ι h (a.val,y.val))]
      exact mul_comm _ _

theorem valid_of_agree (ι : ITree) (s : IStrategy ι) (h : List (ℕ × ℕ))
    (hs : iAgree ι s h) : Nonempty (ValidPath ι h) := by
  revert hs
  induction h using List.reverseRecOn with
  | nil => intro _; exact ⟨.nil⟩
  | append_singleton h p ih =>
      intro hs
      obtain ⟨hh,hp⟩ := (iAgree_concat ι s h p).mp hs
      obtain ⟨t⟩ := ih hh
      obtain ⟨a,ha,hy,_⟩ := hp
      have he : p = (a.val,(s ⟨h,a⟩).val) := Prod.ext ha.symm hy.symm
      subst p
      exact ⟨.snoc t a (s ⟨h,a⟩)⟩

theorem valid_of_path_pos (ι : ITree) (h : List (ℕ × ℕ))
    (hp : 0 < pathMass ι h) : Nonempty (ValidPath ι h) := by
  revert hp
  induction h using List.reverseRecOn with
  | nil => intro _; exact ⟨.nil⟩
  | append_singleton h p ih =>
      intro hp
      have he : pathMass ι (h ++ [p]) = pathMass ι h * kernRaw ι h p.1 p.2 := by
        simpa [pathMass] using pm_append_one ι [] h p.1 p.2
      rw [he] at hp
      have hparent : 0 < pathMass ι h := by
        nlinarith [pathMass_nonneg ι h, kernRaw_nonneg ι h p.1 p.2]
      have hk : 0 < kernRaw ι h p.1 p.2 := by
        nlinarith [pathMass_nonneg ι h, kernRaw_nonneg ι h p.1 p.2]
      obtain ⟨t⟩ := ih hparent
      by_cases ha : p.1 < ι.nA h
      · by_cases hy : p.2 < ι.nY h ⟨p.1,ha⟩
        · exact ⟨.snoc t ⟨p.1,ha⟩ ⟨p.2,hy⟩⟩
        · simp [kernRaw, ha, hy] at hk
      · simp [kernRaw, ha] at hk

def fullMeasure (ι : ITree) : Measure (IStrategy ι) :=
  atomMeasure ι + ENNReal.ofReal (resMass ι []) • residualMeasure ι

theorem fullMeasure_cylinder (ι : ITree) (h : List (ℕ × ℕ)) :
    fullMeasure ι (cylinder ι h) = ENNReal.ofReal (pathMass ι h) := by
  by_cases ht : Nonempty (ValidPath ι h)
  · obtain ⟨t⟩ := ht
    rw [fullMeasure, Measure.add_apply, Measure.smul_apply,
      atomMeasure_cylinder, residualMeasure_valid t]
    change ENNReal.ofReal (cylMass ι h) +
      ENNReal.ofReal (resMass ι []) * ENNReal.ofReal (resCyl ι h) = _
    have hcy : 0 ≤ cylMass ι h := tsum_nonneg (cyl_term_nonneg ι h)
    have hre : 0 ≤ resMass ι [] * resCyl ι h :=
      mul_nonneg (resMass_nonneg ι []) (resCyl_nonneg ι h)
    rw [← ENNReal.ofReal_mul (resMass_nonneg ι []),
      ← ENNReal.ofReal_add hcy hre, exact_split]
  · have hempty : cylinder ι h = ∅ := by
      ext s
      simp only [cylinder, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hs => ht (valid_of_agree ι s h hs)
    have hz : pathMass ι h = 0 := by
      have hn : ¬ 0 < pathMass ι h := fun hp => ht (valid_of_path_pos ι h hp)
      exact le_antisymm (le_of_not_gt hn) (pathMass_nonneg ι h)
    simp [hempty, hz]

instance fullMeasure_probability (ι : ITree) : IsProbabilityMeasure (fullMeasure ι) where
  measure_univ := by
    have hh : cylinder ι [] = Set.univ := by ext s; simp [cylinder, iAgree_nil]
    simpa [hh, pathMass_nil] using fullMeasure_cylinder ι []

theorem fullMeasure_atomic_lower (ι : ITree) :
    ENNReal.ofReal (atomQ ι) ≤ fullMeasure ι (atomicSupport ι) := by
  rw [fullMeasure, Measure.add_apply, atomMeasure_support]
  exact le_add_right le_rfl

theorem exact_infinite_representation (ι : ITree) :
    ∃ μ : Measure (IStrategy ι), IsProbabilityMeasure μ ∧
      (∀ h, μ (cylinder ι h) = ENNReal.ofReal (pathMass ι h)) ∧
      ∃ A : Set (IStrategy ι), A.Countable ∧ ENNReal.ofReal (atomQ ι) ≤ μ A := by
  exact ⟨fullMeasure ι, inferInstance, fullMeasure_cylinder ι,
    atomicSupport ι, atomicSupport_countable ι, fullMeasure_atomic_lower ι⟩

#print axioms atomMeasure_univ
#print axioms atomMeasure_cylinder
#print axioms fullMeasure_cylinder
#print axioms exact_infinite_representation

end Completion
end CausalSpectrum
end
