/-
Zero branches preserve the class of causal seed laws.

A history-dependent controlled tree with nonnegative normalized kernels (`NNTree`) is compared
with its positive-support reduction `T.plus`, an ordinary positive `ITree` whose outputs at a
history are the outputs of positive probability (no renormalization). Reduced histories are
mapped to original ones by `lift`; response strategies are mapped by the restriction `R` and the
extension `E`, with `R ∘ E = id`. Agreement and path masses correspond step by step.
-/
import CausalSeed.SeedRanking
import CausalSeed.Subadditive

noncomputable section
open Classical Finset MeasureTheory
open scoped ENNReal

namespace CausalSpectrum.ZeroBranch

/-- A locally finite, history-dependent controlled tree with nonnegative normalized kernels.
Histories are lists of `(action, output)` index pairs, as for `ITree`. -/
structure NNTree where
  nA : List (ℕ × ℕ) → ℕ
  hA : ∀ h, 0 < nA h
  nY : ∀ h, Fin (nA h) → ℕ
  hY : ∀ h a, 0 < nY h a
  kern : ∀ h, (a : Fin (nA h)) → Fin (nY h a) → ℝ
  knn : ∀ h a y, 0 ≤ kern h a y
  ksum : ∀ h a, ∑ y, kern h a y = 1

namespace NNTree
variable (T : NNTree)

/-! ### Masses and agreement on the original tree -/

def kernRaw (h : List (ℕ × ℕ)) (av yv : ℕ) : ℝ :=
  if ha : av < T.nA h then
    if hy : yv < T.nY h ⟨av, ha⟩ then T.kern h ⟨av, ha⟩ ⟨yv, hy⟩ else 0
  else 0

/-- Probability of a finite history (zero if it is illegal or crosses a zero branch). -/
def pathMass (h : List (ℕ × ℕ)) : ℝ :=
  ∏ k ∈ range h.length, T.kernRaw (h.take k) (h.getD k (0, 0)).1 (h.getD k (0, 0)).2

abbrev NodeIdx := Σ h : List (ℕ × ℕ), Fin (T.nA h)
/-- A total response strategy: an output at every history and action. -/
abbrev Strat := ∀ p : T.NodeIdx, Fin (T.nY p.1 p.2)

def Ok (s : T.Strat) (h : List (ℕ × ℕ)) (p : ℕ × ℕ) : Prop :=
  ∃ ha : p.1 < T.nA h, (s ⟨h, ⟨p.1, ha⟩⟩).val = p.2

/-- `s` reproduces the history `h` when the actions of `h` are played. -/
def Agree (s : T.Strat) (h : List (ℕ × ℕ)) : Prop :=
  ∀ k < h.length, T.Ok s (h.take k) (h.getD k (0, 0))

theorem getD_snoc_lt {h : List (ℕ × ℕ)} {p : ℕ × ℕ} {k : ℕ} (hk : k < h.length) :
    (h ++ [p]).getD k (0, 0) = h.getD k (0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_snoc_eq (h : List (ℕ × ℕ)) (p : ℕ × ℕ) : (h ++ [p]).getD h.length (0, 0) = p := by
  simp [List.getD_eq_getElem?_getD]

theorem take_snoc_le {h : List (ℕ × ℕ)} {p : ℕ × ℕ} {k : ℕ} (hk : k ≤ h.length) :
    (h ++ [p]).take k = h.take k := by
  simp [List.take_append_of_le_length hk]

theorem pathMass_nil : T.pathMass [] = 1 := by simp [pathMass]

theorem pathMass_snoc (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    T.pathMass (h ++ [p]) = T.pathMass h * T.kernRaw h p.1 p.2 := by
  unfold pathMass
  rw [List.length_append, List.length_singleton, prod_range_succ]
  congr 1
  · refine prod_congr rfl fun k hk => ?_
    have hk := mem_range.1 hk
    rw [take_snoc_le (le_of_lt hk), getD_snoc_lt hk]
  · rw [take_snoc_le le_rfl, List.take_length, getD_snoc_eq]

theorem agree_nil (s : T.Strat) : T.Agree s [] := by simp [Agree]

theorem agree_snoc (s : T.Strat) (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    T.Agree s (h ++ [p]) ↔ T.Agree s h ∧ T.Ok s h p := by
  unfold Agree
  rw [List.length_append, List.length_singleton]
  constructor
  · intro H
    refine ⟨fun k hk => ?_, ?_⟩
    · have := H k (by omega)
      rwa [take_snoc_le hk.le, getD_snoc_lt hk] at this
    · have := H h.length (by omega)
      rwa [take_snoc_le le_rfl, List.take_length, getD_snoc_eq] at this
  · rintro ⟨H, hp⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [take_snoc_le hk.le, getD_snoc_lt hk]; exact H k hk
    · rw [take_snoc_le le_rfl, List.take_length, getD_snoc_eq]; exact hp

theorem kernRaw_nonneg (h : List (ℕ × ℕ)) (a y : ℕ) : 0 ≤ T.kernRaw h a y := by
  unfold kernRaw; split_ifs <;> first | exact T.knn _ _ _ | exact le_rfl

theorem pathMass_nonneg (h : List (ℕ × ℕ)) : 0 ≤ T.pathMass h :=
  prod_nonneg fun _ _ => T.kernRaw_nonneg _ _ _

/-! ### Positive support -/

def supp (h : List (ℕ × ℕ)) (a : Fin (T.nA h)) : Finset (Fin (T.nY h a)) :=
  univ.filter fun y => 0 < T.kern h a y

theorem supp_nonempty (h : List (ℕ × ℕ)) (a : Fin (T.nA h)) : (T.supp h a).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have : ∀ y, T.kern h a y = 0 := fun y => by
    have hy : y ∉ T.supp h a := by rw [hne]; simp
    simp only [supp, mem_filter, mem_univ, true_and, not_lt] at hy
    exact le_antisymm hy (T.knn _ _ _)
  have := T.ksum h a
  simp [‹∀ y, T.kern h a y = 0›] at this

theorem card_supp_pos (h : List (ℕ × ℕ)) (a : Fin (T.nA h)) : 0 < (T.supp h a).card :=
  Finset.card_pos.2 (T.supp_nonempty h a)

/-- Increasing enumeration of the positive outputs. -/
def emb (h : List (ℕ × ℕ)) (a : Fin (T.nA h)) : Fin (T.supp h a).card ≃o T.supp h a :=
  (T.supp h a).orderIsoOfFin rfl

theorem kern_emb_pos (h : List (ℕ × ℕ)) (a : Fin (T.nA h)) (i : Fin (T.supp h a).card) :
    0 < T.kern h a (T.emb h a i).1 := by
  have := (T.emb h a i).2
  simp only [supp, mem_filter, mem_univ, true_and] at this
  exact this

theorem sum_emb (h : List (ℕ × ℕ)) (a : Fin (T.nA h)) :
    ∑ i, T.kern h a (T.emb h a i).1 = 1 := by
  rw [← T.ksum h a]
  rw [← sum_filter_add_sum_filter_not univ (fun y => 0 < T.kern h a y)]
  have h0 : ∑ y ∈ univ.filter (fun y => ¬ 0 < T.kern h a y), T.kern h a y = 0 :=
    sum_eq_zero fun y hy => by
      simp only [mem_filter, mem_univ, true_and, not_lt] at hy
      exact le_antisymm hy (T.knn _ _ _)
  rw [h0, add_zero]
  rw [← Finset.sum_coe_sort (univ.filter fun y => 0 < T.kern h a y)]
  exact (Equiv.sum_comp (T.emb h a).toEquiv (fun y : T.supp h a => T.kern h a y.1))

/-! ### The reduced history map -/

/-- Output index of the original tree reached by reduced index `i`; illegal reduced indices
are sent injectively to illegal original indices. -/
def stepY (h : List (ℕ × ℕ)) (a i : ℕ) : ℕ :=
  if ha : a < T.nA h then
    if hi : i < (T.supp h ⟨a, ha⟩).card then (T.emb h ⟨a, ha⟩ ⟨i, hi⟩).1.val
    else T.nY h ⟨a, ha⟩ + i
  else i

def step (h : List (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ × ℕ := (p.1, T.stepY h p.1 p.2)

/-- The inclusion `j` of reduced histories into original histories. -/
def lift (h : List (ℕ × ℕ)) : List (ℕ × ℕ) := h.foldl (fun acc p => acc ++ [T.step acc p]) []

@[simp] theorem lift_nil : T.lift [] = [] := rfl

theorem lift_snoc (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    T.lift (h ++ [p]) = T.lift h ++ [T.step (T.lift h) p] := by
  simp [lift, List.foldl_append]

theorem length_lift (h : List (ℕ × ℕ)) : (T.lift h).length = h.length := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h p ih => simp [lift_snoc, ih]

theorem stepY_inj {h : List (ℕ × ℕ)} {a i i' : ℕ} (e : T.stepY h a i = T.stepY h a i') : i = i' := by
  unfold stepY at e
  split_ifs at e with ha hi hi' hi'
  · have := (T.emb h ⟨a, ha⟩).injective (Subtype.ext (Fin.ext e))
    exact congrArg Fin.val this
  · have := (T.emb h ⟨a, ha⟩ ⟨i, hi⟩).1.isLt; omega
  · have := (T.emb h ⟨a, ha⟩ ⟨i', hi'⟩).1.isLt; omega
  · omega
  · exact e

theorem step_inj {h : List (ℕ × ℕ)} {p p' : ℕ × ℕ} (e : T.step h p = T.step h p') : p = p' := by
  simp only [step, Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  obtain ⟨a, i⟩ := p; obtain ⟨a', i'⟩ := p'
  simp only at e1 e2; subst e1
  rw [T.stepY_inj e2]

theorem lift_injective : Function.Injective T.lift := by
  intro h
  induction h using List.reverseRecOn with
  | nil =>
      intro h' e
      have := congrArg List.length e
      rw [length_lift, length_lift] at this
      exact (List.length_eq_zero_iff.1 this.symm).symm
  | append_singleton h p ih =>
      intro h' e
      rcases List.eq_nil_or_concat h' with rfl | ⟨h'', p', rfl⟩
      · have := congrArg List.length e
        simp [length_lift] at this
      · rw [List.concat_eq_append] at e ⊢
        rw [lift_snoc, lift_snoc] at e
        obtain ⟨e1, e2⟩ := List.append_inj' e rfl
        have e1' := ih e1
        subst e1'
        simp only [List.cons.injEq, and_true] at e2
        rw [T.step_inj e2]

/-! ### The positive tree `T⁺` -/

/-- The positive-support reduction: same actions, outputs restricted to the support,
transition probabilities unchanged. -/
def plus : ITree where
  nA h := T.nA (T.lift h)
  hA h := T.hA _
  nY h a := (T.supp (T.lift h) a).card
  hY h a := T.card_supp_pos _ a
  kern h a i := T.kern (T.lift h) a (T.emb (T.lift h) a i).1
  kpos h a i := T.kern_emb_pos _ a i
  ksum h a := T.sum_emb _ a

theorem kernRaw_of_lt {h : List (ℕ × ℕ)} {a y : ℕ} (ha : a < T.nA h) (hy : y < T.nY h ⟨a, ha⟩) :
    T.kernRaw h a y = T.kern h ⟨a, ha⟩ ⟨y, hy⟩ := by
  simp [kernRaw, ha, hy]

theorem kernRaw_plus (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    CausalSpectrum.kernRaw T.plus h p.1 p.2 =
      T.kernRaw (T.lift h) (T.step (T.lift h) p).1 (T.step (T.lift h) p).2 := by
  obtain ⟨a, i⟩ := p
  by_cases ha : a < T.nA (T.lift h)
  · have ha' : a < T.plus.nA h := ha
    by_cases hi : i < (T.supp (T.lift h) ⟨a, ha⟩).card
    · have hi' : i < T.plus.nY h ⟨a, ha'⟩ := hi
      have e2 : T.step (T.lift h) (a, i) =
          (a, (T.emb (T.lift h) ⟨a, ha⟩ ⟨i, hi⟩).1.val) := by simp [step, stepY, ha, hi]
      rw [e2, T.kernRaw_of_lt ha (T.emb (T.lift h) ⟨a, ha⟩ ⟨i, hi⟩).1.isLt]
      simp [CausalSpectrum.kernRaw, ha', hi']
      rfl
    · have hi' : ¬ i < T.plus.nY h ⟨a, ha'⟩ := hi
      have e2 : T.step (T.lift h) (a, i) = (a, T.nY (T.lift h) ⟨a, ha⟩ + i) := by
        simp [step, stepY, ha, hi]
      rw [e2]
      simp [CausalSpectrum.kernRaw, kernRaw, ha', hi', ha]
  · have ha' : ¬ a < T.plus.nA h := ha
    have e2 : T.step (T.lift h) (a, i) = (a, i) := by simp [step, stepY, ha]
    rw [e2]
    simp [CausalSpectrum.kernRaw, kernRaw, ha', ha]

theorem pathMass_plus (h : List (ℕ × ℕ)) :
    CausalSpectrum.pathMass T.plus h = T.pathMass (T.lift h) := by
  induction h using List.reverseRecOn with
  | nil => simp [CausalSpectrum.pathMass, pm, pathMass]
  | append_singleton h p ih =>
      obtain ⟨a, i⟩ := p
      rw [CausalSpectrum.pathMass, pm_append_one, ← CausalSpectrum.pathMass, ih, lift_snoc,
        pathMass_snoc, List.nil_append]
      exact congrArg _ (T.kernRaw_plus h (a, i))

/-- Every history of positive mass is the image of a reduced history. -/
theorem exists_lift_of_pathMass_ne {h : List (ℕ × ℕ)} (hm : T.pathMass h ≠ 0) :
    ∃ h', T.lift h' = h := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨[], rfl⟩
  | append_singleton h p ih =>
      rw [pathMass_snoc] at hm
      obtain ⟨h', rfl⟩ := ih (left_ne_zero_of_mul hm)
      have hk := right_ne_zero_of_mul hm
      obtain ⟨a, y⟩ := p
      unfold kernRaw at hk
      split_ifs at hk with ha hy
      all_goals try exact absurd rfl hk
      have hpos : 0 < T.kern (T.lift h') ⟨a, ha⟩ ⟨y, hy⟩ :=
        lt_of_le_of_ne (T.knn _ _ _) (Ne.symm hk)
      have hmem : (⟨y, hy⟩ : Fin _) ∈ T.supp (T.lift h') ⟨a, ha⟩ := by simp [supp, hpos]
      set i := (T.emb (T.lift h') ⟨a, ha⟩).symm ⟨_, hmem⟩
      refine ⟨h' ++ [(a, i.val)], ?_⟩
      rw [lift_snoc]
      congr
      simp only [step, stepY, dif_pos ha, dif_pos i.isLt, Prod.mk.injEq, true_and]
      have : (T.emb (T.lift h') ⟨a, ha⟩ ⟨i.val, i.isLt⟩) = ⟨_, hmem⟩ :=
        (T.emb (T.lift h') ⟨a, ha⟩).apply_symm_apply _
      rw [this]

/-! ### Restriction `R` and extension `E` of strategies -/

/-- Reduced index of an original output (a fixed positive default off the support). -/
def rIdx (h : List (ℕ × ℕ)) (a : Fin (T.nA h)) (y : Fin (T.nY h a)) : Fin (T.supp h a).card :=
  if hy : y ∈ T.supp h a then (T.emb h a).symm ⟨y, hy⟩ else ⟨0, T.card_supp_pos h a⟩

theorem rIdx_emb (h : List (ℕ × ℕ)) (a : Fin (T.nA h)) (i : Fin (T.supp h a).card) :
    T.rIdx h a (T.emb h a i).1 = i := by
  simp [rIdx, (T.emb h a i).2]

/-- The restriction `R`: read the original strategy on lifted histories. -/
def R (s : T.Strat) : IStrategy T.plus := fun p => T.rIdx (T.lift p.1) p.2 (s ⟨T.lift p.1, p.2⟩)

def Eat (s : IStrategy T.plus) (h' : List (ℕ × ℕ)) (a : Fin (T.nA (T.lift h'))) :
    Fin (T.nY (T.lift h') a) :=
  (T.emb (T.lift h') a (s ⟨h', a⟩)).1

/-- The extension `E`: positive histories use the reduced strategy, every other history a
fixed positive default output. -/
def E (s : IStrategy T.plus) : T.Strat := fun p =>
  if hp : ∃ h', T.lift h' = p.1 then
    (hp.choose_spec ▸ (fun a => T.Eat s hp.choose a) :
      ∀ a : Fin (T.nA p.1), Fin (T.nY p.1 a)) p.2
  else (T.emb p.1 p.2 ⟨0, T.card_supp_pos _ _⟩).1

theorem cast_Eat (s : IStrategy T.plus) {c h' : List (ℕ × ℕ)} (hc : c = h')
    (e : T.lift c = T.lift h') (a : Fin (T.nA (T.lift h'))) :
    (e ▸ (fun a => T.Eat s c a) : ∀ a : Fin (T.nA (T.lift h')), Fin (T.nY (T.lift h') a)) a =
      T.Eat s h' a := by
  subst hc; rfl

theorem E_lift (s : IStrategy T.plus) (h' : List (ℕ × ℕ)) (a : Fin (T.nA (T.lift h'))) :
    T.E s ⟨T.lift h', a⟩ = T.Eat s h' a := by
  have hp : ∃ c, T.lift c = T.lift h' := ⟨h', rfl⟩
  simp only [E, dif_pos hp]
  exact T.cast_Eat s (T.lift_injective hp.choose_spec) hp.choose_spec a

/-- **`R ∘ E = id`.** -/
theorem R_E (s : IStrategy T.plus) : T.R (T.E s) = s := by
  funext p
  obtain ⟨h', a⟩ := p
  show T.rIdx _ a (T.E s ⟨T.lift h', a⟩) = _
  rw [T.E_lift s h' a]
  exact T.rIdx_emb _ _ _

theorem E_injective : Function.Injective T.E :=
  Function.LeftInverse.injective (g := T.R) T.R_E

/-! ### Agreement correspondences -/

def OkP (s : IStrategy T.plus) (h : List (ℕ × ℕ)) (p : ℕ × ℕ) : Prop :=
  ∃ ha : p.1 < T.plus.nA h, (s ⟨h, ⟨p.1, ha⟩⟩).val = p.2

theorem iAgree_snoc (s : IStrategy T.plus) (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    iAgree T.plus s (h ++ [p]) ↔ iAgree T.plus s h ∧ T.OkP s h p := by
  rw [iAgree_concat]
  apply and_congr_right'
  obtain ⟨p1, p2⟩ := p
  simp only [agreesFrom, OkP, and_true]
  constructor
  · rintro ⟨⟨a, ha⟩, e, hy⟩
    simp only at e
    subst e
    exact ⟨ha, hy⟩
  · rintro ⟨ha, hy⟩; exact ⟨⟨p1, ha⟩, rfl, hy⟩

theorem stepY_lt {h : List (ℕ × ℕ)} {a i : ℕ} (ha : a < T.nA h)
    (hi : i < (T.supp h ⟨a, ha⟩).card) :
    T.stepY h a i = (T.emb h ⟨a, ha⟩ ⟨i, hi⟩).1.val := by
  simp [stepY, ha, hi]

theorem stepY_ge {h : List (ℕ × ℕ)} {a i : ℕ} (ha : a < T.nA h)
    (hi : ¬ i < (T.supp h ⟨a, ha⟩).card) : T.stepY h a i = T.nY h ⟨a, ha⟩ + i := by
  simp [stepY, ha, hi]

theorem ok_E (s : IStrategy T.plus) (h' : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    T.Ok (T.E s) (T.lift h') (T.step (T.lift h') p) ↔ T.OkP s h' p := by
  obtain ⟨a, i⟩ := p
  show (∃ ha : a < T.nA (T.lift h'), (T.E s ⟨T.lift h', ⟨a, ha⟩⟩).val = T.stepY (T.lift h') a i) ↔
    ∃ ha : a < T.nA (T.lift h'), (s ⟨h', ⟨a, ha⟩⟩).val = i
  constructor
  · rintro ⟨ha, hv⟩
    rw [E_lift] at hv
    unfold Eat at hv
    by_cases hi : i < (T.supp (T.lift h') ⟨a, ha⟩).card
    · rw [T.stepY_lt ha hi] at hv
      exact ⟨ha, congrArg Fin.val ((T.emb _ ⟨a, ha⟩).injective (Subtype.ext (Fin.ext hv)))⟩
    · rw [T.stepY_ge ha hi] at hv
      have : (T.emb (T.lift h') ⟨a, ha⟩ (s ⟨h', ⟨a, ha⟩⟩)).1.val < T.nY (T.lift h') ⟨a, ha⟩ :=
        (T.emb (T.lift h') ⟨a, ha⟩ (s ⟨h', ⟨a, ha⟩⟩)).1.isLt
      dsimp only at hv
      omega
  · rintro ⟨ha, hv⟩
    refine ⟨ha, ?_⟩
    have hi : i < (T.supp (T.lift h') ⟨a, ha⟩).card := hv ▸ (s ⟨h', ⟨a, ha⟩⟩).isLt
    rw [E_lift, T.stepY_lt ha hi]
    unfold Eat
    congr 3
    exact Fin.ext hv

theorem ok_E_image (s : IStrategy T.plus) (h' : List (ℕ × ℕ)) (p : ℕ × ℕ)
    (hp : T.Ok (T.E s) (T.lift h') p) : ∃ p', p = T.step (T.lift h') p' := by
  obtain ⟨a, y⟩ := p
  obtain ⟨ha, hv⟩ := hp
  simp only at ha hv
  refine ⟨(a, (s ⟨h', ⟨a, ha⟩⟩).val), ?_⟩
  show (a, y) = (a, T.stepY (T.lift h') a (s ⟨h', ⟨a, ha⟩⟩).val)
  rw [T.stepY_lt ha (s ⟨h', ⟨a, ha⟩⟩).isLt, ← hv, E_lift]
  rfl

/-- `E s` reproduces `lift h'` iff `s` reproduces `h'`. -/
theorem agree_E_lift (s : IStrategy T.plus) (h' : List (ℕ × ℕ)) :
    T.Agree (T.E s) (T.lift h') ↔ iAgree T.plus s h' := by
  induction h' using List.reverseRecOn with
  | nil => simp [agree_nil, iAgree_nil]
  | append_singleton h p ih => rw [lift_snoc, agree_snoc, iAgree_snoc, ih, ok_E]

/-- A history reproduced by an extended strategy is a lifted reduced history. -/
theorem exists_lift_of_agree_E (s : IStrategy T.plus) {h : List (ℕ × ℕ)}
    (hA : T.Agree (T.E s) h) : ∃ h', T.lift h' = h := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨[], rfl⟩
  | append_singleton h p ih =>
      rw [agree_snoc] at hA
      obtain ⟨h', rfl⟩ := ih hA.1
      obtain ⟨p', rfl⟩ := T.ok_E_image s h' p hA.2
      exact ⟨h' ++ [p'], T.lift_snoc h' p'⟩

theorem ok_R (s : T.Strat) (h' : List (ℕ × ℕ)) (p : ℕ × ℕ)
    (hp : T.Ok s (T.lift h') (T.step (T.lift h') p)) : T.OkP (T.R s) h' p := by
  obtain ⟨a, i⟩ := p
  obtain ⟨ha, hv⟩ := hp
  change a < T.nA (T.lift h') at ha
  change (s ⟨T.lift h', ⟨a, ha⟩⟩).val = T.stepY (T.lift h') a i at hv
  refine ⟨ha, ?_⟩
  by_cases hi : i < (T.supp (T.lift h') ⟨a, ha⟩).card
  · rw [T.stepY_lt ha hi] at hv
    show (T.rIdx (T.lift h') ⟨a, ha⟩ (s ⟨T.lift h', ⟨a, ha⟩⟩)).val = i
    have : s ⟨T.lift h', ⟨a, ha⟩⟩ = (T.emb (T.lift h') ⟨a, ha⟩ ⟨i, hi⟩).1 := Fin.ext hv
    rw [this, rIdx_emb]
  · rw [T.stepY_ge ha hi] at hv
    have : (s ⟨T.lift h', ⟨a, ha⟩⟩).val < T.nY (T.lift h') ⟨a, ha⟩ := (s ⟨T.lift h', ⟨a, ha⟩⟩).isLt
    omega

theorem ok_R_back (s : T.Strat) (h' : List (ℕ × ℕ)) (p : ℕ × ℕ) (hp : T.OkP (T.R s) h' p) :
    T.Ok s (T.lift h') (T.step (T.lift h') p) ∨
      ∃ q : ℕ × ℕ, T.Ok s (T.lift h') q ∧ T.kernRaw (T.lift h') q.1 q.2 = 0 := by
  obtain ⟨a, i⟩ := p
  obtain ⟨ha, hv⟩ := hp
  change a < T.nA (T.lift h') at ha
  set y := s ⟨T.lift h', ⟨a, ha⟩⟩
  by_cases hy : y ∈ T.supp (T.lift h') ⟨a, ha⟩
  · left
    have hv' : (T.rIdx (T.lift h') ⟨a, ha⟩ y).val = i := hv
    have hi : i < (T.supp (T.lift h') ⟨a, ha⟩).card := hv' ▸ (T.rIdx _ _ y).isLt
    refine ⟨ha, ?_⟩
    show y.val = T.stepY (T.lift h') a i
    rw [T.stepY_lt ha hi]
    have : T.rIdx (T.lift h') ⟨a, ha⟩ y = ⟨i, hi⟩ := Fin.ext hv'
    simp only [rIdx, dif_pos hy] at this
    rw [← this, OrderIso.apply_symm_apply]
  · right
    refine ⟨(a, y.val), ⟨ha, rfl⟩, ?_⟩
    rw [T.kernRaw_of_lt ha y.isLt]
    simp only [supp, mem_filter, mem_univ, true_and, not_lt] at hy
    exact le_antisymm hy (T.knn _ _ _)

theorem agree_R (s : T.Strat) (h' : List (ℕ × ℕ)) (hA : T.Agree s (T.lift h')) :
    iAgree T.plus (T.R s) h' := by
  induction h' using List.reverseRecOn with
  | nil => exact iAgree_nil _ _
  | append_singleton h p ih =>
      rw [lift_snoc, agree_snoc] at hA
      rw [iAgree_snoc]
      exact ⟨ih hA.1, T.ok_R s h p hA.2⟩

/-- If `R s` reproduces `h'` but `s` does not reproduce `lift h'`, then `s` reproduces a
history of zero mass that is no longer than `h'`. -/
theorem agree_R_back (s : T.Strat) (h' : List (ℕ × ℕ)) (hA : iAgree T.plus (T.R s) h') :
    T.Agree s (T.lift h') ∨
      ∃ g : List (ℕ × ℕ), g.length ≤ h'.length ∧ T.pathMass g = 0 ∧ T.Agree s g := by
  induction h' using List.reverseRecOn with
  | nil => left; exact T.agree_nil s
  | append_singleton h p ih =>
      rw [iAgree_snoc] at hA
      rcases ih hA.1 with hl | ⟨g, hg, h0, hg'⟩
      · rcases T.ok_R_back s h p hA.2 with hok | ⟨q, hq, hk⟩
        · left; rw [lift_snoc, agree_snoc]; exact ⟨hl, hok⟩
        · right
          refine ⟨T.lift h ++ [q], by simp [length_lift], ?_, ?_⟩
          · rw [pathMass_snoc, hk, mul_zero]
          · rw [agree_snoc]; exact ⟨hl, hq⟩
      · right
        exact ⟨g, by simp; omega, h0, hg'⟩

end NNTree
end CausalSpectrum.ZeroBranch
