/-
Exactness and entropy of the interleaved decoder.
-/
import CausalSeed.GapBlocks

noncomputable section
open Classical Finset
open scoped ENNReal

namespace CausalSpectrum.Kernel
open Completion Gap

variable {κ : Kernel} (j₀ : Fin κ.nA) (h2 : 2 ≤ κ.nA)

/-- A plan: blocks of the product sample and windows of the subfamily history, with the
anti-diagonal condition. -/
structure Plan (n r : ℕ) where
  X : Blocks n r
  B : Blocks n r
  sep : ∀ j, n ≤ X.O j + B.O j + 1

/-- One pair: a joint law of a product block of length `p` and a subfamily seed exact to
horizon `q`. -/
structure Comp (p q : ℕ) where
  Ω : Type
  [fin : Fintype Ω]
  w : Ω → ℝ
  xp : Ω → Fin p → Fin (κ.nY j₀)
  bs : Ω → IStrategy (subK j₀ h2).toITree
  nonneg : ∀ o, 0 ≤ w o
  total : ∑ o, w o = 1
  mX : ∀ E : (Fin p → Fin (κ.nY j₀)) → Prop,
    ∑ o, w o * (if E (xp o) then 1 else 0) = ∑ x, prodW (κ.K j₀) x * (if E x then 1 else 0)
  mB : ∀ L : List (ℕ × ℕ), L.length ≤ q →
    ∑ o, w o * indAgree (subK j₀ h2).toITree (bs o) L = pathMass (subK j₀ h2).toITree L

attribute [instance] Comp.fin

variable {j₀ h2} {n r : ℕ} (P : Plan n r) (C : ∀ j : Fin r, Comp j₀ h2 (P.X.s j) (P.B.s j))

/-- The global sample space. -/
abbrev Gl := ∀ j, (C j).Ω

def Xdec (ω : Gl P C) (c : ℕ) : Fin (κ.nY j₀) :=
  if h : ∃ j, P.X.O j ≤ c ∧ c < P.X.O j + P.X.s j then
    (C h.choose).xp (ω h.choose) ⟨c - P.X.O h.choose, by have := h.choose_spec; omega⟩
  else ⟨0, κ.hY j₀⟩

def Bdec (ω : Gl P C) (L : List (ℕ × ℕ)) (b : Fin (subK j₀ h2).nA) : Fin ((subK j₀ h2).nY b) :=
  if h : ∃ j, P.B.O j ≤ L.length ∧ L.length < P.B.O j + P.B.s j then
    (C h.choose).bs (ω h.choose) ⟨L.drop (P.B.O h.choose), b⟩
  else ⟨0, (subK j₀ h2).hY b⟩

theorem nY_sub (a : Fin κ.nA) (ha : a ≠ j₀) :
    (subK j₀ h2).nY ⟨subN j₀ a.val, subN_lt j₀ a.isLt (fun h => ha (Fin.ext h))⟩ = κ.nY a := by
  exact congrArg κ.nY (emb_subN j₀ a.isLt (fun h => ha (Fin.ext h)))

/-- The global strategy. -/
def strat (ω : Gl P C) : IStrategy κ.toITree := fun x =>
  if ha : x.2 = j₀ then Fin.cast (by rw [ha]; rfl) (Xdec P C ω (Zl j₀ x.1).length)
  else Fin.cast (by rw [nY_sub x.2 ha]; rfl)
    (Bdec P C ω (Sl j₀ x.1) ⟨subN j₀ x.2.val, subN_lt j₀ x.2.isLt (fun h => ha (Fin.ext h))⟩)

theorem strat_j0 (ω : Gl P C) (pref : List (ℕ × ℕ)) (a1 : ℕ) (ha : a1 < κ.nA)
    (he : a1 = j₀.val) :
    (strat P C ω ⟨pref, (⟨a1, ha⟩ : Fin (κ.toITree.nA pref))⟩).val =
      (Xdec P C ω (Zl j₀ pref).length).val := by
  have e : (⟨a1, ha⟩ : Fin κ.nA) = j₀ := Fin.ext he
  unfold strat
  split
  · rfl
  · exact absurd e ‹_›

theorem strat_ne (ω : Gl P C) (pref : List (ℕ × ℕ)) (a1 : ℕ) (ha : a1 < κ.nA)
    (hne : a1 ≠ j₀.val) :
    (strat P C ω ⟨pref, (⟨a1, ha⟩ : Fin (κ.toITree.nA pref))⟩).val =
      (Bdec P C ω (Sl j₀ pref) ⟨subN j₀ a1, subN_lt j₀ ha hne⟩).val := by
  have e : (⟨a1, ha⟩ : Fin κ.nA) ≠ j₀ := fun h => hne (congrArg Fin.val h)
  unfold strat
  split
  · exact absurd ‹_› e
  · rfl

/-- The subfamily decoder reproduces output `z` of action `b` after history `L`. -/
def BOk (ω : Gl P C) (L : List (ℕ × ℕ)) (b z : ℕ) : Prop :=
  ∃ hb : b < (subK j₀ h2).nA, (Bdec P C ω L ⟨b, hb⟩).val = z

def XAg (ω : Gl P C) (Z : List ℕ) : Prop :=
  ∀ c < Z.length, (Xdec P C ω c).val = Z.getD c 0

def BAg (ω : Gl P C) (S : List (ℕ × ℕ)) : Prop :=
  ∀ c < S.length, BOk P C ω (S.take c) (S.getD c (0, 0)).1 (S.getD c (0, 0)).2

theorem XAg_snoc (ω : Gl P C) (Z : List ℕ) (z : ℕ) :
    XAg P C ω (Z ++ [z]) ↔ XAg P C ω Z ∧ (Xdec P C ω Z.length).val = z := by
  unfold XAg
  constructor
  · intro h
    refine ⟨fun c hc => ?_, ?_⟩
    · rw [h c (by simp; omega), List.getD_append _ _ _ _ hc]
    · rw [h _ (by simp)]; simp
  · rintro ⟨h, hz⟩ c hc
    simp only [List.length_append, List.length_singleton] at hc
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
    · rw [h c hc, List.getD_append _ _ _ _ hc]
    · subst hc; rw [hz]; simp

theorem BAg_snoc (ω : Gl P C) (S : List (ℕ × ℕ)) (f : ℕ × ℕ) :
    BAg P C ω (S ++ [f]) ↔ BAg P C ω S ∧ BOk P C ω S f.1 f.2 := by
  unfold BAg
  constructor
  · intro h
    refine ⟨fun c hc => ?_, ?_⟩
    · have := h c (by simp; omega)
      rwa [List.getD_append _ _ _ _ hc, List.take_append_of_le_length hc.le] at this
    · have := h S.length (by simp)
      simpa using this
  · rintro ⟨h, hf⟩ c hc
    simp only [List.length_append, List.length_singleton] at hc
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
    · rw [List.getD_append _ _ _ _ hc, List.take_append_of_le_length hc.le]; exact h c hc
    · subst hc; simpa using hf

theorem agree_decomp (ω : Gl P C) (h : List (ℕ × ℕ)) :
    iAgree κ.toITree (strat P C ω) h ↔ XAg P C ω (Zl j₀ h) ∧ BAg P C ω (Sl j₀ h) := by
  induction h using List.reverseRecOn with
  | nil => simp [iAgree_nil, XAg, BAg, Zl, Sl]
  | append_singleton h e ih =>
    obtain ⟨a1, z1⟩ := e
    rw [κ.iAgree_snoc, ih, Zl_snoc, Sl_snoc]
    by_cases he : a1 = j₀.val
    · subst he
      simp only [if_true, XAg_snoc]
      constructor
      · rintro ⟨⟨h1, h2'⟩, ha, hv⟩
        refine ⟨⟨h1, ?_⟩, h2'⟩
        rwa [strat_j0 P C ω h _ ha rfl] at hv
      · rintro ⟨⟨h1, hv⟩, h2'⟩
        refine ⟨⟨h1, h2'⟩, j₀.isLt, ?_⟩
        rwa [strat_j0 P C ω h _ _ rfl]
    · simp only [he, if_false, BAg_snoc]
      by_cases ha : a1 < κ.nA
      · constructor
        · rintro ⟨⟨h1, h2'⟩, ha', hv⟩
          refine ⟨h1, h2', subN_lt j₀ ha he, ?_⟩
          rwa [strat_ne P C ω h a1 ha' he] at hv
        · rintro ⟨h1, h2', hb, hv⟩
          refine ⟨⟨h1, h2'⟩, ha, ?_⟩
          rw [strat_ne P C ω h a1 ha he]; exact hv
      · constructor
        · rintro ⟨-, ha', -⟩; exact absurd ha' ha
        · rintro ⟨-, -, hb, -⟩; exact absurd hb (subN_ge j₀ ha)

/-! ### Blockwise form of the agreement -/

theorem xp_congr (ω : Gl P C) {j j' : Fin r} (e : j' = j) {t t' : ℕ} (ht : t < P.X.s j)
    (ht' : t' < P.X.s j') (he : t' = t) :
    ((C j').xp (ω j') ⟨t', ht'⟩).val = ((C j).xp (ω j) ⟨t, ht⟩).val := by
  subst e; subst he; rfl

theorem bs_congr (ω : Gl P C) {j j' : Fin r} (e : j' = j) (L : List (ℕ × ℕ))
    (b : Fin (subK j₀ h2).nA) :
    ((C j').bs (ω j') ⟨L.drop (P.B.O j'), b⟩).val = ((C j).bs (ω j) ⟨L.drop (P.B.O j), b⟩).val := by
  subst e; rfl

theorem Xdec_block (ω : Gl P C) (j : Fin r) (t : ℕ) (ht : t < P.X.s j) :
    (Xdec P C ω (P.X.O j + t)).val = ((C j).xp (ω j) ⟨t, ht⟩).val := by
  have hex : ∃ j', P.X.O j' ≤ P.X.O j + t ∧ P.X.O j + t < P.X.O j' + P.X.s j' :=
    ⟨j, by omega, by omega⟩
  have hj : hex.choose = j :=
    P.X.uniq _ _ _ hex.choose_spec.1 hex.choose_spec.2 (by omega) (by omega)
  unfold Xdec
  rw [dif_pos hex]
  exact xp_congr P C ω hj ht _ (by rw [hj]; omega)

theorem Bdec_block (ω : Gl P C) (j : Fin r) (L : List (ℕ × ℕ)) (h1 : P.B.O j ≤ L.length)
    (h3 : L.length < P.B.O j + P.B.s j) (b : Fin (subK j₀ h2).nA) :
    (Bdec P C ω L b).val = ((C j).bs (ω j) ⟨L.drop (P.B.O j), b⟩).val := by
  have hex : ∃ j', P.B.O j' ≤ L.length ∧ L.length < P.B.O j' + P.B.s j' := ⟨j, h1, h3⟩
  have hj : hex.choose = j :=
    P.B.uniq _ _ _ hex.choose_spec.1 hex.choose_spec.2 h1 h3
  unfold Bdec
  refine Eq.trans ?_ (bs_congr P C ω hj L b)
  exact congrArg Fin.val (dif_pos hex)

def XAj (j : Fin r) (o : (C j).Ω) (Z : List ℕ) : Prop :=
  ∀ t (ht : t < P.X.s j), P.X.O j + t < Z.length →
    ((C j).xp o ⟨t, ht⟩).val = Z.getD (P.X.O j + t) 0

theorem XAg_iff (ω : Gl P C) (Z : List ℕ) (hZ : Z.length ≤ n) :
    XAg P C ω Z ↔ ∀ j, XAj P C j (ω j) Z := by
  constructor
  · intro h j t ht hc
    rw [← Xdec_block P C ω j t ht]; exact h _ hc
  · intro h c hc
    obtain ⟨j, h1, h3⟩ := P.X.cover c (lt_of_lt_of_le hc hZ)
    have e : P.X.O j + (c - P.X.O j) = c := by omega
    have := h j (c - P.X.O j) (by omega) (by rw [e]; exact hc)
    rw [e] at this
    rw [← e, Xdec_block P C ω j _ (by omega), e]; exact this

/-- Generic one-step agreement. -/
def Ok (ν : Kernel) (s : IStrategy ν.toITree) (L : List (ℕ × ℕ)) (x : ℕ × ℕ) : Prop :=
  ∃ ha : x.1 < ν.nA, (s ⟨L, ⟨x.1, ha⟩⟩).val = x.2

theorem iAgree_getD (ν : Kernel) (s : IStrategy ν.toITree) (t : List (ℕ × ℕ)) :
    iAgree ν.toITree s t ↔ ∀ k < t.length, Ok ν s (t.take k) (t.getD k (0, 0)) := by
  rw [ν.iAgree_iff_forall]
  constructor
  · intro h k hk; rw [List.getD_eq_getElem _ _ hk]; exact h k hk
  · intro h k hk; have := h k hk; rw [List.getD_eq_getElem _ _ hk] at this; exact this

theorem win_take {α : Type*} (O q : ℕ) (L : List α) {k} (hk : k ≤ q) :
    (win O q L).take k = (L.take (O + k)).drop O := by
  simp only [win, List.take_take, min_eq_left hk, List.drop_take]
  congr 1; omega

def BAj (j : Fin r) (o : (C j).Ω) (S : List (ℕ × ℕ)) : Prop :=
  iAgree (subK j₀ h2).toITree ((C j).bs o) (win (P.B.O j) (P.B.s j) S)

theorem BOk_block (ω : Gl P C) (j : Fin r) (S : List (ℕ × ℕ)) {c} (hc : c ≤ S.length)
    (h1 : P.B.O j ≤ c) (h3 : c < P.B.O j + P.B.s j) (x : ℕ × ℕ) :
    BOk P C ω (S.take c) x.1 x.2 ↔ Ok (subK j₀ h2) ((C j).bs (ω j)) ((S.take c).drop (P.B.O j)) x := by
  have hl : (S.take c).length = c := by simp [hc]
  unfold BOk Ok
  have h1' : P.B.O j ≤ (S.take c).length := by rw [hl]; exact h1
  have h3' : (S.take c).length < P.B.O j + P.B.s j := by rw [hl]; exact h3
  · constructor
    · rintro ⟨hb, hv⟩
      exact ⟨hb, (Bdec_block P C ω j _ h1' h3' ⟨x.1, hb⟩).symm.trans hv⟩
    · rintro ⟨hb, hv⟩
      exact ⟨hb, (Bdec_block P C ω j _ h1' h3' ⟨x.1, hb⟩).trans hv⟩

theorem BAg_iff (ω : Gl P C) (S : List (ℕ × ℕ)) (hS : S.length ≤ n) :
    BAg P C ω S ↔ ∀ j, BAj P C j (ω j) S := by
  constructor
  · intro h j
    unfold BAj
    rw [iAgree_getD]
    intro k hk
    rw [length_win, lt_min_iff] at hk
    have hc : P.B.O j + k < S.length := by omega
    have := h _ hc
    rw [BOk_block P C ω j S hc.le (by omega) (by omega)] at this
    rw [win_getD _ _ _ _ hk.1, win_take _ _ _ hk.1.le]
    exact this
  · intro h c hc
    obtain ⟨j, h1, h3⟩ := P.B.cover c (lt_of_lt_of_le hc hS)
    have e : P.B.O j + (c - P.B.O j) = c := by omega
    have := (iAgree_getD _ _ _).1 (h j) (c - P.B.O j) (by
      rw [length_win, lt_min_iff]; omega)
    rw [win_getD _ _ _ _ (by omega), win_take _ _ _ (by omega), e] at this
    rw [BOk_block P C ω j S hc.le h1 h3]
    exact this

/-! ### The product weight lemma and exactness -/

theorem prod_range_ite {M : Type*} [CommMonoid M] (f : ℕ → M) {m n : ℕ} (h : m ≤ n) :
    ∏ c ∈ range n, (if c < m then f c else 1) = ∏ c ∈ range m, f c := by
  rw [prod_ite, prod_const_one, mul_one]
  congr 1; ext c; simp only [mem_filter, mem_range]; omega

theorem sum_K_ite (z : ℕ) :
    ∑ y, κ.K j₀ y * (if y.val = z then 1 else 0) = kz j₀ z := by
  unfold kz
  split_ifs with hz
  · rw [Finset.sum_eq_single ⟨z, hz⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
    · simp
  · exact sum_eq_zero fun y _ => by rw [if_neg (fun (h : y.val = z) => hz (h ▸ y.isLt)), mul_zero]

theorem sum_prodW_pred {N p : ℕ} {w : Fin N → ℝ} (hs : ∑ y, w y = 1)
    (E : (Fin p → Fin N) → Prop) {dE : DecidablePred E} (Pt : Fin p → Fin N → Prop)
    (hE : ∀ x, E x ↔ ∀ t, Pt t (x t)) :
    ∑ x, prodW w x * (if E x then 1 else 0) = ∏ t, ∑ y, w y * (if Pt t y then 1 else 0) := by
  rw [← sum_prodW_prefix hs]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  exact if_congr (hE x) rfl rfl

/-- The `j₀` factor of block `j`. -/
def gZ (Z : List ℕ) (c : ℕ) : ℝ := if c < Z.length then kz j₀ (Z.getD c 0) else 1

/-- **Anti-diagonal separation and the pair marginals.** -/
theorem factor_eq (j : Fin r) (Z : List ℕ) (S : List (ℕ × ℕ)) (hZS : Z.length + S.length ≤ n) :
    ∑ o, (C j).w o * (if XAj P C j o Z ∧ BAj P C j o S then 1 else 0) =
      (∏ t ∈ range (P.X.s j), gZ (j₀ := j₀) Z (P.X.O j + t)) *
        pathMass (subK j₀ h2).toITree (win (P.B.O j) (P.B.s j) S) := by
  by_cases hA : Z.length ≤ P.X.O j
  · have hX : ∀ o, XAj P C j o Z := fun o t ht hc => absurd hc (by omega)
    have h1 : ∏ t ∈ range (P.X.s j), gZ (j₀ := j₀) Z (P.X.O j + t) = 1 :=
      prod_eq_one fun t _ => by unfold gZ; rw [if_neg (by omega)]
    rw [h1, one_mul, ← (C j).mB _ (by rw [length_win]; exact min_le_left _ _)]
    refine sum_congr rfl fun o _ => ?_
    simp only [hX o, true_and, BAj, indAgree]
  · have hB : S.length ≤ P.B.O j := by have := P.sep j; omega
    have hw : win (P.B.O j) (P.B.s j) S = [] := by
      simp [win, List.drop_eq_nil_of_le hB]
    have hBA : ∀ o, BAj P C j o S := fun o => by unfold BAj; rw [hw]; exact iAgree_nil _ _
    rw [hw, pathMass_nil, mul_one]
    simp only [hBA, and_true]
    refine Eq.trans ((C j).mX (fun x => ∀ t (ht : t < P.X.s j), P.X.O j + t < Z.length →
      (x ⟨t, ht⟩).val = Z.getD (P.X.O j + t) 0)) ?_
    refine Eq.trans (sum_prodW_pred (κ.Ksum j₀) (fun x => ∀ t (ht : t < P.X.s j), P.X.O j + t < Z.length →
      (x ⟨t, ht⟩).val = Z.getD (P.X.O j + t) 0) (fun t y => P.X.O j + t.val < Z.length →
      y.val = Z.getD (P.X.O j + t.val) 0) (fun x => ⟨fun h t => h t.val t.isLt,
        fun h t ht => h ⟨t, ht⟩⟩)) ?_
    rw [← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun t _ => ?_
    unfold gZ
    split_ifs with hc
    · simp only [hc, true_implies]; exact sum_K_ite _
    · simp only [hc, false_implies, if_true, mul_one]; exact κ.Ksum j₀

theorem ind_forall {Q : Fin r → Prop} :
    (if ∀ j, Q j then (1:ℝ) else 0) = ∏ j, (if Q j then 1 else 0) := by
  split_ifs with h
  · exact (prod_eq_one fun j _ => if_pos (h j)).symm
  · push_neg at h; obtain ⟨j, hj⟩ := h
    exact (prod_eq_zero (mem_univ j) (if_neg hj)).symm

/-- **Exactness of the interleaved decoder.** -/
theorem decoder_exact (h : List (ℕ × ℕ)) (hn : h.length ≤ n) :
    ∑ ω : Gl P C, (∏ j, (C j).w (ω j)) * indAgree κ.toITree (strat P C ω) h =
      pathMass κ.toITree h := by
  have hl := length_Zl_Sl j₀ h
  have hZ : (Zl j₀ h).length ≤ n := by omega
  have hS : (Sl j₀ h).length ≤ n := by omega
  have e1 : ∀ ω : Gl P C, indAgree κ.toITree (strat P C ω) h =
      ∏ j, (if XAj P C j (ω j) (Zl j₀ h) ∧ BAj P C j (ω j) (Sl j₀ h) then 1 else 0) := by
    intro ω
    unfold indAgree
    by_cases hA : iAgree κ.toITree (strat P C ω) h
    · rw [if_pos hA]
      obtain ⟨hx, hb⟩ := (agree_decomp P C ω h).1 hA
      rw [XAg_iff P C ω _ hZ] at hx; rw [BAg_iff P C ω _ hS] at hb
      exact (prod_eq_one fun j _ => if_pos ⟨hx j, hb j⟩).symm
    · rw [if_neg hA]
      have : ¬ ∀ j, (XAj P C j (ω j) (Zl j₀ h) ∧ BAj P C j (ω j) (Sl j₀ h)) := fun hall =>
        hA ((agree_decomp P C ω h).2 ⟨(XAg_iff P C ω _ hZ).2 fun j => (hall j).1,
          (BAg_iff P C ω _ hS).2 fun j => (hall j).2⟩)
      push_neg at this
      obtain ⟨j, hj⟩ := this
      exact (prod_eq_zero (mem_univ j) (if_neg (fun h' => hj h'.1 h'.2))).symm
  simp_rw [e1, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j o => (C j).w o *
    (if XAj P C j o (Zl j₀ h) ∧ BAj P C j o (Sl j₀ h) then 1 else 0))]
  simp_rw [factor_eq P C _ (Zl j₀ h) (Sl j₀ h) (by omega)]
  rw [prod_mul_distrib, P.X.prod_eq]
  simp only [gZ]
  rw [prod_range_ite _ hZ]
  simp_rw [(subK j₀ h2).pathMass_eq_prod, win_prod (subK j₀ h2).wt (0, 0)]
  rw [P.B.prod_eq (fun c => if c < (Sl j₀ h).length then (subK j₀ h2).wt ((Sl j₀ h).getD c (0, 0))
      else 1), prod_range_ite _ hS, pathMass_split j₀ h2, (subK j₀ h2).pathMass_eq_prod,
    list_prod_eq_range _ 0, list_prod_eq_range _ (0, 0)]

/-! ### The global seed -/

instance : Countable (Gl P C) := inferInstance

def gSeed : AlphabetSeed κ.toITree (Gl P C) where
  weight ω := ∏ j, (C j).w (ω j)
  nonneg ω := prod_nonneg fun j _ => (C j).nonneg _
  mass := by
    convert hasSum_fintype (fun ω : Gl P C => ∏ j, (C j).w (ω j))
    rw [← Fintype.prod_sum]; simp [(C _).total]
  strategy := strat P C

theorem gSeed_exactTo : (gSeed P C).ExactTo n := by
  intro h hn
  simp only [AlphabetSeed.hit, gSeed, tsum_fintype]
  exact decoder_exact P C h hn

theorem gSeed_entropy :
    (gSeed P C).entropy = ENNReal.ofReal (∑ j, ∑ o, Real.negMulLog ((C j).w o)) := by
  unfold AlphabetSeed.entropy
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    exact entropy_pi (fun j o => (C j).w o) (fun j o => (C j).nonneg o) (fun j => (C j).total)
  · intro ω _
    have h1 : ∏ j, (C j).w (ω j) ≤ 1 := Finset.prod_le_one₀ (fun j _ => (C j).nonneg _) fun j _ => by
      have := single_le_sum (fun o _ => (C j).nonneg o) (mem_univ (ω j)); rw [(C j).total] at this
      exact this
    exact Real.negMulLog_nonneg (show 0 ≤ ∏ j, (C j).w (ω j) from
      prod_nonneg fun j _ => (C j).nonneg (ω j)) h1

/-- **Cost of a plan.** `C_n` is at most the sum of the pair entropies. -/
theorem finiteCost_le_plan :
    finiteCost κ.toITree n ≤ ENNReal.ofReal (∑ j, ∑ o, Real.negMulLog ((C j).w o)) := by
  rw [← countableFiniteCost_eq, ← gSeed_entropy P C, ← (gSeed P C).toSeed_entropy]
  exact iInf_le_of_le ⟨(gSeed P C).toSeed, ((gSeed P C).toSeed_exactTo n).2 (gSeed_exactTo P C)⟩
    le_rfl

end CausalSpectrum.Kernel
