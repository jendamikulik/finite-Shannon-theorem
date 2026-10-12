/-
Random-walk maxima for a finite i.i.d. increment law, in finite form.

A law `Q` on a finite alphabet with increments `X y`. A sample of length `n` is a word
`ys : Fin n → Fin k` of weight `∏ Q(ys i)`; expectations are finite weighted sums. The walk is
`S_j = X_1 + … + X_j`, its running maximum `M_n = max_{0 ≤ j ≤ n} S_j`.

Main result: Spitzer's identity `E M_n = ∑_{k=1}^n E(S_k)_+ / k`, proved by a cyclic-shift
argument (no generating functions).
-/
import CausalSeed.Entropy

noncomputable section
open Classical Finset

namespace CausalSpectrum.Walk

/-- A finite increment law: weights `Q` (a probability vector) and increments `X`. -/
structure Law where
  k : ℕ
  Q : Fin k → ℝ
  Qnn : ∀ y, 0 ≤ Q y
  Qsum : ∑ y, Q y = 1
  X : Fin k → ℝ

/-! ### Deterministic walks -/

/-- Partial sum `S_j = x_0 + … + x_{j-1}`. -/
def S (x : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range j, x i

/-- Running maximum `M_n = max_{0 ≤ j ≤ n} S_j`. -/
def M (x : ℕ → ℝ) (n : ℕ) : ℝ := (range (n + 1)).sup' nonempty_range_add_one (S x)

/-- `min_{1 ≤ l ≤ N} S_l`. -/
def mn (x : ℕ → ℝ) (N : ℕ) : ℝ := (Icc 1 (N + 1)).inf' (by simp) (S x)

theorem S_zero (x : ℕ → ℝ) : S x 0 = 0 := by simp [S]

theorem S_succ (x : ℕ → ℝ) (j : ℕ) : S x (j + 1) = S x j + x j := by simp [S, sum_range_succ]

theorem le_M (x : ℕ → ℝ) {n j : ℕ} (hj : j ≤ n) : S x j ≤ M x n :=
  le_sup' (S x) (mem_range.2 (by omega))

theorem M_le {x : ℕ → ℝ} {n : ℕ} {c : ℝ} (h : ∀ j ≤ n, S x j ≤ c) : M x n ≤ c :=
  sup'_le _ _ fun j hj => h j (by simpa [Nat.lt_succ_iff] using hj)

theorem M_nonneg (x : ℕ → ℝ) (n : ℕ) : 0 ≤ M x n := by
  have := le_M x (Nat.zero_le n); rwa [S_zero] at this

theorem M_zero (x : ℕ → ℝ) : M x 0 = 0 :=
  le_antisymm (M_le fun j hj => by obtain rfl : j = 0 := by omega
                                   exact (S_zero x).le) (M_nonneg x 0)

theorem M_succ (x : ℕ → ℝ) (n : ℕ) : M x (n + 1) = max (M x n) (S x (n + 1)) := by
  apply le_antisymm
  · apply M_le; intro j hj
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · exact (le_M x (by omega)).trans (le_max_left _ _)
    · obtain rfl : j = n + 1 := by omega
      exact le_max_right _ _
  · exact max_le (M_le fun j hj => le_M x (by omega)) (le_M x le_rfl)

theorem M_mono (x : ℕ → ℝ) (n : ℕ) : M x n ≤ M x (n + 1) := by
  rw [M_succ]; exact le_max_left _ _

theorem S_congr {x x' : ℕ → ℝ} {j : ℕ} (h : ∀ i < j, x i = x' i) : S x j = S x' j :=
  sum_congr rfl fun i hi => h i (mem_range.1 hi)

theorem M_congr {x x' : ℕ → ℝ} {n : ℕ} (h : ∀ i < n, x i = x' i) : M x n = M x' n := by
  unfold M
  exact sup'_congr _ rfl fun j hj => S_congr fun i hi => h i (by simp at hj; omega)

/-- The cons of a value in front of a sequence. -/
def consS (c : ℝ) (x : ℕ → ℝ) : ℕ → ℝ := fun i => Nat.casesOn i c x

theorem S_consS (c : ℝ) (x : ℕ → ℝ) (j : ℕ) : S (consS c x) (j + 1) = c + S x j := by
  induction j with
  | zero => simp [S, consS]
  | succ j ih => rw [S_succ, ih, S_succ]; simp [consS]; ring

theorem M_consS (c : ℝ) (x : ℕ → ℝ) (n : ℕ) : M (consS c x) (n + 1) = max 0 (c + M x n) := by
  apply le_antisymm
  · apply M_le; intro j hj
    rcases j with _ | j
    · rw [S_zero]; exact le_max_left _ _
    · rw [S_consS]
      linarith [le_M x (n := n) (j := j) (by omega), le_max_right 0 (c + M x n)]
  · refine max_le (M_nonneg _ _) ?_
    obtain ⟨j, hj, he⟩ := exists_mem_eq_sup' nonempty_range_add_one (S x)
    change c + M x n ≤ _
    rw [show M x n = S x j from he, ← S_consS]
    exact le_M _ (by simp at hj; omega)

/-! ### Reversal -/

/-- The reversed word of length `N`. -/
def revS (x : ℕ → ℝ) (N : ℕ) : ℕ → ℝ := fun i => if i < N then x (N - 1 - i) else 0

theorem S_revS (x : ℕ → ℝ) (N : ℕ) : ∀ l ≤ N, S (revS x N) l = S x N - S x (N - l)
  | 0, _ => by simp [S_zero]
  | l + 1, hl => by
    rw [S_succ, S_revS x N l (by omega)]
    have : S x (N - l) = S x (N - (l + 1)) + x (N - (l + 1)) := by
      rw [← S_succ]; congr 1; omega
    rw [this, revS, if_pos (by omega), show N - 1 - l = N - (l + 1) by omega]; ring

theorem inf'_add_const {ι : Type*} {s : Finset ι} (H : s.Nonempty) (g : ι → ℝ) (c : ℝ) :
    s.inf' H (fun l => g l + c) = s.inf' H g + c := by
  apply le_antisymm
  · obtain ⟨l, hl, he⟩ := exists_mem_eq_inf' H g
    rw [he]; exact inf'_le _ hl
  · exact le_inf' _ _ fun l hl => by linarith [inf'_le g hl]

/-- `S_{n+1} - M_n = min_{1 ≤ l ≤ n+1} S_l` of the reversed word. -/
theorem S_sub_M (x : ℕ → ℝ) (n : ℕ) : S x (n + 1) - M x n = mn (revS x (n + 1)) n := by
  apply le_antisymm
  · obtain ⟨j, hj, he⟩ := exists_mem_eq_inf' (s := Icc 1 (n + 1)) (by simp) (S (revS x (n + 1)))
    rw [mn, he, S_revS x _ j (by simp at hj; omega)]
    have := le_M x (n := n) (j := n + 1 - j) (by simp at hj; omega)
    linarith
  · obtain ⟨j, hj, he⟩ := exists_mem_eq_sup' nonempty_range_add_one (S x)
    have hj' : j ≤ n := by simp at hj; omega
    have h1 := inf'_le (S (revS x (n + 1))) (show n + 1 - j ∈ Icc 1 (n + 1) by simp; omega)
    rw [S_revS x _ _ (by omega), show n + 1 - (n + 1 - j) = j by omega] at h1
    change mn _ n ≤ S x (n + 1) - M x n
    rw [show M x n = S x j from he]; exact h1

/-! ### The cyclic lemma -/

section Cyclic
variable (p : ℕ → ℝ) (n : ℕ)

theorem S_period (hp : ∀ i, p (i + (n + 1)) = p i) :
    ∀ i, S p (i + (n + 1)) = S p i + S p (n + 1) := by
  intro i
  unfold S; rw [add_comm i, sum_range_add, add_comm]; congr 1
  exact sum_congr rfl fun j _ => by rw [add_comm]; exact hp j

/-- `f i = min_{1 ≤ l ≤ n+1} S_{i+l}`. -/
def fmin (i : ℕ) : ℝ := (Icc 1 (n + 1)).inf' (by simp) (fun l => S p (i + l))

theorem fmin_succ (hp : ∀ i, p (i + (n + 1)) = p i) (hc : 0 < S p (n + 1)) (i : ℕ) :
    fmin p n i = min (S p (i + 1)) (fmin p n (i + 1)) := by
  apply le_antisymm
  · refine le_min (inf'_le _ (show 1 ∈ Icc 1 (n + 1) by simp)) (le_inf' _ _ fun l hl => ?_)
    rw [Finset.mem_Icc] at hl
    rcases Nat.lt_or_ge l (n + 1) with h | h
    · rw [show i + 1 + l = i + (l + 1) by omega]; exact inf'_le _ (by simp; omega)
    · obtain rfl : l = n + 1 := by omega
      rw [show i + 1 + (n + 1) = (i + 1) + (n + 1) by omega, S_period p n hp]
      have := inf'_le (fun l => S p (i + l)) (show 1 ∈ Icc 1 (n + 1) by simp)
      change fmin p n i ≤ _ at this
      linarith
  · refine le_inf' _ _ fun l hl => ?_
    rw [Finset.mem_Icc] at hl
    rcases Nat.eq_or_lt_of_le hl.1 with h | h
    · subst h; exact min_le_left _ _
    · refine (min_le_right _ _).trans ?_
      have := inf'_le (fun l => S p (i + 1 + l)) (show l - 1 ∈ Icc 1 (n + 1) by simp; omega)
      change fmin p n (i + 1) ≤ S p (i + 1 + (l - 1)) at this
      rwa [show i + 1 + (l - 1) = i + l by omega] at this

theorem fmin_period (hp : ∀ i, p (i + (n + 1)) = p i) (i : ℕ) :
    fmin p n (i + (n + 1)) = fmin p n i + S p (n + 1) := by
  unfold fmin
  rw [← inf'_add_const]
  congr 1; funext l
  rw [show i + (n + 1) + l = (i + l) + (n + 1) by omega, S_period p n hp]

/-- **Cyclic lemma.** For an `(n+1)`-periodic sequence,
`∑_{i ≤ n} (min_{1≤l≤n+1} (S_{i+l} - S_i))_+ = (S_{n+1})_+`. -/
theorem cyclic_sum (hp : ∀ i, p (i + (n + 1)) = p i) :
    ∑ i ∈ range (n + 1), max (fmin p n i - S p i) 0 = max (S p (n + 1)) 0 := by
  rcases le_or_gt (S p (n + 1)) 0 with hc | hc
  · rw [max_eq_right hc]
    refine sum_eq_zero fun i _ => max_eq_right ?_
    have := inf'_le (fun l => S p (i + l)) (show n + 1 ∈ Icc 1 (n + 1) by simp)
    try dsimp only at this
    rw [S_period p n hp] at this
    change fmin p n i ≤ _ at this
    linarith
  · rw [max_eq_left hc.le]
    have h1 : ∀ i, max (fmin p n i - S p i) 0 = fmin p n i - min (S p i) (fmin p n i) := by
      intro i
      rcases le_total (S p i) (fmin p n i) with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]
      · rw [min_eq_right h, max_eq_right (by linarith)]; ring
    simp only [h1, sum_sub_distrib]
    have h2 : ∑ i ∈ range (n + 1), min (S p i) (fmin p n i) =
        ∑ i ∈ range (n + 1), fmin p n i - S p (n + 1) := by
      rw [sum_range_succ', sum_range_succ]
      have e1 : ∀ i, min (S p (i + 1)) (fmin p n (i + 1)) = fmin p n i :=
        fun i => (fmin_succ p n hp hc i).symm
      simp only [e1]
      have e2 : min (S p 0) (fmin p n 0) = fmin p n n - S p (n + 1) := by
        rw [fmin_succ p n hp hc n]
        have a := fmin_period p n hp 0
        simp only [zero_add] at a
        rw [a, S_zero]
        have : min (S p (n + 1)) (fmin p n 0 + S p (n + 1)) = min 0 (fmin p n 0) + S p (n + 1) := by
          rw [← min_add_add_right, zero_add]
        linarith
      rw [e2]; ring
    rw [h2]; ring

end Cyclic

/-- The cyclic rotation by `i` of a word of length `n+1`. -/
def rotS (x : ℕ → ℝ) (n i : ℕ) : ℕ → ℝ :=
  fun j => if j < n + 1 then x ((i + j) % (n + 1)) else 0

theorem S_rotS (x : ℕ → ℝ) (n i : ℕ) :
    ∀ l ≤ n + 1, S (rotS x n i) l = S (fun j => x (j % (n + 1))) (i + l) -
      S (fun j => x (j % (n + 1))) i
  | 0, _ => by simp [S_zero]
  | l + 1, hl => by
    rw [S_succ, S_rotS x n i l (by omega), show i + (l + 1) = i + l + 1 by omega, S_succ,
      rotS, if_pos (by omega)]; ring

/-- **Deterministic Spitzer step.** For a word of length `n+1`,
`∑_{i ≤ n} (min_{1≤l≤n+1} S_l(rot_i x))_+ = (S_{n+1})_+`. -/
theorem sum_rot (x : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), max (mn (rotS x n i) n) 0 = max (S x (n + 1)) 0 := by
  set p : ℕ → ℝ := fun j => x (j % (n + 1))
  have hp : ∀ i, p (i + (n + 1)) = p i := fun i => by simp [p]
  have hS : S p (n + 1) = S x (n + 1) :=
    S_congr fun i hi => by simp [p, Nat.mod_eq_of_lt hi]
  rw [← hS, ← cyclic_sum p n hp]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  unfold mn fmin
  rw [sub_eq_add_neg, ← inf'_add_const]
  exact inf'_congr _ rfl fun l hl => by
    rw [S_rotS x n i l (by simp at hl; omega)]; ring

/-! ### Expectations over i.i.d. words -/

namespace Law
variable (W : Law)

/-- Weight of a word: `∏ Q(ys i)`. -/
def wgt {n : ℕ} (ys : Fin n → Fin W.k) : ℝ := ∏ i, W.Q (ys i)

/-- Increment sequence of a word, extended by zero. -/
def seq {n : ℕ} (ys : Fin n → Fin W.k) : ℕ → ℝ := fun i => if h : i < n then W.X (ys ⟨i, h⟩) else 0

/-- Expectation over i.i.d. words of length `n`. -/
def E (n : ℕ) (f : (ℕ → ℝ) → ℝ) : ℝ := ∑ ys : Fin n → Fin W.k, W.wgt ys * f (W.seq ys)

variable {W}

theorem wgt_nonneg {n : ℕ} (ys : Fin n → Fin W.k) : 0 ≤ W.wgt ys :=
  prod_nonneg fun _ _ => W.Qnn _

variable (W)

theorem sum_wgt (n : ℕ) : ∑ ys : Fin n → Fin W.k, W.wgt ys = 1 := by
  unfold wgt
  rw [← Fintype.prod_sum (fun (_ : Fin n) (y : Fin W.k) => W.Q y)]
  simp [W.Qsum]

theorem E_const (n : ℕ) (c : ℝ) : W.E n (fun _ => c) = c := by
  unfold E; rw [← sum_mul, sum_wgt, one_mul]

theorem E_add (n : ℕ) (f g : (ℕ → ℝ) → ℝ) :
    W.E n (fun x => f x + g x) = W.E n f + W.E n g := by
  unfold E; rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring

theorem E_mul_const (n : ℕ) (f : (ℕ → ℝ) → ℝ) (c : ℝ) :
    W.E n (fun x => c * f x) = c * W.E n f := by
  unfold E; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem E_sum (n : ℕ) {ι : Type*} (s : Finset ι) (g : ι → (ℕ → ℝ) → ℝ) :
    W.E n (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, W.E n (g i) := by
  unfold E; simp only [mul_sum]; exact sum_comm

theorem E_mono (n : ℕ) {f g : (ℕ → ℝ) → ℝ} (h : ∀ x, f x ≤ g x) : W.E n f ≤ W.E n g :=
  sum_le_sum fun ys _ => mul_le_mul_of_nonneg_left (h _) (wgt_nonneg ys)

theorem E_nonneg (n : ℕ) {f : (ℕ → ℝ) → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ W.E n f := by
  have := W.E_mono n (f := fun _ => 0) h; rwa [E_const] at this

theorem seq_cons {n : ℕ} (y : Fin W.k) (zs : Fin n → Fin W.k) :
    W.seq (Fin.cons y zs : Fin (n + 1) → Fin W.k) = consS (W.X y) (W.seq zs) := by
  funext i
  rcases i with _ | i
  · simp [seq, consS]
  · by_cases h : i < n
    · simp [seq, consS, h]
      exact congrArg W.X (Fin.cons_succ (α := fun _ => Fin W.k) y zs ⟨i, h⟩)
    · simp [seq, consS, h]

/-- First-step decomposition. -/
theorem E_succ (n : ℕ) (f : (ℕ → ℝ) → ℝ) :
    W.E (n + 1) f = ∑ y, W.Q y * W.E n (fun x => f (consS (W.X y) x)) := by
  unfold E
  rw [← (Fin.consEquiv fun _ => Fin W.k).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun zs _ => ?_
  have e : (Fin.consEquiv (fun _ => Fin W.k)) (y, zs) = Fin.cons y zs := rfl
  rw [e, seq_cons]
  simp only [wgt, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  try ring

theorem E_zero (f : (ℕ → ℝ) → ℝ) : W.E 0 f = f (fun _ => 0) := by
  unfold E
  rw [Fintype.sum_unique]
  simp only [wgt, Finset.univ_eq_empty, prod_empty, one_mul]
  congr 1

/-- Marginalization: a functional of the first `n` increments has the same expectation over
words of length `n + 1` and `n`. -/
theorem E_marg : ∀ (n : ℕ) (f : (ℕ → ℝ) → ℝ),
    (∀ x x', (∀ i < n, x i = x' i) → f x = f x') → W.E (n + 1) f = W.E n f
  | 0, f, hf => by
    rw [E_succ]
    simp only [E_zero]
    have : ∀ y, f (consS (W.X y) fun _ => 0) = f fun _ => 0 :=
      fun y => hf _ _ (fun i hi => absurd hi (Nat.not_lt_zero _))
    simp only [this]
    rw [← sum_mul, W.Qsum, one_mul]
  | n + 1, f, hf => by
    rw [E_succ, E_succ (n := n)]
    refine sum_congr rfl fun y _ => ?_
    rw [E_marg n]
    intro x x' h
    apply hf
    intro i hi
    rcases i with _ | i
    · rfl
    · exact h i (by omega)

/-- Permutation of the coordinates of a word of length `N`. -/
def permS {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if h : j < N then x (σ ⟨j, h⟩) else 0

/-- Exchangeability: permuting the increments does not change expectations. -/
theorem E_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : (ℕ → ℝ) → ℝ) :
    W.E N (fun x => f (permS σ x)) = W.E N f := by
  unfold E
  refine Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ fun ys => ?_
  have hw : W.wgt (Equiv.arrowCongr σ.symm (Equiv.refl _) ys) = W.wgt ys := by
    unfold wgt; simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl,
      Function.comp_apply, id]
    exact Equiv.prod_comp σ (fun i => W.Q (ys i))
  have hs : permS σ (W.seq ys) = W.seq (Equiv.arrowCongr σ.symm (Equiv.refl _) ys) := by
    funext j
    unfold permS seq
    by_cases h : j < N
    · simp only [h, dite_true, Fin.is_lt, Fin.eta, Equiv.arrowCongr_apply, Equiv.symm_symm,
        Equiv.coe_refl, Function.comp_apply, id]
    · simp only [h, dite_false]
  show W.wgt ys * f (permS σ (W.seq ys)) = _
  rw [hw, hs]

theorem revS_eq (x : ℕ → ℝ) (n : ℕ) : revS x (n + 1) = permS (N := n + 1) Fin.revPerm x := by
  funext j
  unfold revS permS
  by_cases h : j < n + 1
  · simp only [h, if_true, dite_true, Fin.revPerm_apply, Fin.val_rev]
    congr 1; omega
  · simp [h]

theorem rotS_eq (x : ℕ → ℝ) (n i : ℕ) (hi : i < n + 1) :
    rotS x n i = permS (Equiv.addLeft (⟨i, hi⟩ : Fin (n + 1))) x := by
  funext j
  unfold rotS permS
  by_cases h : j < n + 1
  · simp only [h, if_true, dite_true, Equiv.coe_addLeft, Fin.val_add]
  · simp [h]

/-! ### Spitzer's identity -/

/-- `E M_n`. -/
def EM (n : ℕ) : ℝ := W.E n (fun x => M x n)

/-- `E (S_k)_+`. -/
def ESp (k : ℕ) : ℝ := W.E k (fun x => max (S x k) 0)

theorem E_mn (n : ℕ) :
    W.E (n + 1) (fun x => max (mn x n) 0) = W.ESp (n + 1) / (n + 1) := by
  have h : ∀ i ∈ range (n + 1),
      W.E (n + 1) (fun x => max (mn (rotS x n i) n) 0) = W.E (n + 1) (fun x => max (mn x n) 0) :=
    fun i hi => by
      simp only [rotS_eq _ n i (mem_range.1 hi)]
      exact W.E_perm _ (fun x => max (mn x n) 0)
  have hs := W.E_sum (n + 1) (range (n + 1)) (fun i x => max (mn (rotS x n i) n) 0)
  simp only [sum_rot] at hs
  rw [sum_congr rfl h, sum_const, card_range, nsmul_eq_mul] at hs
  unfold ESp
  rw [hs]; push_cast
  field_simp
  try ring

theorem EM_succ (n : ℕ) : W.EM (n + 1) = W.EM n + W.ESp (n + 1) / (n + 1) := by
  unfold EM
  have h1 : ∀ x, M x (n + 1) = M x n + max (mn (revS x (n + 1)) n) 0 := by
    intro x
    rw [M_succ, ← S_sub_M]
    rcases le_total (M x n) (S x (n + 1)) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  simp only [h1]
  rw [E_add, W.E_marg n (fun x => M x n) (fun x x' h => M_congr h)]
  simp only [revS_eq]
  rw [W.E_perm Fin.revPerm (fun x => max (mn x n) 0), E_mn]

/-- **Spitzer's identity.** `E M_n = ∑_{k=1}^n E(S_k)_+ / k`. -/
theorem spitzer (n : ℕ) : W.EM n = ∑ k ∈ range n, W.ESp (k + 1) / (k + 1) := by
  induction n with
  | zero => simp [EM, M_zero, E_const]
  | succ n ih => rw [EM_succ, ih, sum_range_succ]

/-! ### The law of the maximum -/

/-- `P(M_n ≤ x)`. -/
def cdfM (n : ℕ) (x : ℝ) : ℝ := W.E n (fun z => if M z n ≤ x then 1 else 0)

theorem cdfM_zero (x : ℝ) : W.cdfM 0 x = if 0 ≤ x then 1 else 0 := by
  simp [cdfM, E_zero, M_zero]

theorem cdfM_succ (n : ℕ) (x : ℝ) :
    W.cdfM (n + 1) x = if 0 ≤ x then ∑ y, W.Q y * W.cdfM n (x - W.X y) else 0 := by
  unfold cdfM
  rw [E_succ]
  simp only [M_consS, max_le_iff]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    refine sum_congr rfl fun y _ => ?_
    congr 1; congr 1; funext z
    by_cases h : M z n ≤ x - W.X y
    · rw [if_pos ⟨hx, by linarith⟩, if_pos h]
    · rw [if_neg (fun h' => h (by linarith [h'.2])), if_neg h]
  · rw [if_neg hx]
    refine sum_eq_zero fun y _ => ?_
    convert mul_zero (W.Q y) using 2
    convert W.E_const n 0 using 2
    funext z; exact if_neg fun h => hx h.1

theorem cdfM_nonneg (n : ℕ) (x : ℝ) : 0 ≤ W.cdfM n x :=
  W.E_nonneg n fun _ => by split_ifs <;> norm_num

theorem cdfM_neg (n : ℕ) {x : ℝ} (hx : x < 0) : W.cdfM n x = 0 := by
  unfold cdfM
  have : (fun z => if M z n ≤ x then (1:ℝ) else 0) = fun _ => 0 := by
    funext z; rw [if_neg (by linarith [M_nonneg z n])]
  rw [this, E_const]

theorem cdfM_succ_le (n : ℕ) (x : ℝ) : W.cdfM (n + 1) x ≤ W.cdfM n x := by
  unfold cdfM
  rw [← W.E_marg n (fun z => if M z n ≤ x then (1:ℝ) else 0)
    (fun z z' h => by rw [M_congr h])]
  refine W.E_mono _ fun z => ?_
  have := M_mono z n
  split_ifs with h1 h2 <;> first | exact absurd (le_trans this h1) h2 | norm_num

/-! ### Exponential moments -/

/-- `λ(θ) = E e^{θ X}`. -/
def mgf (θ : ℝ) : ℝ := ∑ y, W.Q y * Real.exp (θ * W.X y)

theorem S_consS' (c : ℝ) (x : ℕ → ℝ) (j : ℕ) : S (consS c x) (j + 1) = c + S x j := S_consS c x j

theorem E_exp_S (θ : ℝ) (k : ℕ) : W.E k (fun z => Real.exp (θ * S z k)) = W.mgf θ ^ k := by
  induction k with
  | zero => simp [E_zero, S_zero]
  | succ k ih =>
    rw [E_succ, pow_succ, mgf, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    simp only [S_consS, mul_add, Real.exp_add]
    rw [E_mul_const, ih]; unfold mgf; ring

end Law

end CausalSpectrum.Walk
