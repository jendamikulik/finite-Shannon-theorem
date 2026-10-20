/-
Finite-horizon sandwich and the countable obstruction for
*The Entropy Cost of Vanishing Activity*.

Proved here, with no `sorry`:
* a product of Bernoulli laws has entropy `∑ h₂(pₜ)`;
* the product of the geometric gates has entropy `∑ (h₂(pₜ) + 2pₜ)`;
* every countable readout of that Bernoulli product has entropy at least the
  Bernoulli entropy, and the gate product attains the upper value;
* if `∑ p` diverges, no countable seed matches every finite maximizing transcript;
* if `∑ h₂(p)` diverges, no such seed has finite entropy.

Not in this file: one measure on every history-indexed response table, and
cylinder exactness for a history-dependent policy. The critical window
`log₂ ln n + O(1)` is not proved here.
-/
import CausalSeed.VanishingEmbed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Pseudo.Defs

noncomputable section

open Real Filter Finset

namespace Vanishing

/-- Bernoulli probability of a bit, with success probability `p`. -/
def bern (p : ℝ) (b : Bool) : ℝ :=
  if b then p else 1 - p

theorem bern_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : 0 ≤ bern p b := by
  cases b <;> simp [bern] <;> linarith [hp0, hp1]

theorem bern_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : bern p b ≤ 1 := by
  cases b <;> simp [bern] <;> linarith [hp0, hp1]

theorem bern_le_one_sub {p : ℝ} (hp : p ≤ 1 / 2) (b : Bool) : bern p b ≤ 1 - p := by
  cases b <;> simp [bern] <;> linarith [hp]

theorem bernoulli_sum {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) : ∑ b : Bool, bern p b = 1 := by
  rw [bool_sum]
  simp [bern]

theorem bernoulli_entropy {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ b : Bool, shannonTerm (bern p b) = h2 p := by
  rw [bool_sum]
  simp [bern, h2, add_comm]

/-- Joint law of independent Bernoulli bits. -/
def bernJoint {n : ℕ} (p : Fin n → ℝ) (y : Fin n → Bool) : ℝ :=
  ∏ t, bern (p t) (y t)

theorem bernJoint_nonneg {n : ℕ} {p : Fin n → ℝ} (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (y : Fin n → Bool) : 0 ≤ bernJoint p y :=
  Finset.prod_nonneg fun t _ => bern_nonneg (hp0 t) (hp1 t) (y t)

theorem bernJoint_le_one {n : ℕ} {p : Fin n → ℝ} (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (y : Fin n → Bool) : bernJoint p y ≤ 1 := by
  simpa [bernJoint] using
    Finset.prod_le_one₀ (s := Finset.univ) (f := fun t => bern (p t) (y t))
      (fun t _ => bern_nonneg (hp0 t) (hp1 t) (y t))
      (fun t _ => bern_le_one (hp0 t) (hp1 t) (y t))

theorem bernJoint_cons {n : ℕ} (p0 : ℝ) (p : Fin n → ℝ) (b : Bool) (y : Fin n → Bool) :
    bernJoint (Fin.cons p0 p) (Fin.cons b y) = bern p0 b * bernJoint p y := by
  rw [bernJoint, bernJoint, Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

theorem bernJoint_sum {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) :
    ∑ y : Fin n → Bool, bernJoint p y = 1 := by
  induction n with
  | zero =>
    rw [Fintype.sum_unique]
    simp [bernJoint]
  | succ n ih =>
    let p0 := p 0
    let p' := Fin.tail p
    have hp0' : ∀ t, 0 ≤ p' t := fun t => hp0 t.succ
    have hp1' : ∀ t, p' t ≤ 1 := fun t => hp1 t.succ
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => Bool)
    rw [← e.sum_comp (bernJoint p)]
    have hfac : ∀ q : Bool × (Fin n → Bool),
        bernJoint p (e q) = bern p0 q.1 * bernJoint p' q.2 := by
      intro q
      have hpcons : p = Fin.cons p0 p' := by simp [p0, p', Fin.cons_self_tail]
      have he : e q = Fin.cons q.1 q.2 := rfl
      rw [hpcons, he]
      exact bernJoint_cons p0 p' q.1 q.2
    simp_rw [hfac, Fintype.sum_prod_type]
    change ∑ x : Bool, ∑ y : Fin n → Bool, bern p0 x * bernJoint p' y = 1
    simp_rw [← Finset.mul_sum]
    simp_rw [ih p' hp0' hp1', mul_one]
    exact bernoulli_sum (hp0 0) (hp1 0)

theorem bernJoint_entropy {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) :
    ∑ y : Fin n → Bool, shannonTerm (bernJoint p y) = ∑ t, h2 (p t) := by
  induction n with
  | zero =>
    rw [Fintype.sum_unique]
    simp [bernJoint, shannonTerm, logb_one]
  | succ n ih =>
    let p0 := p 0
    let p' := Fin.tail p
    have hp0' : ∀ t, 0 ≤ p' t := fun t => hp0 t.succ
    have hp1' : ∀ t, p' t ≤ 1 := fun t => hp1 t.succ
    have hp00 : 0 ≤ p0 := hp0 0
    have hp01 : p0 ≤ 1 := hp1 0
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => Bool)
    rw [← e.sum_comp fun y => shannonTerm (bernJoint p y)]
    have hfac : ∀ q : Bool × (Fin n → Bool),
        bernJoint p (e q) = bern p0 q.1 * bernJoint p' q.2 := by
      intro q
      have hpcons : p = Fin.cons p0 p' := by simp [p0, p', Fin.cons_self_tail]
      have he : e q = Fin.cons q.1 q.2 := rfl
      rw [hpcons, he]
      exact bernJoint_cons p0 p' q.1 q.2
    simp_rw [hfac]
    have hpt : ∀ b (y : Fin n → Bool), shannonTerm (bern p0 b * bernJoint p' y) =
        bernJoint p' y * shannonTerm (bern p0 b) +
          bern p0 b * shannonTerm (bernJoint p' y) :=
      fun b y => shannonTerm_mul (bern_nonneg hp00 hp01 b) (bernJoint_nonneg hp0' hp1' y)
    rw [Fintype.sum_prod_type]
    change ∑ x : Bool, ∑ y : Fin n → Bool,
      shannonTerm (bern p0 x * bernJoint p' y) = ∑ t, h2 (p t)
    simp_rw [hpt, Finset.sum_add_distrib]
    have hmass : ∑ y : Fin n → Bool, bernJoint p' y = 1 := bernJoint_sum p' hp0' hp1'
    have hent : ∑ y : Fin n → Bool, shannonTerm (bernJoint p' y) = ∑ t, h2 (p' t) :=
      ih p' hp0' hp1'
    have hL : ∑ x : Bool, ∑ y : Fin n → Bool, bernJoint p' y * shannonTerm (bern p0 x) =
        h2 p0 := by
      simp_rw [← Finset.sum_mul, hmass, one_mul]
      exact bernoulli_entropy hp00 hp01
    have hR : ∑ x : Bool, ∑ y : Fin n → Bool, bern p0 x * shannonTerm (bernJoint p' y) =
        ∑ t, h2 (p' t) := by
      simp_rw [← Finset.mul_sum, hent, ← Finset.sum_mul, bernoulli_sum hp00 hp01, one_mul]
    rw [hL, hR, Fin.sum_univ_succ (fun t => h2 (p t))]
    simp [p0, p', Fin.tail]

theorem zProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : 0 ≤ zProb p k := by
  cases k with
  | zero =>
    simp [zProb]
    linarith
  | succ k =>
    simp [zProb]
    positivity

theorem zProb_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : zProb p k ≤ 1 := by
  cases k with
  | zero =>
    simp [zProb]
    linarith
  | succ k =>
    have hpow : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    simp [zProb]
    have hpow0 : (0 : ℝ) ≤ (1 / 2) ^ (k + 1) := by positivity
    have : p * (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
      have := mul_le_mul hp1 hpow hpow0 (by norm_num : (0 : ℝ) ≤ 1)
      simpa using this
    simpa using this

/-- Product of the geometric gates. -/
def seedProb {n : ℕ} (p : Fin n → ℝ) (z : Fin n → ℕ) : ℝ :=
  ∏ t, zProb (p t) (z t)

theorem seedProb_cons {n : ℕ} (p0 : ℝ) (p : Fin n → ℝ) (z0 : ℕ) (z : Fin n → ℕ) :
    seedProb (Fin.cons p0 p) (Fin.cons z0 z) = zProb p0 z0 * seedProb p z := by
  rw [seedProb, seedProb, Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

theorem seedProb_nonneg {n : ℕ} {p : Fin n → ℝ} (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (z : Fin n → ℕ) : 0 ≤ seedProb p z :=
  Finset.prod_nonneg fun t _ => zProb_nonneg (hp0 t) (hp1 t) (z t)

theorem seedProb_le_one {n : ℕ} {p : Fin n → ℝ} (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (z : Fin n → ℕ) : seedProb p z ≤ 1 := by
  simpa [seedProb] using
    Finset.prod_le_one₀ (s := Finset.univ) (f := fun t => zProb (p t) (z t))
      (fun t _ => zProb_nonneg (hp0 t) (hp1 t) (z t))
      (fun t _ => zProb_le_one (hp0 t) (hp1 t) (z t))

theorem seedProb_pack {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) :
    Summable (seedProb p) ∧ ∑' z, seedProb p z = 1 := by
  induction n with
  | zero =>
    let z0 : Fin 0 → ℕ := fun t => Fin.elim0 t
    have honly : ∀ z : Fin 0 → ℕ, z = z0 := by
      intro z
      ext t
      exact Fin.elim0 t
    have hs : HasSum (seedProb p) (seedProb p z0) :=
      hasSum_single z0 fun z hz => False.elim (hz (honly z))
    refine ⟨hs.summable, hs.tsum_eq.trans ?_⟩
    simp [seedProb]
  | succ n ih =>
    let p0 := p 0
    let p' := Fin.tail p
    have hp0' : ∀ t, 0 ≤ p' t := fun t => hp0 t.succ
    have hp1' : ∀ t, p' t ≤ 1 := fun t => hp1 t.succ
    have hp00 : 0 ≤ p0 := hp0 0
    have hp01 : p0 ≤ 1 := hp1 0
    obtain ⟨hν, hνsum⟩ := ih p' hp0' hp1'
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
    have hfac : ∀ q : ℕ × (Fin n → ℕ), seedProb p (e q) = zProb p0 q.1 * seedProb p' q.2 := by
      intro q
      have hpcons : p = Fin.cons p0 p' := by simp [p0, p', Fin.cons_self_tail]
      have he : e q = Fin.cons q.1 q.2 := rfl
      rw [hpcons, he]
      exact seedProb_cons p0 p' q.1 q.2
    have hμN : Summable fun k : ℕ => ‖zProb p0 k‖ :=
      summable_norm_of_nonneg _ (fun k => zProb_nonneg hp00 hp01 k) summable_zProb
    have hνN : Summable fun z : Fin n → ℕ => ‖seedProb p' z‖ :=
      summable_norm_of_nonneg _ (seedProb_nonneg hp0' hp1') hν
    have hprod : Summable fun q : ℕ × (Fin n → ℕ) => zProb p0 q.1 * seedProb p' q.2 :=
      summable_mul_of_summable_norm hμN hνN
    have hs : Summable (seedProb p) := by
      rw [← e.summable_iff]
      exact (summable_congr hfac).2 hprod
    refine ⟨hs, ?_⟩
    rw [← e.tsum_eq (seedProb p), tsum_congr hfac, ← tsum_mul_tsum_of_summable_norm hμN hνN,
      zProb_tsum hp00 hp01, hνsum]
    ring

theorem seedProb_summable {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) :
    Summable (seedProb p) :=
  (seedProb_pack p hp0 hp1).1

theorem seedProb_sum {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) :
    ∑' z, seedProb p z = 1 :=
  (seedProb_pack p hp0 hp1).2

theorem summable_finset_sum {α β : Type*} [DecidableEq β] (s : Finset β) (g : β → α → ℝ)
    (hg : ∀ b ∈ s, Summable (g b)) : Summable fun a => ∑ b ∈ s, g b a := by
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    have hfun : (fun a => ∑ c ∈ insert b s, g c a) = fun a => g b a + ∑ c ∈ s, g c a := by
      funext a
      rw [Finset.sum_insert hb]
    rw [hfun]
    exact (hg b (Finset.mem_insert_self b s)).add
      (ih fun c hc => hg c (Finset.mem_insert_of_mem hc))

/-- A finite sum of sums is the sum of the finite sum. -/
theorem sum_tsum_swap {α β : Type*} [DecidableEq β] {s : Finset β} {g : β → α → ℝ}
    (hg : ∀ b ∈ s, Summable (g b)) :
    ∑ b ∈ s, ∑' a, g b a = ∑' a, ∑ b ∈ s, g b a := by
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    have hgb : Summable (g b) := hg b (Finset.mem_insert_self b s)
    have hgs : ∀ c ∈ s, Summable (g c) := fun c hc => hg c (Finset.mem_insert_of_mem hc)
    have hsum : Summable fun a => ∑ c ∈ s, g c a := summable_finset_sum s g hgs
    have hfun : (fun a => ∑ c ∈ insert b s, g c a) = fun a => g b a + ∑ c ∈ s, g c a := by
      funext a
      rw [Finset.sum_insert hb]
    rw [Finset.sum_insert hb, ih hgs, hfun, hgb.tsum_add hsum]

theorem shannonTerm_push_le {α β : Type*} [Fintype β] [DecidableEq β] (μ : α → ℝ) (f : α → β)
    (h0 : ∀ a, 0 ≤ μ a) (h1 : ∀ a, μ a ≤ 1) (hs : Summable μ)
    (hE : Summable fun a => shannonTerm (μ a)) (_hsum : ∑' a, μ a = 1) :
    ∑ b, shannonTerm (∑' a, if f a = b then μ a else 0) ≤ ∑' a, shannonTerm (μ a) := by
  classical
  let w : β → α → ℝ := fun b a => if f a = b then μ a else 0
  have hw0 : ∀ b a, 0 ≤ w b a := by
    intro b a
    dsimp [w]
    split_ifs <;> simp [h0]
  have hwle : ∀ b a, w b a ≤ μ a := by
    intro b a
    dsimp [w]
    split_ifs <;> simp [h0]
  have hwS : ∀ b, Summable (w b) := fun b => hs.of_nonneg_of_le (hw0 b) (hwle b)
  have hwA : ∀ b, ∑' a, w b a ≤ 1 := by
    intro b
    exact le_trans ((hwS b).tsum_le_tsum (hwle b) hs) (le_of_eq _hsum)
  have hwTerm : ∀ b a, shannonTerm (w b a) ≤ shannonTerm (μ a) := by
    intro b a
    by_cases hba : f a = b
    · simp [w, hba]
    · have : w b a = 0 := by simp [w, hba]
      rw [this, shannonTerm]
      simp
      exact shannonTerm_nonneg_of_le_one (h0 a) (h1 a)
  have hwE : ∀ b, Summable fun a => shannonTerm (w b a) := fun b =>
    hE.of_nonneg_of_le (fun a => shannonTerm_nonneg_of_le_one (hw0 b a) (le_trans (hwle b a) (h1 a)))
      (hwTerm b)
  have hgroup : ∀ b, shannonTerm (∑' a, w b a) ≤ ∑' a, shannonTerm (w b a) :=
    fun b => shannonTerm_group (w b) (hw0 b) (hwS b) (hwE b) (hwA b)
  refine le_trans (Finset.sum_le_sum fun b _ => hgroup b) ?_
  rw [sum_tsum_swap fun b _ => hwE b]
  refine le_of_eq (tsum_congr ?_)
  intro a
  rw [Fintype.sum_eq_single (f a)]
  · simp [w]
  · intro b hb
    have : w b a = 0 := by simp [w, hb.symm]
    simp [this, shannonTerm]

set_option maxHeartbeats 800000 in
/-- Entropy of the geometric-gate product. -/
theorem seed_entropy {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 < p t) (hp1 : ∀ t, p t < 1) :
    Summable (fun z : Fin n → ℕ => shannonTerm (seedProb p z)) ∧
      ∑' z, shannonTerm (seedProb p z) = ∑ t, (h2 (p t) + 2 * p t) := by
  induction n with
  | zero =>
    let z0 : Fin 0 → ℕ := fun t => Fin.elim0 t
    have honly : ∀ z : Fin 0 → ℕ, z = z0 := by
      intro z; ext t; exact Fin.elim0 t
    have hterm : shannonTerm (seedProb p z0) = 0 := by simp [seedProb, shannonTerm, logb_one]
    have hs : HasSum (fun z => shannonTerm (seedProb p z)) 0 := by
      have h0 : HasSum (fun z => shannonTerm (seedProb p z)) (shannonTerm (seedProb p z0)) :=
        hasSum_single z0 fun z hz => absurd (honly z) hz
      simpa [hterm] using h0
    exact ⟨hs.summable, hs.tsum_eq.trans (by simp)⟩
  | succ n ih =>
    let p0 := p 0
    let q := Fin.tail p
    have hq0 : ∀ t, 0 < q t := fun t => hp0 t.succ
    have hq1 : ∀ t, q t < 1 := fun t => hp1 t.succ
    have hp00 : 0 < p0 := hp0 0
    have hp01 : p0 < 1 := hp1 0
    obtain ⟨hνE, hνent⟩ := ih q hq0 hq1
    have hμE : Summable fun k => shannonTerm (zProb p0 k) := by
      by_contra h
      have hzero := tsum_eq_zero_of_not_summable h
      have hent := sparseCoordinate_entropy hp00 hp01
      rw [hzero] at hent
      have hpos : 0 < h2 p0 + 2 * p0 := by
        have hh : 0 ≤ h2 p0 := by
          unfold h2
          exact add_nonneg
            (shannonTerm_nonneg_of_le_one hp00.le hp01.le)
            (shannonTerm_nonneg_of_le_one (sub_nonneg.mpr hp01.le) (by linarith))
        linarith
      linarith
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
    have hfac : ∀ a : ℕ × (Fin n → ℕ),
        seedProb p (e a) = zProb p0 a.1 * seedProb q a.2 := by
      intro a
      have hpcons : p = Fin.cons p0 q := by simp [p0, q, Fin.cons_self_tail]
      have he : e a = Fin.cons a.1 a.2 := rfl
      rw [hpcons, he]
      exact seedProb_cons p0 q a.1 a.2
    have hpt : ∀ a : ℕ × (Fin n → ℕ), shannonTerm (zProb p0 a.1 * seedProb q a.2) =
        seedProb q a.2 * shannonTerm (zProb p0 a.1) +
          zProb p0 a.1 * shannonTerm (seedProb q a.2) :=
      fun a => shannonTerm_mul (zProb_nonneg hp00.le hp01.le a.1)
        (seedProb_nonneg (fun t => (hq0 t).le) (fun t => (hq1 t).le) a.2)
    have hνN : Summable fun z : Fin n → ℕ => ‖seedProb q z‖ :=
      summable_norm_of_nonneg _ (seedProb_nonneg (fun t => (hq0 t).le) (fun t => (hq1 t).le))
        (seedProb_summable q (fun t => (hq0 t).le) (fun t => (hq1 t).le))
    have hμEN : Summable fun k : ℕ => ‖shannonTerm (zProb p0 k)‖ :=
      summable_norm_of_nonneg _ (fun k => shannonTerm_nonneg_of_le_one
        (zProb_nonneg hp00.le hp01.le k) (zProb_le_one hp00.le hp01.le k)) hμE
    have hμN : Summable fun k : ℕ => ‖zProb p0 k‖ :=
      summable_norm_of_nonneg _ (fun k => zProb_nonneg hp00.le hp01.le k) summable_zProb
    have hνEN : Summable fun z : Fin n → ℕ => ‖shannonTerm (seedProb q z)‖ :=
      summable_norm_of_nonneg _ (fun z => shannonTerm_nonneg_of_le_one
        (seedProb_nonneg (fun t => (hq0 t).le) (fun t => (hq1 t).le) z)
        (seedProb_le_one (fun t => (hq0 t).le) (fun t => (hq1 t).le) z)) hνE
    have sA : Summable fun a : ℕ × (Fin n → ℕ) =>
        shannonTerm (zProb p0 a.1) * seedProb q a.2 :=
      summable_mul_of_summable_norm hμEN hνN
    have sB : Summable fun a : ℕ × (Fin n → ℕ) =>
        zProb p0 a.1 * shannonTerm (seedProb q a.2) :=
      summable_mul_of_summable_norm hμN hνEN
    have hSprod : Summable fun a : ℕ × (Fin n → ℕ) =>
        shannonTerm (zProb p0 a.1 * seedProb q a.2) :=
      ((sA.congr fun a => mul_comm _ _).add sB).congr fun a => (hpt a).symm
    have hs : Summable fun z => shannonTerm (seedProb p z) := by
      rw [← e.summable_iff]
      exact (summable_congr fun a => congrArg shannonTerm (hfac a)).2 hSprod
    have hprod := entropy_prod (fun k => zProb p0 k) (seedProb q)
      (fun k => zProb_nonneg hp00.le hp01.le k)
      (seedProb_nonneg (fun t => (hq0 t).le) (fun t => (hq1 t).le))
      (zProb_tsum hp00.le hp01.le) (seedProb_sum q (fun t => (hq0 t).le) (fun t => (hq1 t).le))
      summable_zProb (seedProb_summable q (fun t => (hq0 t).le) (fun t => (hq1 t).le))
      hμE hνE (fun k => zProb_le_one hp00.le hp01.le k)
      (fun z => seedProb_le_one (fun t => (hq0 t).le) (fun t => (hq1 t).le) z)
    refine ⟨hs, ?_⟩
    rw [← e.tsum_eq, tsum_congr fun a => congrArg shannonTerm (hfac a), hprod,
      sparseCoordinate_entropy hp00 hp01, hνent, Fin.sum_univ_succ (fun t => h2 (p t) + 2 * p t)]
    simp [p0, q, Fin.tail]

theorem h2_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ h2 p := by
  unfold h2
  exact add_nonneg (shannonTerm_nonneg_of_le_one hp0 hp1)
    (shannonTerm_nonneg_of_le_one (sub_nonneg.mpr hp1) (by linarith))

theorem zProb_bit {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    ∑' k : ℕ, (if (k ≠ 0) = b then zProb p k else 0) = bern p b := by
  cases b with
  | false =>
    have hs : HasSum (fun k : ℕ => if (k ≠ 0) = false then zProb p k else 0) (zProb p 0) :=
      hasSum_single 0 fun k hk => by simp [hk]
    rw [hs.tsum_eq, zProb_zero]
    simp [bern]
  | true =>
    have hfun : (fun k : ℕ => if (k ≠ 0) = true then zProb p k else 0) =
        fun k => if k = 0 then (0 : ℝ) else zProb p k := by
      funext k
      by_cases hk : k = 0 <;> simp [hk]
    have hsplit := summable_zProb.tsum_eq_add_tsum_ite (b := 0) (f := fun k => zProb p k)
    rw [zProb_tsum hp0 hp1, zProb_zero] at hsplit
    rw [hfun]
    have : ∑' k, (if k = 0 then (0 : ℝ) else zProb p k) = p := by linarith
    simpa [bern] using this

theorem seed_bit {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (y : Fin n → Bool) :
    ∑' z : Fin n → ℕ, (if ∀ t, (z t ≠ 0) = y t then seedProb p z else 0) = bernJoint p y := by
  induction n with
  | zero =>
    let z0 : Fin 0 → ℕ := fun t => Fin.elim0 t
    have honly : ∀ z : Fin 0 → ℕ, z = z0 := by intro z; ext t; exact Fin.elim0 t
    have hs : HasSum (fun z : Fin 0 → ℕ => if ∀ t, (z t ≠ 0) = y t then seedProb p z else 0)
        (seedProb p z0) :=
      hasSum_single z0 fun z hz => absurd (honly z) hz
    rw [hs.tsum_eq]
    simp [seedProb, bernJoint]
  | succ n ih =>
    let p0 := p 0
    let q := Fin.tail p
    have hq0 : ∀ t, 0 ≤ q t := fun t => hp0 t.succ
    have hq1 : ∀ t, q t ≤ 1 := fun t => hp1 t.succ
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
    let A : ℕ → ℝ := fun k => if (k ≠ 0) = y 0 then zProb p0 k else 0
    let B : (Fin n → ℕ) → ℝ := fun z =>
      if ∀ t, (z t ≠ 0) = y t.succ then seedProb q z else 0
    have hfac : ∀ a : ℕ × (Fin n → ℕ),
        (if ∀ t, ((e a) t ≠ 0) = y t then seedProb p (e a) else 0) = A a.1 * B a.2 := by
      intro a
      have hpcons : p = Fin.cons p0 q := by simp [p0, q, Fin.cons_self_tail]
      have he : e a = Fin.cons a.1 a.2 := rfl
      have hseed : seedProb p (e a) = zProb p0 a.1 * seedProb q a.2 := by
        rw [hpcons, he]; exact seedProb_cons p0 q a.1 a.2
      have hbits : (∀ t, ((e a) t ≠ 0) = y t) ↔
          (a.1 ≠ 0) = y 0 ∧ ∀ t : Fin n, (a.2 t ≠ 0) = y t.succ := by
        constructor
        · intro h
          exact ⟨by simpa [he] using h 0, fun t => by simpa [he] using h t.succ⟩
        · intro h t
          cases t using Fin.cases with
          | zero => simpa [he] using h.1
          | succ t => simpa [he] using h.2 t
      by_cases hA : (a.1 ≠ 0) = y 0
      · by_cases hB : ∀ t : Fin n, (a.2 t ≠ 0) = y t.succ
        · have hall : ∀ t, ((e a) t ≠ 0) = y t := hbits.mpr ⟨hA, hB⟩
          rw [if_pos hall, hseed]
          change zProb p0 a.1 * seedProb q a.2 =
            (if (a.1 ≠ 0) = y 0 then zProb p0 a.1 else 0) *
              (if ∀ t : Fin n, (a.2 t ≠ 0) = y t.succ then seedProb q a.2 else 0)
          rw [if_pos hA, if_pos hB]
        · have hnot : ¬ ∀ t, ((e a) t ≠ 0) = y t := fun h => hB (hbits.mp h).2
          rw [if_neg hnot]
          change (0 : ℝ) =
            (if (a.1 ≠ 0) = y 0 then zProb p0 a.1 else 0) *
              (if ∀ t : Fin n, (a.2 t ≠ 0) = y t.succ then seedProb q a.2 else 0)
          rw [if_pos hA, if_neg hB, mul_zero]
      · have hnot : ¬ ∀ t, ((e a) t ≠ 0) = y t := fun h => hA (hbits.mp h).1
        rw [if_neg hnot]
        change (0 : ℝ) =
          (if (a.1 ≠ 0) = y 0 then zProb p0 a.1 else 0) *
            (if ∀ t : Fin n, (a.2 t ≠ 0) = y t.succ then seedProb q a.2 else 0)
        rw [if_neg hA, zero_mul]
    have hAS : Summable A :=
      summable_zProb.of_nonneg_of_le
        (fun k => by
          dsimp [A]
          split_ifs
          · exact zProb_nonneg (hp0 0) (hp1 0) k
          · exact le_rfl)
        (fun k => by
          dsimp [A]
          split_ifs
          · exact le_rfl
          · exact zProb_nonneg (hp0 0) (hp1 0) k)
    have hBS : Summable B :=
      (seedProb_summable q hq0 hq1).of_nonneg_of_le
        (fun z => by
          dsimp [B]
          split_ifs
          · exact seedProb_nonneg hq0 hq1 z
          · exact le_rfl)
        (fun z => by
          dsimp [B]
          split_ifs
          · exact le_rfl
          · exact seedProb_nonneg hq0 hq1 z)
    have hAn : Summable fun k => ‖A k‖ :=
      summable_norm_of_nonneg _ (fun k => by
        dsimp [A]
        split_ifs
        · exact zProb_nonneg (hp0 0) (hp1 0) k
        · exact le_rfl) hAS
    have hBn : Summable fun z => ‖B z‖ :=
      summable_norm_of_nonneg _ (fun z => by
        dsimp [B]
        split_ifs
        · exact seedProb_nonneg hq0 hq1 z
        · exact le_rfl) hBS
    rw [← e.tsum_eq, tsum_congr hfac, (tsum_mul_tsum_of_summable_norm hAn hBn).symm]
    have hAsum : ∑' k, A k = bern p0 (y 0) := by
      simpa [A] using zProb_bit (hp0 0) (hp1 0) (y 0)
    have hBsum : ∑' z, B z = bernJoint q (fun t => y t.succ) := by
      simpa [B] using ih q hq0 hq1 (fun t => y t.succ)
    rw [hAsum, hBsum]
    unfold bernJoint
    rw [Fin.prod_univ_succ (fun t => bern (p t) (y t))]
    simp [p0, q, Fin.tail]

/-- A countable law together with a deterministic readout of the maximizing bits. -/
def IsMaxReadout {n : ℕ} {α : Type} (p : Fin n → ℝ) (μ : α → ℝ) (f : α → Fin n → Bool) : Prop :=
  (∀ a, 0 ≤ μ a) ∧ Summable μ ∧ (∑' a, μ a = 1) ∧ (∀ a, μ a ≤ 1) ∧
    Summable (fun a => shannonTerm (μ a)) ∧
    ∀ y, ∑' a, (if f a = y then μ a else 0) = bernJoint p y

/-- Least Shannon entropy of a countable readout of the independent Bernoulli vector. -/
def readoutCost (n : ℕ) (p : Fin n → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ (α : Type) (μ : α → ℝ) (f : α → Fin n → Bool),
    IsMaxReadout p μ f ∧ e = ∑' a, shannonTerm (μ a)}

theorem readout_lower {n : ℕ} {α : Type} (p : Fin n → ℝ) (μ : α → ℝ) (f : α → Fin n → Bool)
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) (h : IsMaxReadout p μ f) :
    ∑ t, h2 (p t) ≤ ∑' a, shannonTerm (μ a) := by
  rcases h with ⟨h0, hs, hsum, h1, hE, hex⟩
  have hpush := shannonTerm_push_le μ f h0 h1 hs hE hsum
  have hent : ∑ y, shannonTerm (bernJoint p y) = ∑ t, h2 (p t) := bernJoint_entropy p hp0 hp1
  have : ∑ y, shannonTerm (∑' a, if f a = y then μ a else 0) = ∑ t, h2 (p t) := by
    simp_rw [hex]
    exact hent
  linarith

theorem gate_is_readout {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 < p t) (hp1 : ∀ t, p t < 1) :
    IsMaxReadout p (seedProb p) (fun z t => decide (z t ≠ 0)) := by
  refine ⟨seedProb_nonneg (fun t => (hp0 t).le) (fun t => (hp1 t).le),
    seedProb_summable p (fun t => (hp0 t).le) (fun t => (hp1 t).le),
    seedProb_sum p (fun t => (hp0 t).le) (fun t => (hp1 t).le),
    seedProb_le_one (fun t => (hp0 t).le) (fun t => (hp1 t).le),
    (seed_entropy p hp0 hp1).1, ?_⟩
  intro y
  have hbit := seed_bit p (fun t => (hp0 t).le) (fun t => (hp1 t).le) y
  rw [← hbit]
  refine tsum_congr fun z => ?_
  have hiff : ((fun t => decide (z t ≠ 0)) = y) ↔ ∀ t, (z t ≠ 0) = y t := by
    constructor
    · intro h t
      have ht : decide (z t ≠ 0) = y t := congrFun h t
      by_cases h0 : z t = 0
      · have hdec : decide (z t ≠ 0) = false := by simp [h0]
        rw [hdec] at ht
        simp [h0, ht.symm]
      · have hdec : decide (z t ≠ 0) = true := by simp [h0]
        rw [hdec] at ht
        simp [h0, ht]
    · intro h
      funext t
      have ht : (z t ≠ 0) = y t := h t
      by_cases h0 : z t = 0
      · simp [h0] at ht
        simp [h0, ht]
      · simp [h0] at ht
        simp [h0, ht]
  by_cases hz : (fun t => decide (z t ≠ 0)) = y
  · rw [if_pos hz, if_pos (hiff.mp hz)]
  · rw [if_neg hz, if_neg (fun hall => hz (hiff.mpr hall))]

theorem activity_sandwich {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 < p t) (hp1 : ∀ t, p t < 1) :
    ∑ t, h2 (p t) ≤ readoutCost n p ∧
      readoutCost n p ≤ ∑ t, (h2 (p t) + 2 * p t) := by
  have hmem : (∑' z, shannonTerm (seedProb p z)) ∈
      {e | ∃ (α : Type) (μ : α → ℝ) (f : α → Fin n → Bool),
        IsMaxReadout p μ f ∧ e = ∑' a, shannonTerm (μ a)} := by
    refine ⟨Fin n → ℕ, seedProb p, fun z t => decide (z t ≠ 0), gate_is_readout p hp0 hp1, rfl⟩
  have hlow : ∀ e ∈ {e | ∃ (α : Type) (μ : α → ℝ) (f : α → Fin n → Bool),
      IsMaxReadout p μ f ∧ e = ∑' a, shannonTerm (μ a)}, ∑ t, h2 (p t) ≤ e := by
    intro e he
    rcases he with ⟨α, μ, f, h, rfl⟩
    exact readout_lower p μ f (fun t => (hp0 t).le) (fun t => (hp1 t).le) h
  have hbdd : BddBelow {e | ∃ (α : Type) (μ : α → ℝ) (f : α → Fin n → Bool),
      IsMaxReadout p μ f ∧ e = ∑' a, shannonTerm (μ a)} :=
    ⟨∑ t, h2 (p t), hlow⟩
  refine ⟨le_csInf ⟨_, hmem⟩ hlow, ?_⟩
  rw [readoutCost]
  exact (csInf_le hbdd hmem).trans_eq (seed_entropy p hp0 hp1).2

/-- No countable seed reproduces every finite maximizing transcript when `∑ p` diverges. -/
theorem no_countable_seed_of_divergent {α : Type} (p : ℕ → ℝ) (μ : α → ℝ) (f : α → ℕ → Bool)
    (hp : ∀ t, 0 < p t ∧ p t ≤ 1 / 2)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, p i) atTop atTop)
    (h0 : ∀ a, 0 ≤ μ a) (hs : Summable μ) (hsum : ∑' a, μ a = 1)
    (hex : ∀ n (y : Fin n → Bool),
      ∑' a, (if ∀ t : Fin n, f a t.val = y t then μ a else 0) =
        ∏ t, bern (p t.val) (y t)) : False := by
  classical
  have hpos : ∃ a, 0 < μ a := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ a, μ a = 0 := fun a => le_antisymm (hnone a) (h0 a)
    have : ∑' a, μ a = 0 := by simp [hzero]
    linarith
  obtain ⟨a0, ha0⟩ := hpos
  let y : ℕ → Bool := f a0
  have hpre : ∀ n, μ a0 ≤ ∏ t : Fin n, bern (p t.val) (y t.val) := by
    intro n
    have hmass := hex n (fun t => y t.val)
    let g : α → ℝ := fun a => if ∀ t : Fin n, f a t.val = y t.val then μ a else 0
    have hg0 : ∀ a, 0 ≤ g a := fun a => by
      dsimp [g]
      split_ifs with h
      · exact h0 a
      · exact le_rfl
    have hs' : Summable g :=
      hs.of_nonneg_of_le hg0 (fun a => by
        dsimp [g]
        split_ifs with h
        · exact le_rfl
        · exact h0 a)
    have hsplit := hs'.tsum_eq_add_tsum_ite a0
    have hga : g a0 = μ a0 := by simp [g, y]
    have hrest : 0 ≤ ∑' a, if a = a0 then (0 : ℝ) else g a :=
      tsum_nonneg fun a => by split_ifs <;> first | exact le_rfl | exact hg0 a
    rw [hga] at hsplit
    have hle : μ a0 ≤ ∑' a, g a := by linarith
    exact hle.trans_eq hmass
  have hle_prod : ∀ n, ∏ t : Fin n, bern (p t.val) (y t.val) ≤
      ∏ i ∈ Finset.range n, (1 - p i) := by
    intro n
    have hfin : ∏ t : Fin n, bern (p t.val) (y t.val) ≤ ∏ t : Fin n, (1 - p t.val) := by
      refine Finset.prod_le_prod₀ ?_ ?_
      · intro t _
        exact bern_nonneg (hp t.val).1.le (by linarith [(hp t.val).2]) (y t.val)
      · intro t _
        exact bern_le_one_sub (hp t.val).2 (y t.val)
    have hrange : ∏ t : Fin n, (1 - p t.val) = ∏ i ∈ Finset.range n, (1 - p i) :=
      Fin.prod_univ_eq_prod_range (fun i => 1 - p i) n
    exact hfin.trans (le_of_eq hrange)
  have hto : Tendsto (fun n => ∏ i ∈ Finset.range n, (1 - p i)) atTop (nhds 0) :=
    prod_one_sub_tendsto_zero (fun t => (hp t).1.le) (fun t => by linarith [(hp t).2]) hdiv
  rw [Metric.tendsto_atTop] at hto
  obtain ⟨N, hN⟩ := hto (μ a0) ha0
  have hdist := hN N le_rfl
  have hnn : 0 ≤ ∏ i ∈ Finset.range N, (1 - p i) :=
    Finset.prod_nonneg fun i _ => by linarith [(hp i).2]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hdist
  exact lt_irrefl _ (lt_of_le_of_lt (hpre N) (lt_of_le_of_lt (hle_prod N) hdist))

theorem exact_seed_ge_prefix {n : ℕ} {α : Type} (p : ℕ → ℝ) (μ : α → ℝ) (f : α → ℕ → Bool)
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (h0 : ∀ a, 0 ≤ μ a) (hs : Summable μ) (hsum : ∑' a, μ a = 1) (h1 : ∀ a, μ a ≤ 1)
    (hE : Summable fun a => shannonTerm (μ a))
    (hex : ∀ y : Fin n → Bool,
      ∑' a, (if (fun t : Fin n => f a t.val) = y then μ a else 0) =
        bernJoint (fun t : Fin n => p t.val) y) :
    ∑ t : Fin n, h2 (p t.val) ≤ ∑' a, shannonTerm (μ a) := by
  have hread : IsMaxReadout (fun t : Fin n => p t.val) μ (fun a t => f a t.val) :=
    ⟨h0, hs, hsum, h1, hE, hex⟩
  simpa using readout_lower (fun t : Fin n => p t.val) μ (fun a t => f a t.val)
    (fun t => hp0 t) (fun t => hp1 t) hread

theorem no_finite_entropy_of_divergent_h2 {α : Type} (p : ℕ → ℝ) (μ : α → ℝ) (f : α → ℕ → Bool)
    (hp : ∀ t, 0 ≤ p t ∧ p t ≤ 1)
    (hdiv : ¬ Summable fun t => h2 (p t))
    (h0 : ∀ a, 0 ≤ μ a) (hs : Summable μ) (hsum : ∑' a, μ a = 1) (h1 : ∀ a, μ a ≤ 1)
    (hE : Summable fun a => shannonTerm (μ a))
    (hex : ∀ n (y : Fin n → Bool),
      ∑' a, (if (fun t : Fin n => f a t.val) = y then μ a else 0) =
        bernJoint (fun t : Fin n => p t.val) y) :
    False := by
  have hbound : ∀ n, ∑ t ∈ Finset.range n, h2 (p t) ≤ ∑' a, shannonTerm (μ a) := by
    intro n
    have hfin : ∑ t : Fin n, h2 (p t.val) ≤ ∑' a, shannonTerm (μ a) :=
      exact_seed_ge_prefix p μ f (fun t => (hp t).1) (fun t => (hp t).2) h0 hs hsum h1 hE (hex n)
    rw [← Fin.sum_univ_eq_sum_range (fun i => h2 (p i)) n]
    exact hfin
  have hnonneg : ∀ t, 0 ≤ h2 (p t) := fun t => h2_nonneg (hp t).1 (hp t).2
  exact hdiv (summable_of_sum_range_le hnonneg hbound)

end Vanishing
end
