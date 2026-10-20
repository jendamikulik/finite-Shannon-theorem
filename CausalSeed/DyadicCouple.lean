/-
Dyadic laws and their comonotone common refinement.

A dyadic law is a list of levels `k` (atom mass `2^{-k}`) with payloads.
`couple`: for finitely many dyadic laws `L a` of total mass one there is one dyadic
law `R` whose atoms carry a payload for every `a`, such that (i) the payload map to
each `L a` is measure preserving, and (ii) the information CDF of `R` is at least
`min_a` of the information CDFs of the `L a`.  This is the refinement criterion and
the minimum-CDF lemma for dyadic laws, proved by repeated halving of sorted lists.
-/
import CausalSeed.Spectrum

noncomputable section
open Classical
namespace CausalSpectrum.Dyadic

/-- Mass `2^{-k}` of a level-`k` atom. -/
abbrev wt (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem wt_pos (k : ℕ) : 0 < wt k := by positivity

theorem wt_succ (k : ℕ) : wt (k + 1) = wt k / 2 := by simp [wt, pow_succ]; ring

section lists
variable {β : Type}

/-- `E_L g = ∑ 2^{-k} g(x)`. -/
def massL (L : List (ℕ × β)) (g : β → ℝ) : ℝ := (L.map fun m => wt m.1 * g m.2).sum

/-- Information CDF `∑ [k ≤ t] 2^{-k}`. -/
def cdfL (L : List (ℕ × β)) (t : ℝ) : ℝ :=
  (L.map fun m => if (m.1 : ℝ) ≤ t then wt m.1 else 0).sum

@[simp] theorem massL_nil (g : β → ℝ) : massL ([] : List (ℕ × β)) g = 0 := rfl
@[simp] theorem massL_cons (m : ℕ × β) (L : List (ℕ × β)) (g : β → ℝ) :
    massL (m :: L) g = wt m.1 * g m.2 + massL L g := by simp [massL]
@[simp] theorem cdfL_nil (t : ℝ) : cdfL ([] : List (ℕ × β)) t = 0 := rfl
@[simp] theorem cdfL_cons (m : ℕ × β) (L : List (ℕ × β)) (t : ℝ) :
    cdfL (m :: L) t = (if (m.1 : ℝ) ≤ t then wt m.1 else 0) + cdfL L t := by simp [cdfL]

theorem massL_append (L L' : List (ℕ × β)) (g : β → ℝ) :
    massL (L ++ L') g = massL L g + massL L' g := by simp [massL]
theorem cdfL_append (L L' : List (ℕ × β)) (t : ℝ) :
    cdfL (L ++ L') t = cdfL L t + cdfL L' t := by simp [cdfL]

theorem massL_perm {L L' : List (ℕ × β)} (h : L.Perm L') (g : β → ℝ) :
    massL L g = massL L' g := (h.map _).sum_eq
theorem cdfL_perm {L L' : List (ℕ × β)} (h : L.Perm L') (t : ℝ) :
    cdfL L t = cdfL L' t := (h.map _).sum_eq

theorem cdfL_nonneg (L : List (ℕ × β)) (t : ℝ) : 0 ≤ cdfL L t := by
  induction L with
  | nil => simp
  | cons m L ih => rw [cdfL_cons]; have := wt_pos m.1; split_ifs <;> linarith

theorem massL_one_nonneg (L : List (ℕ × β)) : 0 ≤ massL L (fun _ => 1) := by
  induction L with
  | nil => simp
  | cons m L ih => rw [massL_cons]; have := wt_pos m.1; linarith

theorem cdfL_le_mass (L : List (ℕ × β)) (t : ℝ) : cdfL L t ≤ massL L (fun _ => 1) := by
  induction L with
  | nil => simp
  | cons m L ih => rw [cdfL_cons, massL_cons]; have := wt_pos m.1; split_ifs <;> linarith

theorem cdfL_eq_mass {L : List (ℕ × β)} {t : ℝ} (h : ∀ m ∈ L, (m.1 : ℝ) ≤ t) :
    cdfL L t = massL L (fun _ => 1) := by
  induction L with
  | nil => simp
  | cons m L ih =>
    rw [cdfL_cons, massL_cons, if_pos (h m (by simp)), ih fun x hx => h x (by simp [hx])]
    ring

theorem cdfL_eq_zero {L : List (ℕ × β)} {t : ℝ} (h : ∀ m ∈ L, t < (m.1 : ℝ)) :
    cdfL L t = 0 := by
  induction L with
  | nil => simp
  | cons m L ih =>
    rw [cdfL_cons, if_neg (not_le.mpr (h m (by simp))), ih fun x hx => h x (by simp [hx])]
    ring

theorem eq_nil_of_mass_zero {L : List (ℕ × β)} (h : massL L (fun _ => 1) = 0) : L = [] := by
  cases L with
  | nil => rfl
  | cons m L =>
    rw [massL_cons] at h
    have := wt_pos m.1; have := massL_one_nonneg L; linarith

theorem eq_single {L : List (ℕ × β)} (h1 : massL L (fun _ => 1) = 1) {m : ℕ × β}
    (hm : m ∈ L) (h0 : m.1 = 0) : L = [m] := by
  have hp := List.perm_cons_erase hm
  have := massL_perm hp (fun _ => 1)
  rw [massL_cons, h0, h1] at this
  simp only [wt, pow_zero, mul_one] at this
  have he : L.erase m = [] := eq_nil_of_mass_zero (by linarith)
  rw [he] at hp
  exact List.perm_singleton.mp hp

/-- Shift levels down by one. -/
def dec (L : List (ℕ × β)) : List (ℕ × β) := L.map fun m => (m.1 - 1, m.2)
/-- Shift levels up by one. -/
def inc (L : List (ℕ × β)) : List (ℕ × β) := L.map fun m => (m.1 + 1, m.2)

theorem massL_dec {L : List (ℕ × β)} (h : ∀ m ∈ L, 1 ≤ m.1) (g : β → ℝ) :
    massL (dec L) g = 2 * massL L g := by
  induction L with
  | nil => simp [dec]
  | cons m L ih =>
    have hm := h m (by simp)
    have ih' := ih fun x hx => h x (by simp [hx])
    simp only [dec, List.map_cons, massL_cons] at ih' ⊢
    rw [ih']
    obtain ⟨k, hk⟩ : ∃ k, m.1 = k + 1 := ⟨m.1 - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, wt_succ]; ring

theorem cdfL_dec {L : List (ℕ × β)} (h : ∀ m ∈ L, 1 ≤ m.1) (t : ℝ) :
    cdfL (dec L) (t - 1) = 2 * cdfL L t := by
  induction L with
  | nil => simp [dec]
  | cons m L ih =>
    have hm := h m (by simp)
    have ih' := ih fun x hx => h x (by simp [hx])
    simp only [dec, List.map_cons, cdfL_cons] at ih' ⊢
    rw [ih']
    obtain ⟨k, hk⟩ : ∃ k, m.1 = k + 1 := ⟨m.1 - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, wt_succ]
    push_cast
    by_cases ht : (k : ℝ) + 1 ≤ t
    · rw [if_pos (by linarith), if_pos ht]; ring
    · rw [if_neg (by linarith), if_neg ht]; ring

theorem massL_inc (L : List (ℕ × β)) (g : β → ℝ) : massL (inc L) g = massL L g / 2 := by
  induction L with
  | nil => simp [inc]
  | cons m L ih =>
    simp only [inc, List.map_cons, massL_cons] at ih ⊢
    rw [ih, wt_succ]; ring

theorem cdfL_inc (L : List (ℕ × β)) (t : ℝ) : cdfL (inc L) t = cdfL L (t - 1) / 2 := by
  induction L with
  | nil => simp [inc]
  | cons m L ih =>
    simp only [inc, List.map_cons, cdfL_cons] at ih ⊢
    rw [ih, wt_succ]
    push_cast
    by_cases ht : (m.1 : ℝ) + 1 ≤ t
    · rw [if_pos ht, if_pos (by linarith)]; ring
    · rw [if_neg ht, if_neg (by linarith)]; ring

/-- Split level-0 atoms into two level-1 atoms. -/
def spl (L : List (ℕ × β)) : List (ℕ × β) :=
  L.flatMap fun m => if m.1 = 0 then [(1, m.2), (1, m.2)] else [m]

theorem spl_cons (m : ℕ × β) (L : List (ℕ × β)) :
    spl (m :: L) = (if m.1 = 0 then [(1, m.2), (1, m.2)] else [m]) ++ spl L := by
  simp [spl]

theorem massL_spl (L : List (ℕ × β)) (g : β → ℝ) : massL (spl L) g = massL L g := by
  induction L with
  | nil => simp [spl]
  | cons m L ih =>
    rw [spl_cons, massL_append, ih, massL_cons]
    split_ifs with h
    · simp [h, wt]; ring
    · simp

theorem cdfL_spl (L : List (ℕ × β)) {t : ℝ} (ht : 1 ≤ t) : cdfL (spl L) t = cdfL L t := by
  induction L with
  | nil => simp [spl]
  | cons m L ih =>
    rw [spl_cons, cdfL_append, ih, cdfL_cons]
    by_cases h : m.1 = 0
    · rw [if_pos h]
      simp [h, wt, ht, show (0:ℝ) ≤ t by linarith]; ring
    · rw [if_neg h]; simp

theorem spl_levels {L : List (ℕ × β)} {N : ℕ} (h : ∀ m ∈ L, m.1 ≤ N + 1) :
    ∀ m ∈ spl L, 1 ≤ m.1 ∧ m.1 ≤ N + 1 := by
  intro m hm
  simp only [spl, List.mem_flatMap] at hm
  obtain ⟨x, hx, hmx⟩ := hm
  have := h x hx
  split_ifs at hmx with h0
  · simp at hmx; rcases hmx with rfl | rfl <;> simp <;> omega
  · simp at hmx; subst hmx; omega

/-- Ordering by level. -/
def byLevel (p q : ℕ × β) : Bool := decide (p.1 ≤ q.1)

/-- A prefix of a level-sorted list with mass exactly `2^{-m}`. -/
theorem exists_prefix : ∀ (D m : ℕ) (L : List (ℕ × β)),
    (∀ x ∈ L, m ≤ x.1 ∧ x.1 ≤ m + D) → L.Pairwise (fun p q => p.1 ≤ q.1) →
    wt m ≤ massL L (fun _ => 1) → ∃ j, massL (L.take j) (fun _ => 1) = wt m := by
  intro D
  induction D with
  | zero =>
    intro m L hl _ hm
    cases L with
    | nil => simp at hm; exact absurd hm (not_le.mpr (wt_pos m))
    | cons x rest =>
      have := hl x (by simp)
      refine ⟨1, ?_⟩
      simp [show x.1 = m by omega]
  | succ D ih =>
    intro m L hl hs hm
    cases L with
    | nil => simp at hm; exact absurd hm (not_le.mpr (wt_pos m))
    | cons x rest =>
      by_cases hx : x.1 = m
      · exact ⟨1, by simp [hx]⟩
      have hx1 := hl x (by simp)
      have hall : ∀ y ∈ x :: rest, m + 1 ≤ y.1 ∧ y.1 ≤ (m + 1) + D := by
        intro y hy
        have := hl y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · omega
        · have := List.rel_of_pairwise_cons hs hy'; omega
      have hm1 : wt (m + 1) ≤ massL (x :: rest) (fun _ => 1) := by
        rw [wt_succ]; have := wt_pos m; linarith
      obtain ⟨j1, hj1⟩ := ih (m + 1) _ hall hs hm1
      set L := x :: rest
      have hsplit := massL_append (L.take j1) (L.drop j1) (fun _ => 1)
      rw [List.take_append_drop] at hsplit
      have hd : wt (m + 1) ≤ massL (L.drop j1) (fun _ => 1) := by
        rw [wt_succ] at hj1 ⊢; linarith
      obtain ⟨j2, hj2⟩ := ih (m + 1) (L.drop j1)
        (fun y hy => hall y (List.mem_of_mem_drop hy)) (hs.sublist (List.drop_sublist _ _)) hd
      refine ⟨j1 + j2, ?_⟩
      rw [List.take_add, massL_append, hj1, hj2, wt_succ]; ring

end lists

section couple
variable {A : Type} [Fintype A] [Nonempty A] {β : A → Type}

theorem univ_ne : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty

/-- The coupling property. -/
def Couples (L : ∀ a, List (ℕ × β a)) (R : List (ℕ × ∀ a, β a)) : Prop :=
  (∀ a (g : β a → ℝ), massL R (fun p => g (p a)) = massL (L a) g) ∧
    ∀ t : ℝ, Finset.univ.inf' univ_ne (fun a => cdfL (L a) t) ≤ cdfL R t

theorem couple_single (L : ∀ a, List (ℕ × β a)) (h1 : ∀ a, massL (L a) (fun _ => 1) = 1)
    (hB : ∀ a, ∃ m ∈ L a, m.1 = 0) : ∃ R, Couples L R := by
  choose m hm h0 using hB
  have hL : ∀ a, L a = [m a] := fun a => eq_single (h1 a) (hm a) (h0 a)
  refine ⟨[(0, fun a => (m a).2)], fun a g => ?_, fun t => ?_⟩
  · rw [hL a]; simp [h0 a]
  · obtain ⟨a⟩ := (inferInstance : Nonempty A)
    refine (Finset.inf'_le _ (Finset.mem_univ a)).trans (le_of_eq ?_)
    rw [hL a]; simp [h0 a]

/-- **Comonotone dyadic refinement.** -/
theorem couple : ∀ (N : ℕ) (L : ∀ a, List (ℕ × β a)),
    (∀ a, ∀ m ∈ L a, m.1 ≤ N) → (∀ a, massL (L a) (fun _ => 1) = 1) → ∃ R, Couples L R := by
  intro N
  induction N with
  | zero =>
    intro L hN h1
    refine couple_single L h1 fun a => ?_
    cases hLa : L a with
    | nil => have := h1 a; rw [hLa] at this; simp at this
    | cons x rest => exact ⟨x, by simp, by have := hN a x (by rw [hLa]; simp); omega⟩
  | succ N ih =>
    intro L hN h1
    by_cases hB : ∀ a, ∃ m ∈ L a, m.1 = 0
    · exact couple_single L h1 hB
    push_neg at hB
    obtain ⟨a1, ha1⟩ := hB
    -- sort the split lists and halve them
    let S : ∀ a, List (ℕ × β a) := fun a => (spl (L a)).mergeSort byLevel
    have hSperm : ∀ a, (S a).Perm (spl (L a)) := fun a => List.mergeSort_perm _ _
    have hSlev : ∀ a, ∀ x ∈ S a, 1 ≤ x.1 ∧ x.1 ≤ N + 1 := fun a x hx =>
      spl_levels (hN a) x ((hSperm a).mem_iff.mp hx)
    have hSsort : ∀ a, (S a).Pairwise (fun p q => p.1 ≤ q.1) := by
      intro a
      have := List.pairwise_mergeSort (le := byLevel (β := β a))
        (fun p q r hpq hqr => by simp [byLevel] at *; omega)
        (fun p q => by simp [byLevel]; omega) (spl (L a))
      exact this.imp fun h => by simpa [byLevel] using h
    have hSmass : ∀ a (g : β a → ℝ), massL (S a) g = massL (L a) g := fun a g => by
      rw [massL_perm (hSperm a), massL_spl]
    have hhalf : ∀ a, ∃ j, massL ((S a).take j) (fun _ => 1) = wt 1 := fun a =>
      exists_prefix N 1 (S a) (fun x hx => by have := hSlev a x hx; omega) (hSsort a)
        (by rw [hSmass, h1]; simp [wt]; norm_num)
    choose j hj using hhalf
    let P : ∀ a, List (ℕ × β a) := fun a => (S a).take (j a)
    let Q : ∀ a, List (ℕ × β a) := fun a => (S a).drop (j a)
    have hPQ : ∀ a, P a ++ Q a = S a := fun a => List.take_append_drop _ _
    have hPlev : ∀ a, ∀ x ∈ P a, 1 ≤ x.1 ∧ x.1 ≤ N + 1 := fun a x hx =>
      hSlev a x (List.mem_of_mem_take hx)
    have hQlev : ∀ a, ∀ x ∈ Q a, 1 ≤ x.1 ∧ x.1 ≤ N + 1 := fun a x hx =>
      hSlev a x (List.mem_of_mem_drop hx)
    have hPm : ∀ a, massL (P a) (fun _ => 1) = 1 / 2 := fun a => by rw [hj a]; simp [wt]
    have hQm : ∀ a, massL (Q a) (fun _ => 1) = 1 / 2 := fun a => by
      have := massL_append (P a) (Q a) (fun _ => 1)
      rw [hPQ, hSmass, h1, hPm] at this; linarith
    have hcross : ∀ a, ∀ p ∈ P a, ∀ q ∈ Q a, p.1 ≤ q.1 := fun a => by
      have := hSsort a
      rw [← hPQ a, List.pairwise_append] at this
      exact this.2.2
    have hdecP : ∀ a, ∀ m ∈ dec (P a), m.1 ≤ N := fun a m hm => by
      simp only [dec, List.mem_map] at hm
      obtain ⟨x, hx, rfl⟩ := hm; have := hPlev a x hx; simp; omega
    have hdecQ : ∀ a, ∀ m ∈ dec (Q a), m.1 ≤ N := fun a m hm => by
      simp only [dec, List.mem_map] at hm
      obtain ⟨x, hx, rfl⟩ := hm; have := hQlev a x hx; simp; omega
    obtain ⟨R1, hR1m, hR1c⟩ := ih (fun a => dec (P a)) hdecP fun a => by
      rw [massL_dec (fun x hx => (hPlev a x hx).1), hPm]; norm_num
    obtain ⟨R2, hR2m, hR2c⟩ := ih (fun a => dec (Q a)) hdecQ fun a => by
      rw [massL_dec (fun x hx => (hQlev a x hx).1), hQm]; norm_num
    refine ⟨inc (R1 ++ R2), fun a g => ?_, fun t => ?_⟩
    · rw [massL_inc, massL_append, hR1m, hR2m, massL_dec (fun x hx => (hPlev a x hx).1),
        massL_dec (fun x hx => (hQlev a x hx).1), ← hSmass a g, ← hPQ a, massL_append]
      ring
    · by_cases ht : t < 1
      · refine (Finset.inf'_le _ (Finset.mem_univ a1)).trans ?_
        rw [cdfL_eq_zero (fun m hm => ?_)]
        · exact cdfL_nonneg _ _
        · have : m.1 ≠ 0 := ha1 m hm
          have : (1:ℝ) ≤ m.1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
          linarith
      push_neg at ht
      -- per-action half CDFs
      have hF : ∀ a, cdfL (L a) t = cdfL (P a) t + cdfL (Q a) t := fun a => by
        rw [← cdfL_append, hPQ, cdfL_perm (hSperm a), cdfL_spl _ ht]
      have hPmin : ∀ a, cdfL (P a) t = min (1 / 2) (cdfL (L a) t) := fun a => by
        by_cases hall : ∀ p ∈ P a, (p.1 : ℝ) ≤ t
        · have hp := cdfL_eq_mass hall
          rw [hPm] at hp
          rw [hp, hF, hp]
          have := cdfL_nonneg (Q a) t
          rw [min_eq_left (by linarith)]
        · push_neg at hall
          obtain ⟨p, hp, hpt⟩ := hall
          have hq : cdfL (Q a) t = 0 := cdfL_eq_zero fun q hq =>
            lt_of_lt_of_le hpt (by exact_mod_cast hcross a p hp q hq)
          have := cdfL_le_mass (P a) t
          rw [hPm] at this
          rw [hF, hq, add_zero, min_eq_right this]
      set Fm := Finset.univ.inf' univ_ne (fun a => cdfL (L a) t)
      have hle : ∀ a, Fm ≤ cdfL (L a) t := fun a => Finset.inf'_le _ (Finset.mem_univ a)
      have h1' : min (1 / 2) Fm ≤ cdfL R1 (t - 1) / 2 := by
        have := hR1c (t - 1)
        have hlow : min (1 / 2) Fm * 2 ≤ Finset.univ.inf' univ_ne
            (fun a => cdfL (dec (P a)) (t - 1)) := by
          refine Finset.le_inf' _ _ fun a _ => ?_
          rw [cdfL_dec (fun x hx => (hPlev a x hx).1), hPmin]
          have := min_le_min_left (1 / 2 : ℝ) (hle a); linarith
        linarith
      have h2' : max 0 (Fm - 1 / 2) ≤ cdfL R2 (t - 1) / 2 := by
        have := hR2c (t - 1)
        have hlow : max 0 (Fm - 1 / 2) * 2 ≤ Finset.univ.inf' univ_ne
            (fun a => cdfL (dec (Q a)) (t - 1)) := by
          refine Finset.le_inf' _ _ fun a _ => ?_
          rw [cdfL_dec (fun x hx => (hQlev a x hx).1)]
          have hq : cdfL (Q a) t = cdfL (L a) t - min (1 / 2) (cdfL (L a) t) := by
            rw [← hPmin, hF]; ring
          rw [hq]
          have := hle a
          have h0 : 0 ≤ cdfL (L a) t - min (1 / 2) (cdfL (L a) t) := by
            have := min_le_right (1 / 2 : ℝ) (cdfL (L a) t); linarith
          have h3 : Fm - 1 / 2 ≤ cdfL (L a) t - min (1 / 2) (cdfL (L a) t) := by
            have := min_le_left (1 / 2 : ℝ) (cdfL (L a) t); linarith
          have := max_le h0 h3; linarith
        linarith
      rw [cdfL_inc, cdfL_append]
      have hsum : Fm = min (1 / 2) Fm + max 0 (Fm - 1 / 2) := by
        rcases le_total Fm (1 / 2) with h | h
        · rw [min_eq_right h, max_eq_left (by linarith)]; ring
        · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      linarith

end couple
end CausalSpectrum.Dyadic
