/-
Principia GoldenSphere, souhrnné vydání, 19. listopadu 2026.

Část I je dopis a sféra. Sféry jsou v `GoldenSphere.lean`.
Tento soubor formalizuje části II a III: Eulerův horizont účtu
a paměť po návratu.

Dokázáno, bez `sorry`:

* plný obrat vrátí fázi a přesto má nenulovou vnitřní cenu;
* `e^{i·0} = 1` a rozšířený účet na vlákně projekce se nemění;
* nabídka se záznamem se promítá na původní `G` a je neprázdná
  právě tehdy, když existuje svědek;
* diagonální vývoj mlčí na sterilním směru, záměna ne;
* stejná aktivní odpověď nerozliší uložený bit;
* po známé otázce je počet zpráv transverzála;
* na trojici dvojic je transverzála 2 a žádný bod nestačí;
* před otázkou INDEX potřebuje všechna různá slova, po ní jeden bit;
* jeden vektor odpovědí pokryje `2^n` z `3^n` historií, tedy
  `Mₙ · 2ⁿ ≥ 3ⁿ`, a `M₁ = 2`;
* uzavřená rodina drží historii ve své buňce.

Není dokázáno: náhodný horní odhad `(3/2)ⁿ (n ln 3 + 1)`,
existence sterilního neutrina, Hypotéza 9, láska jako operátor,
vědomí, poloha nul `ξ`.
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import CausalSeed.GoldenSphere

noncomputable section

open Real Finset

namespace CausalSpectrum
namespace Collecta

/-! ### Fáze a účet -/

theorem full_turn (θ : ℝ) :
    Complex.exp ((θ + 2 * π) * Complex.I) = Complex.exp (θ * Complex.I) := by
  have hpi : Complex.exp (π * Complex.I) = -1 := Complex.exp_pi_mul_I
  have h2 : Complex.exp (2 * (π : ℂ) * Complex.I) = 1 := by
    calc
      Complex.exp (2 * (π : ℂ) * Complex.I)
          = Complex.exp (π * Complex.I + π * Complex.I) := by ring_nf
      _ = Complex.exp (π * Complex.I) * Complex.exp (π * Complex.I) :=
          Complex.exp_add _ _
      _ = 1 := by simp [hpi]
  calc
    Complex.exp ((θ + 2 * π) * Complex.I)
        = Complex.exp (θ * Complex.I + 2 * (π : ℂ) * Complex.I) := by
          congr 1
          ring
    _ = Complex.exp (θ * Complex.I) * Complex.exp (2 * (π : ℂ) * Complex.I) := by
          rw [Complex.exp_add]
    _ = Complex.exp (θ * Complex.I) := by simp [h2]

def pathCost (δ : ℝ) : ℝ := |δ|

theorem full_turn_still_costs :
    Complex.exp ((0 + 2 * Real.pi) * Complex.I) =
        Complex.exp ((0 : ℝ) * Complex.I) ∧
      pathCost (2 * Real.pi) ≠ 0 := by
  refine ⟨full_turn 0, ?_⟩
  have hpos : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
  rw [pathCost, abs_of_pos hpos]
  exact hpos.ne'

theorem exp_zero_is_one : Complex.exp ((0 : ℝ) * Complex.I) = 1 := by
  simp

def extendAccount {X S : Type*} (c : X → ℝ) : X × S → ℝ := fun p => c p.1

theorem fibre_is_free {X S : Type*} (c : X → ℝ) (x : X) (s s' : S) :
    extendAccount c (x, s') - extendAccount c (x, s) = 0 := by
  simp [extendAccount]

/-! ### Nabídka se záznamem -/

variable {X Ω W N Sx : Type*}

def AK (S : GoldenSphere.Sphere X Ω W N) (w : W) (x : X) : Set Ω :=
  { a | a ∈ GoldenSphere.admissible S w x ∧ S.F x a ∈ S.K }

def Gb (S : GoldenSphere.Sphere X Ω W N) (M : X → Sx → Ω → Sx)
    (w : W) (x : X) (s : Sx) : Set (X × Sx) :=
  { p | ∃ a, a ∈ AK S w x ∧ p = (S.F x a, M x s a) }

theorem proj_Gb (S : GoldenSphere.Sphere X Ω W N) (M : X → Sx → Ω → Sx)
    (w : W) (x : X) (s : Sx) :
    Prod.fst '' Gb S M w x s = GoldenSphere.G S w x := by
  ext y
  constructor
  · rintro ⟨p, ⟨a, ha, hp⟩, hfst⟩
    obtain rfl := hp
    have hy : S.F x a = y := by simpa using hfst
    subst hy
    exact ⟨a, ha.1, rfl, ha.2⟩
  · rintro ⟨a, ha, rfl, hk⟩
    exact ⟨(S.F x a, M x s a), ⟨a, ⟨ha, hk⟩, rfl⟩, rfl⟩

theorem Gb_nonempty_iff (S : GoldenSphere.Sphere X Ω W N) (M : X → Sx → Ω → Sx)
    (w : W) (x : X) (s : Sx) :
    (Gb S M w x s).Nonempty ↔ (AK S w x).Nonempty := by
  constructor
  · rintro ⟨_, a, ha, _⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨(S.F x a, M x s a), a, ha, rfl⟩

theorem hearing_keeps_account {X Sx : Type*} (c : X → ℝ) (x : X) (s s' : Sx) :
    extendAccount c (x, s') = extendAccount c (x, s) := by
  simp [extendAccount]

/-! ### Ortogonální směr -/

def Uθ (θ : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (Complex.exp (θ * Complex.I) * v.1, v.2)

def Pa (v : ℂ × ℂ) : ℂ × ℂ := (v.1, 0)

theorem diagonal_silent (θ : ℝ) (v : ℂ × ℂ) (hv : v.1 = 0) :
    (Pa (Uθ θ v)).1 = 0 := by
  simp [Pa, Uθ, hv]

def swapV (v : ℂ × ℂ) : ℂ × ℂ := (v.2, v.1)

theorem swap_not_silent :
    Pa ((0 : ℂ), 1) = Pa (0, 0) ∧
      Pa (swapV ((0 : ℂ), 1)) ≠ Pa (swapV (0, 0)) := by
  constructor
  · simp [Pa]
  · simp [Pa, swapV]

/-! ### Jeden vstup, dvě čtení -/

def activeAnswer {X : Type*} : X × Fin 2 → X := Prod.fst

theorem same_answer_two_bits {X : Type*} (x : X) :
    activeAnswer (x, (0 : Fin 2)) = activeAnswer (x, 1) ∧
      ((x, (0 : Fin 2)) : X × Fin 2) ≠ (x, 1) := by
  constructor
  · rfl
  · intro h
    have := congrArg Prod.snd h
    simp at this

theorem answer_cannot_split {X Z : Type*} (x : X) (g : X → Z) :
    g (activeAnswer (x, (0 : Fin 2))) = g (activeAnswer (x, 1)) := rfl

/-! ### Transverzála -/

def hitting {α : Type*} (T : Set α) (family : Set (Set α)) : Prop :=
  ∀ E ∈ family, (T ∩ E).Nonempty

theorem message_iff {α : Type*} (T : Set α) (family : Set (Set α)) :
    hitting T family ↔ ∀ E ∈ family, ∃ a, a ∈ T ∧ a ∈ E := by
  simp [hitting, Set.Nonempty, Set.mem_inter_iff]

def pairEdges : Finset (Finset (Fin 3)) :=
  { {0, 1}, {0, 2}, {1, 2} }

theorem pairs_need_two :
    (∀ e ∈ pairEdges, (({0, 1} : Finset (Fin 3)) ∩ e).Nonempty) ∧
      ∀ x : Fin 3, ∃ e ∈ pairEdges, x ∉ e := by
  constructor
  · decide
  · intro x
    fin_cases x
    · exact ⟨{1, 2}, by decide, by decide⟩
    · exact ⟨{0, 2}, by decide, by decide⟩
    · exact ⟨{0, 1}, by decide, by decide⟩

/-! ### INDEX -/

theorem one_bit_after {n : ℕ} (i : Fin n) (b : Fin 2) :
    ∃ h' : Fin n → Fin 2, h' i ≠ b := by
  refine ⟨fun j => if j = i then 1 - b else 0, ?_⟩
  intro hEq
  have hb : (1 - b : Fin 2) = b := by simpa using hEq
  fin_cases b <;> simp at hb

theorem index_before_injective {n Mem : Type*}
    (mem : (n → Fin 2) → Mem) (ans : Mem → n → Fin 2)
    (h : ∀ w i, ans (mem w) i = w i) :
    Function.Injective mem := by
  intro w w' hw
  funext i
  have h1 := h w i
  have h2 := h w' i
  rw [hw] at h1
  exact h1.symm.trans h2

theorem index_identity_works {n : Type*} :
    Function.Injective (fun w : n → Fin 2 => w) :=
  Function.injective_id

/-! ### Pokrytí historií -/

def covers {n : ℕ} (a b : Fin n → Fin 3) : Prop :=
  ∀ i, a i ≠ b i

lemma card_excluded (a : Fin 3) :
    Fintype.card { x : Fin 3 // x ≠ a } = 2 := by
  fin_cases a <;> simp

section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma card_one_vector {n : ℕ} (a : Fin n → Fin 3) :
    Fintype.card { b : Fin n → Fin 3 // covers a b } = 2 ^ n := by
  have hcong : Fintype.card { b : Fin n → Fin 3 // covers a b } =
      Fintype.card (∀ i : Fin n, { x : Fin 3 // x ≠ a i }) := by
    refine Fintype.card_congr ?_
    exact {
      toFun := fun b i => ⟨b.1 i, (b.2 i).symm⟩
      invFun := fun f => ⟨fun i => (f i).1, fun i => (f i).2.symm⟩
      left_inv := by intro _; rfl
      right_inv := by intro _; rfl
    }
  rw [hcong, Fintype.card_pi]
  simp only [card_excluded, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma card_one_vector_finset {n : ℕ} (a : Fin n → Fin 3) :
    ((univ : Finset (Fin n → Fin 3)).filter fun b => covers a b).card = 2 ^ n := by
  simpa [Fintype.card_subtype] using card_one_vector a

theorem cover_lower {n : ℕ} (T : Finset (Fin n → Fin 3))
    (hT : ∀ b : Fin n → Fin 3, ∃ a ∈ T, covers a b) :
    2 ^ n * T.card ≥ 3 ^ n := by
  let cover (a : Fin n → Fin 3) : Finset (Fin n → Fin 3) :=
    univ.filter fun b => covers a b
  have hsub : (univ : Finset (Fin n → Fin 3)) ⊆ T.biUnion cover := by
    intro b _
    obtain ⟨a, ha, hc⟩ := hT b
    exact mem_biUnion.mpr ⟨a, ha, by simpa [cover] using hc⟩
  have hcard : (univ : Finset (Fin n → Fin 3)).card = 3 ^ n := by
    simp [Fintype.card_fin]
  have hineq : (univ : Finset (Fin n → Fin 3)).card ≤ (T.biUnion cover).card :=
    card_le_card hsub
  have hunion : (T.biUnion cover).card ≤ ∑ a ∈ T, (cover a).card :=
    card_biUnion_le
  have hsum : ∑ a ∈ T, (cover a).card = T.card * 2 ^ n := by
    have : ∀ a ∈ T, (cover a).card = 2 ^ n := fun a _ => by
      simpa [cover] using card_one_vector_finset a
    rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.nsmul_eq_mul]
  have : 3 ^ n ≤ T.card * 2 ^ n := by
    calc
      3 ^ n = (univ : Finset (Fin n → Fin 3)).card := hcard.symm
      _ ≤ (T.biUnion cover).card := hineq
      _ ≤ ∑ a ∈ T, (cover a).card := hunion
      _ = T.card * 2 ^ n := hsum
  simpa [Nat.mul_comm] using this

theorem M1_eq_two :
    (∃ T : Finset (Fin 1 → Fin 3), T.card = 2 ∧ ∀ b, ∃ a ∈ T, covers a b) ∧
      ∀ T : Finset (Fin 1 → Fin 3), (∀ b, ∃ a ∈ T, covers a b) → 2 ≤ T.card := by
  constructor
  · let a0 : Fin 1 → Fin 3 := fun _ => 0
    let a1 : Fin 1 → Fin 3 := fun _ => 1
    have hne : a0 ∉ ({a1} : Finset (Fin 1 → Fin 3)) := by
      intro h
      have := congrFun (Finset.mem_singleton.mp h) 0
      simp [a0, a1] at this
    refine ⟨{a0, a1}, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]
    · intro b
      match hb : b 0 with
      | 0 =>
        exact ⟨a1, by simp [a0, a1], by
          intro i
          fin_cases i
          simp [a1, hb]⟩
      | 1 =>
        exact ⟨a0, by simp [a0, a1], by
          intro i
          fin_cases i
          simp [a0, hb]⟩
      | 2 =>
        exact ⟨a0, by simp [a0, a1], by
          intro i
          fin_cases i
          simp [a0, hb]⟩
  · intro T hT
    have h := cover_lower T hT
    omega

end

/-! ### Uzavřená rodina -/

variable {H E : Type*}

def path (stepH : E → H → Option H) : List E → H → Option H
  | [], h => some h
  | e :: es, h => (stepH e h).bind (path stepH es)

def foldMem {Mem : Type*} (next : Mem → E → Mem) : Mem → List E → Mem
  | m, [] => m
  | m, e :: es => foldMem next (next m e) es

structure ClosedFamily (Mem : Type*) (stepH : E → H → Option H)
    (H0 : Set H) (Q Ω : Type*) (A : Q → H → Set Ω) where
  C : Mem → Set H
  init : Mem
  init_covers : H0 ⊆ C init
  answer : Mem → Q → Ω
  answer_safe : ∀ m q h, h ∈ C m → answer m q ∈ A q h
  next : Mem → E → Mem
  next_closed : ∀ m e h h', h ∈ C m → stepH e h = some h' → h' ∈ C (next m e)

theorem closed_keeps_from {Mem : Type*} {stepH : E → H → Option H}
    {H0 : Set H} {Q Ω : Type*} {A : Q → H → Set Ω}
    (F : ClosedFamily Mem stepH H0 Q Ω A)
    {m : Mem} {h0 : H} (hm : h0 ∈ F.C m) :
    ∀ es h, path stepH es h0 = some h → h ∈ F.C (foldMem F.next m es) := by
  intro es
  induction es generalizing m h0 with
  | nil =>
    intro h hh
    have hh' : h0 = h := by simpa [path] using hh
    subst hh'
    simpa [foldMem] using hm
  | cons e es ih =>
    intro h hh
    cases hs : stepH e h0 with
    | none => simp [path, hs] at hh
    | some h1 =>
      have hh' : path stepH es h1 = some h := by
        simpa [path, hs] using hh
      have h1mem : h1 ∈ F.C (F.next m e) := F.next_closed m e h0 h1 hm hs
      simpa [foldMem] using ih h1mem h hh'

theorem closed_keeps {Mem : Type*} {stepH : E → H → Option H}
    {H0 : Set H} {Q Ω : Type*} {A : Q → H → Set Ω}
    (F : ClosedFamily Mem stepH H0 Q Ω A)
    {h0 : H} (hh0 : h0 ∈ H0) :
    ∀ es h, path stepH es h0 = some h → h ∈ F.C (foldMem F.next F.init es) :=
  closed_keeps_from F (F.init_covers hh0)

end Collecta
end CausalSpectrum
