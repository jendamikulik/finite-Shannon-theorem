/-
Hypothesis 9, the fateful reading.

Section `Hypotéza 9, osudová` of `notes/Unity.tex`, stated over the
golden sphere of `CausalSeed/GoldenSphere.lean` and the supplier
`Unity.Fateful` of `CausalSeed/Unity.lean`. Nothing is redefined.

Fate would be an external supplier: a map that writes the next state and
thereby controls the outcome. Two readings are not the same hypothesis.

Proved here, with no sorry:

* the definition of a supplier inside the offer, in the form
  `G(w,x) ≠ ∅ → σ(w,x) ∈ G(w,x)` (`supplier_iff`);
* a sphere that opens every action and refuses every consent has an
  empty offer; every map is vacuously a supplier of it, and no supplier
  offers a step (`fate_in_refusal`);
* a value of `σ` that lies in `G(w,x)` lies in `K`, and a trajectory
  written by a supplier through nonempty offers stays in `K`
  (`fate_inside_care`, `supplier_run_stays`);
* no map that depends only on the wish gives, after one wish, `1` in one
  state and `0` in another (`intention_is_not_the_instrument_nat`); inside a
  sphere whose two offers under one wish are `{1}` and `{0}`, a supplier
  exists and none of them depends only on the wish
  (`flip_supplier_not_wish_only`);
* a state written where every opened action lacks some consent is not
  offered; it is a step of the sphere with the consents erased, whose
  offer differs (`over_consent_not_offered`, `erased_offer_strictly_larger`);
* where the total is booked does not factor through the total, and equal
  inside and outside totals do not yield an offered step
  (`booking_does_not_factor_through_total`, `same_total_no_step`).

Not proved: the existence of a supplier, and Hypothesis 9 above consent.
-/
import CausalSeed.Unity

namespace CausalSpectrum
namespace Fate

open GoldenSphere Unity

variable {X Ω W N : Type*}

/-! ### Fate inside the offer -/

/-- The definition `Osud uvnitř nabídky`: a map `σ` is the supplier of a
`Unity.Fateful` structure exactly when `G(w,x) ≠ ∅ → σ(w,x) ∈ G(w,x)`. -/
theorem supplier_iff (S : Sphere X Ω W N) (σ : W → X → X) :
    (∃ F : Fateful S, F.supplier = σ) ↔
      ∀ w x, G S w x ≠ ∅ → σ w x ∈ G S w x := by
  constructor
  · rintro ⟨F, rfl⟩ w x h
    exact F.controls w x (Set.nonempty_iff_ne_empty.2 h)
  · intro h
    exact ⟨⟨σ, fun w x hne => h w x (Set.nonempty_iff_ne_empty.1 hne)⟩, rfl⟩

/-! ### Fate in a refusal offers nothing -/

/-- Any action outside the consent of one agent empties the offer at that
state, whatever the wish. -/
theorem refusal_empties_offer (S : Sphere X Ω W N) (w : W) (x : X) (i : N)
    (hi : ∀ a, a ∉ S.C i x) : G S w x = ∅ := by
  ext y
  constructor
  · rintro ⟨a, ha, _, _⟩
    exact (hi a (ha.2 i)).elim
  · intro hy
    exact hy.elim

/-- Every map is, vacuously, a supplier of the silent sphere. -/
def silentSupplier (σ : Unit → Unit → Unit) : Fateful silentSphere where
  supplier := σ
  controls w x h := by
    rw [silent_offer] at h
    exact (Set.not_nonempty_empty h).elim

/-- Theorem `Osud v odmítnutí nic nenabídne`. There is a sphere, with a
nonempty set of agents, that opens every action and whose every consent
refuses every action. Its offer is empty. Suppliers of it exist, and no
supplier of it offers a step. -/
theorem fate_in_refusal :
    ∃ S : Sphere Unit Unit Unit Unit,
      (∀ w x, S.I w x = Set.univ) ∧
      (∀ i x a, a ∉ S.C i x) ∧
      (∀ w x, G S w x = ∅) ∧
      Nonempty (Fateful S) ∧
      ∀ (F : Fateful S) w x, F.supplier w x ∉ G S w x :=
  ⟨silentSphere, fun _ _ => rfl, fun _ _ _ h => h, silent_offer,
    ⟨silentSupplier fun _ _ => ()⟩, fate_does_not_fill_silence⟩

/-! ### Fate inside care stays -/

/-- Theorem `Osud uvnitř péče zůstává`. If `σ(w,x) ∈ G(w,x)`, then
`σ(w,x) ∈ K`. Any map, at any point. -/
theorem fate_inside_care (S : Sphere X Ω W N) (σ : W → X → X) (w : W) (x : X)
    (h : σ w x ∈ G S w x) : σ w x ∈ S.K :=
  G_subset_K S w x h

/-- A trajectory written by a supplier, starting in care and passing only
through nonempty offers, stays in care. The nonempty offers are a
hypothesis; the supplier does not produce them. -/
theorem supplier_run_stays (S : Sphere X Ω W N) (F : Fateful S) (w : ℕ → W)
    (x : ℕ → X) (h0 : x 0 ∈ S.K) (hrun : ∀ t, x (t + 1) = F.supplier (w t) (x t))
    (hoff : ∀ t, (G S (w t) (x t)).Nonempty) : ∀ t, x t ∈ S.K :=
  stays_in_K S w x h0 fun t => (hrun t).symm ▸ F.controls (w t) (x t) (hoff t)

/-- The existence of a supplier does not give a step: the silent sphere has
suppliers and an empty offer. -/
theorem supplier_does_not_give_step :
    Nonempty (Fateful silentSphere) ∧ ∀ w x, ¬ ∃ y, y ∈ G silentSphere w x :=
  ⟨⟨silentSupplier fun _ _ => ()⟩, fun w x ⟨y, hy⟩ => by
    rw [silent_offer] at hy
    exact hy⟩

/-! ### The intention is not the instrument -/

/-- Theorem `Záměr není instrument`, general form. A map that depends only
on the wish cannot give, after one wish `w`, the value `y₁` in a state `x₀`
and a different value `y₀` in a state `x₁`. -/
theorem intention_is_not_the_instrument_general {Y : Type*} (w : W) (x₀ x₁ : X)
    {y₀ y₁ : Y} (hy : y₁ ≠ y₀) :
    ¬ ∃ σ : W → X → Y, (∃ g : W → Y, ∀ w x, σ w x = g w) ∧
        σ w x₀ = y₁ ∧ σ w x₁ = y₀ := by
  rintro ⟨σ, ⟨g, hg⟩, h₁, h₀⟩
  exact hy (h₁.symm.trans ((hg w x₀).trans ((hg w x₁).symm.trans h₀)))

/-- Theorem `Záměr není instrument`, with the values `1` and `0`. -/
theorem intention_is_not_the_instrument_nat (w : W) (x₀ x₁ : X) :
    ¬ ∃ σ : W → X → ℕ, (∃ g : W → ℕ, ∀ w x, σ w x = g w) ∧
        σ w x₀ = 1 ∧ σ w x₁ = 0 :=
  intention_is_not_the_instrument_general w x₀ x₁ one_ne_zero

/-- A sphere on two states whose offer under the one wish is the other
state: `G(w,false) = {true}` and `G(w,true) = {false}`. -/
def flipSphere : Sphere Bool Bool Unit Unit where
  I := fun _ _ => Set.univ
  F := fun _ a => a
  C := fun _ x => {!x}
  K := Set.univ

theorem flip_offer (w : Unit) (x : Bool) : G flipSphere w x = {!x} := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl, _⟩
    exact ha.2 ()
  · intro hy
    exact ⟨y, ⟨trivial, fun _ => hy⟩, rfl, trivial⟩

/-- Inside a sphere: after one wish the two offers demand `1` and `0`.
A supplier exists, and no supplier depends only on the wish. -/
theorem flip_supplier_not_wish_only :
    Nonempty (Fateful flipSphere) ∧
      ¬ ∃ F : Fateful flipSphere, ∃ g : Unit → Bool, ∀ w x, F.supplier w x = g w := by
  refine ⟨⟨⟨fun _ x => !x, fun w x _ => by rw [flip_offer]; rfl⟩⟩, ?_⟩
  rintro ⟨F, g, hg⟩
  have h₀ := F.controls () false (by rw [flip_offer]; exact Set.singleton_nonempty _)
  have h₁ := F.controls () true (by rw [flip_offer]; exact Set.singleton_nonempty _)
  rw [flip_offer, hg] at h₀ h₁
  exact Bool.false_ne_true ((Set.mem_singleton_iff.1 h₁).symm.trans
    (Set.mem_singleton_iff.1 h₀))

/-! ### Fate above consent erases the sphere -/

/-- A state written at `(w,x)` only through actions that agent `i` refuses
is not offered. -/
theorem over_consent_not_offered (S : Sphere X Ω W N) (w : W) (x : X) (y : X)
    (i : N) (hy : ∀ a, a ∈ S.I w x → y = S.F x a → a ∉ S.C i x) :
    y ∉ G S w x := by
  rintro ⟨a, ha, hya, _⟩
  exact hy a ha.1 hya (ha.2 i)

/-- A map that writes a state outside a nonempty offer is not a supplier
of the sphere. -/
theorem over_consent_not_supplier (S : Sphere X Ω W N) (σ : W → X → X) (w : W)
    (x : X) (hne : (G S w x).Nonempty) (hout : σ w x ∉ G S w x) :
    ¬ ∃ F : Fateful S, F.supplier = σ := by
  rintro ⟨F, rfl⟩
  exact hout (F.controls w x hne)

/-- A trajectory that takes a written step outside the offer is not a
trajectory of the sphere. -/
theorem over_consent_not_a_run (S : Sphere X Ω W N) (w : ℕ → W) (x : ℕ → X)
    (t : ℕ) (hout : x (t + 1) ∉ G S (w t) (x t)) :
    ¬ ∀ s, x (s + 1) ∈ G S (w s) (x s) :=
  fun h => hout (h t)

/-- The sphere with every consent boundary erased. -/
def erased (S : Sphere X Ω W N) : Sphere X Ω W N where
  I := S.I
  F := S.F
  C := fun _ _ => Set.univ
  K := S.K

/-- Erasing consents can only enlarge the offer. -/
theorem offer_subset_erased (S : Sphere X Ω W N) (w : W) (x : X) :
    G S w x ⊆ G (erased S) w x := by
  rintro y ⟨a, ha, hy, hk⟩
  exact ⟨a, ⟨ha.1, fun _ => trivial⟩, hy, hk⟩

/-- A state written above consent, opened by the wish and landing in care,
is a step of the erased sphere. -/
theorem written_is_erased_step (S : Sphere X Ω W N) (w : W) (x : X) (a : Ω)
    (hI : a ∈ S.I w x) (hK : S.F x a ∈ S.K) : S.F x a ∈ G (erased S) w x :=
  ⟨a, ⟨hI, fun _ => trivial⟩, rfl, hK⟩

/-- For the silent sphere the erased offer is the whole state space and the
offer itself is empty: writing over the refusals does not complete the
sphere, it replaces it by another one. -/
theorem erased_offer_strictly_larger (w x : Unit) :
    G silentSphere w x = ∅ ∧ G (erased silentSphere) w x = Set.univ := by
  refine ⟨silent_offer w x, ?_⟩
  ext y
  exact ⟨fun _ => trivial, fun _ => ⟨y, ⟨trivial, fun _ => trivial⟩, rfl, trivial⟩⟩

/-! ### The same total booked outside -/

/-- Where an account `(inside, outside)` books its charge does not factor
through its total. -/
theorem booking_does_not_factor_through_total :
    ¬ ∃ g : Set.range (fun p : ℝ × ℝ => p.1 + p.2) → ℝ,
        ∀ p : ℝ × ℝ, g ⟨p.1 + p.2, ⟨p, rfl⟩⟩ = p.1 := by
  intro h
  have hconst := (factors_through_iff (fun p : ℝ × ℝ => p.1 + p.2) (fun p => p.1)).1 h
  have := hconst (internal 1) (external 1) (same_total 1)
  exact charge_sits_elsewhere 1 one_ne_zero this

/-- Equal inside and outside totals do not yield an offered step: they
hold for every value, and the silent sphere offers nothing. -/
theorem same_total_no_step :
    ¬ ∀ S : Sphere Unit Unit Unit Unit,
        (∀ c : ℝ, (internal c).1 + (internal c).2 = (external c).1 + (external c).2) →
          ∃ y, y ∈ G S () () := by
  intro h
  obtain ⟨y, hy⟩ := h silentSphere same_total
  rw [silent_offer] at hy
  exact hy

end Fate
end CausalSpectrum
