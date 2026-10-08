import CausalSeed.Arithmetic
noncomputable section
open Classical
namespace CausalSpectrum

section Node
variable (nA : ℕ) (hA : 0 < nA) (nY : Fin nA → ℕ)
  (hY : ∀ a, 0 < nY a)
  (K : (a : Fin nA) → Fin (nY a) → ℝ)
  (Kpos : ∀ a y, 0 < K a y) (Ksum : ∀ a, ∑ y, K a y = 1)
  (child : (a : Fin nA) → Fin (nY a) → Tree)

def pack (a : Fin nA) (y : Fin (nY a)) (sub : Leaf (child a y)) :
    Leaf (Tree.node nA hA nY hY K Kpos Ksum child) :=
  cast (rfl : ((x : Fin nA) ×' ((z : Fin (nY x)) ×' Leaf (child x z))) =
      Leaf (Tree.node nA hA nY hY K Kpos Ksum child)) ⟨a, y, sub⟩

def unpack (ℓ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child)) :
    (a : Fin nA) ×' ((y : Fin (nY a)) ×' Leaf (child a y)) :=
  cast (rfl : Leaf (Tree.node nA hA nY hY K Kpos Ksum child) =
    ((x : Fin nA) ×' ((z : Fin (nY x)) ×' Leaf (child x z)))) ℓ

theorem unpack_pack (a : Fin nA) (y : Fin (nY a)) (sub : Leaf (child a y)) :
    unpack nA hA nY hY K Kpos Ksum child (pack nA hA nY hY K Kpos Ksum child a y sub)
      = ⟨a, y, sub⟩ := rfl

theorem pack_unpack (ℓ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child)) :
    pack nA hA nY hY K Kpos Ksum child
      (unpack nA hA nY hY K Kpos Ksum child ℓ).1
      (unpack nA hA nY hY K Kpos Ksum child ℓ).2.1
      (unpack nA hA nY hY K Kpos Ksum child ℓ).2.2 = ℓ := rfl

theorem leafMass_pack (a : Fin nA) (y : Fin (nY a)) (sub : Leaf (child a y)) :
    leafMass (pack nA hA nY hY K Kpos Ksum child a y sub) = K a y * leafMass sub := rfl

theorem compatible_pack (a : Fin nA) (y : Fin (nY a)) (sub : Leaf (child a y))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    CompatiblePolicy (pack nA hA nY hY K Kpos Ksum child a y sub) π ↔
      a = π.1 ∧ CompatiblePolicy sub (π.2 a y) := by
  rfl

def outCyl (a0 : Fin nA) (y0 : Fin (nY a0))
    (ℓ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child)) : Prop :=
  ∃ sub : Leaf (child a0 y0), ℓ = pack nA hA nY hY K Kpos Ksum child a0 y0 sub

theorem assign_compatible
    (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    (unpack nA hA nY hY K Kpos Ksum child (α π).1).1 = π.1 ∧
      CompatiblePolicy (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.2
        (π.2 (unpack nA hA nY hY K Kpos Ksum child (α π).1).1
          (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.1) := by
  exact (compatible_pack nA hA nY hY K Kpos Ksum child
      (unpack nA hA nY hY K Kpos Ksum child (α π).1).1
      (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.1
      (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.2 π).mp
    ((pack_unpack nA hA nY hY K Kpos Ksum child (α π).1).symm ▸ (α π).2)

theorem hitMass_output
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child))
    (y0 : Fin (nY π.1)) :
    hitMass (outCyl nA hA nY hY K Kpos Ksum child π.1 y0) π = K π.1 y0 := by
  simp only [hitMass, policySum]
  have hpack : ∀ (y : Fin (nY π.1)) (sub : Leaf (child π.1 y)),
      (⟨π.1, y, sub⟩ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child)) =
        pack nA hA nY hY K Kpos Ksum child π.1 y sub :=
    fun _ _ => rfl
  simp_rw [hpack]
  have hterm : ∀ y : Fin (nY π.1),
      policySum (fun sub =>
        if outCyl nA hA nY hY K Kpos Ksum child π.1 y0
            (pack nA hA nY hY K Kpos Ksum child π.1 y sub)
          then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y sub) else 0)
        (π.2 π.1 y) =
      if y = y0 then K π.1 y0 else 0 := by
    intro y
    by_cases hy : y = y0
    · rw [hy]
      have hfun : ∀ sub,
          (if outCyl nA hA nY hY K Kpos Ksum child π.1 y0
              (pack nA hA nY hY K Kpos Ksum child π.1 y0 sub)
            then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y0 sub) else 0) =
            K π.1 y0 * leafMass sub := by
        intro sub
        rw [ite_eq_left ⟨sub, rfl⟩, leafMass_pack]
      have hsum : policySum (fun sub => K π.1 y0 * leafMass sub) (π.2 π.1 y0) =
          K π.1 y0 := by
        rw [policySum_mul, policySum_leafMass, mul_one]
      -- transport hfun into the sum
      have hcongr : policySum (fun sub =>
          if outCyl nA hA nY hY K Kpos Ksum child π.1 y0
              (pack nA hA nY hY K Kpos Ksum child π.1 y0 sub)
            then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y0 sub) else 0)
          (π.2 π.1 y0) =
          policySum (fun sub => K π.1 y0 * leafMass sub) (π.2 π.1 y0) := by
        congr 1
        funext sub
        exact hfun sub
      rw [hcongr, hsum, ite_eq_left rfl]
    · have hfun : ∀ sub,
          (if outCyl nA hA nY hY K Kpos Ksum child π.1 y0
              (pack nA hA nY hY K Kpos Ksum child π.1 y sub)
            then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y sub) else 0) = 0 := by
        intro sub
        rw [ite_eq_right]
        intro hex
        rcases hex with ⟨sub0, h⟩
        have hU := congrArg (unpack nA hA nY hY K Kpos Ksum child) h
        rw [unpack_pack, unpack_pack] at hU
        have hinner := PSigma.mk.inj (eq_of_heq (PSigma.mk.inj hU).2)
        exact hy hinner.1
      have hcongr : policySum (fun sub =>
          if outCyl nA hA nY hY K Kpos Ksum child π.1 y0
              (pack nA hA nY hY K Kpos Ksum child π.1 y sub)
            then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y sub) else 0)
          (π.2 π.1 y) = policySum (fun _ => (0 : ℝ)) (π.2 π.1 y) := by
        congr 1
        funext sub
        exact hfun sub
      rw [hcongr, policySum_zero, ite_eq_right hy]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin (nY π.1))) y0 (fun _ => K π.1 y0),
    ite_eq_left (Finset.mem_univ y0)]

def extendPolicy (a : Fin nA) (y0 : Fin (nY a)) (ρ : Policy (child a y0)) :
    Policy (Tree.node nA hA nY hY K Kpos Ksum child) :=
  (a, fun a' y =>
    if ha : a' = a then
      if hy : y = ha ▸ y0 then
        cast (by
          subst ha
          subst hy
          rfl) ρ
      else
        defaultPolicy (child a' y)
    else
      defaultPolicy (child a' y))

theorem extendPolicy_child (a : Fin nA) (y0 : Fin (nY a)) (ρ : Policy (child a y0)) :
    (extendPolicy nA hA nY hY K Kpos Ksum child a y0 ρ).2 a y0 = ρ := by
  simp [extendPolicy, cast_eq]

def assignOut (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) : Fin (nY π.1) :=
  cast (congrArg (fun b => Fin (nY b))
      (assign_compatible nA hA nY hY K Kpos Ksum child α π).1)
    (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.1

def castSub (a a' : Fin nA) (h : a = a') (y : Fin (nY a)) (sub : Leaf (child a y)) :
    Leaf (child a' (cast (congrArg (fun b => Fin (nY b)) h) y)) :=
  cast (by
    have hsig : (⟨a, y⟩ : (b : Fin nA) × Fin (nY b)) =
        ⟨a', cast (congrArg (fun b => Fin (nY b)) h) y⟩ := by
      subst h; rfl
    exact congrArg (fun p : (b : Fin nA) × Fin (nY b) => Leaf (child p.1 p.2)) hsig) sub

theorem pack_idx (a : Fin nA) (y : Fin (nY a)) (sub : Leaf (child a y))
    (a' : Fin nA) (h : a = a') :
    pack nA hA nY hY K Kpos Ksum child a y sub =
      pack nA hA nY hY K Kpos Ksum child a'
        (cast (congrArg (fun b => Fin (nY b)) h) y)
        (castSub nA nY child a a' h y sub) := by
  subst h
  rfl

theorem outCyl_assign (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    outCyl nA hA nY hY K Kpos Ksum child π.1
      (assignOut nA hA nY hY K Kpos Ksum child α π) (α π).1 := by
  have ha := (assign_compatible nA hA nY hY K Kpos Ksum child α π).1
  rw [(pack_unpack nA hA nY hY K Kpos Ksum child (α π).1).symm]
  exact ⟨castSub nA nY child _ _ ha _ _,
    pack_idx nA hA nY hY K Kpos Ksum child _ _ _ _ ha⟩

theorem sigma_out
    (a : Fin nA) (y : Fin (nY a)) (sub : Leaf (child a y))
    (a' : Fin nA) (y' : Fin (nY a')) (sub' : Leaf (child a' y'))
    (h : (⟨a, y, sub⟩ : (x : Fin nA) ×' ((z : Fin (nY x)) ×' Leaf (child x z))) =
      ⟨a', y', sub'⟩) :
    a = a' ∧
      y' = cast (congrArg (fun b => Fin (nY b)) (PSigma.mk.inj h).1) y := by
  have ha := (PSigma.mk.inj h).1
  subst ha
  have hrest := eq_of_heq (PSigma.mk.inj h).2
  have hy := (PSigma.mk.inj hrest).1
  subst hy
  exact ⟨rfl, rfl⟩

theorem fin_cast_trans {a b c : Fin nA} (h1 : a = b) (h2 : b = c) (y : Fin (nY a)) :
    cast (congrArg (fun t => Fin (nY t)) h2)
        (cast (congrArg (fun t => Fin (nY t)) h1) y) =
      cast (congrArg (fun t => Fin (nY t)) (h1.trans h2)) y := by
  subst h1
  subst h2
  rfl

theorem not_outCyl_other (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π ρ : Policy (Tree.node nA hA nY hY K Kpos Ksum child))
    (hact : π.1 = ρ.1)
    (hout : cast (congrArg (fun b => Fin (nY b)) hact)
        (assignOut nA hA nY hY K Kpos Ksum child α π) ≠
      assignOut nA hA nY hY K Kpos Ksum child α ρ) :
    ¬ outCyl nA hA nY hY K Kpos Ksum child π.1
        (assignOut nA hA nY hY K Kpos Ksum child α π) (α ρ).1 := by
  intro hex
  rcases hex with ⟨sub, hℓ⟩
  have hU := congrArg (unpack nA hA nY hY K Kpos Ksum child) hℓ
  rw [unpack_pack] at hU
  have hs := sigma_out nA nY child
    (unpack nA hA nY hY K Kpos Ksum child (α ρ).1).1
    (unpack nA hA nY hY K Kpos Ksum child (α ρ).1).2.1
    (unpack nA hA nY hY K Kpos Ksum child (α ρ).1).2.2
    π.1 (assignOut nA hA nY hY K Kpos Ksum child α π) sub hU
  have hc := (assign_compatible nA hA nY hY K Kpos Ksum child α ρ).1
  -- assignOut ρ is the cast of the unpacked output along hc
  have hyρ : assignOut nA hA nY hY K Kpos Ksum child α ρ =
      cast (congrArg (fun b => Fin (nY b)) hc)
        (unpack nA hA nY hY K Kpos Ksum child (α ρ).1).2.1 := rfl
  apply hout
  rw [hyρ, hs.2]
  have hstep := fin_cast_trans nA nY (PSigma.mk.inj hU).1 hact
    (unpack nA hA nY hY K Kpos Ksum child (α ρ).1).2.1
  set_option pp.proofs true in
  exact hstep

theorem outCyl_cast (a a' : Fin nA) (h : a = a') (y : Fin (nY a))
    (ℓ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child)) :
    outCyl nA hA nY hY K Kpos Ksum child a y ℓ ↔
      outCyl nA hA nY hY K Kpos Ksum child a'
        (cast (congrArg (fun b => Fin (nY b)) h) y) ℓ := by
  subst h
  rfl

theorem K_cast (a a' : Fin nA) (h : a = a') (y : Fin (nY a)) :
    K a y = K a' (cast (congrArg (fun b => Fin (nY b)) h) y) := by
  subst h
  rfl

theorem conflict_splits (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π ρ : Policy (Tree.node nA hA nY hY K Kpos Ksum child))
    (hact : π.1 = ρ.1)
    (hout : cast (congrArg (fun b => Fin (nY b)) hact)
        (assignOut nA hA nY hY K Kpos Ksum child α π) ≠
      assignOut nA hA nY hY K Kpos Ksum child α ρ) :
    ∃ S : Leaf (Tree.node nA hA nY hY K Kpos Ksum child) → Prop,
      S (α π).1 ∧ ¬ S (α ρ).1 ∧ hitMass S π = hitMass S ρ := by
  let S := outCyl nA hA nY hY K Kpos Ksum child π.1
    (assignOut nA hA nY hY K Kpos Ksum child α π)
  refine ⟨S, outCyl_assign nA hA nY hY K Kpos Ksum child α π,
    not_outCyl_other nA hA nY hY K Kpos Ksum child α π ρ hact hout, ?_⟩
  have hπ := hitMass_output nA hA nY hY K Kpos Ksum child π
    (assignOut nA hA nY hY K Kpos Ksum child α π)
  have hρ := hitMass_output nA hA nY hY K Kpos Ksum child ρ
    (cast (congrArg (fun b => Fin (nY b)) hact)
      (assignOut nA hA nY hY K Kpos Ksum child α π))
  have hpred : S = outCyl nA hA nY hY K Kpos Ksum child ρ.1
      (cast (congrArg (fun b => Fin (nY b)) hact)
        (assignOut nA hA nY hY K Kpos Ksum child α π)) := by
    funext ℓ
    exact propext (outCyl_cast nA hA nY hY K Kpos Ksum child π.1 ρ.1 hact _ ℓ)
  have hk := K_cast nA nY K π.1 ρ.1 hact
    (assignOut nA hA nY hY K Kpos Ksum child α π)
  rw [hπ, hk, ← hρ, hpred]

/-- A child event, seen through one root output, has mass `K` times the child mass. -/
theorem hitMass_lift
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child))
    (y0 : Fin (nY π.1)) (Sc : Leaf (child π.1 y0) → Prop) :
    hitMass (fun ℓ => ∃ sub, ℓ = pack nA hA nY hY K Kpos Ksum child π.1 y0 sub ∧ Sc sub) π =
      K π.1 y0 * hitMass Sc (π.2 π.1 y0) := by
  simp only [hitMass, policySum]
  have hpack : ∀ (y : Fin (nY π.1)) (sub : Leaf (child π.1 y)),
      (⟨π.1, y, sub⟩ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child)) =
        pack nA hA nY hY K Kpos Ksum child π.1 y sub :=
    fun _ _ => rfl
  simp_rw [hpack]
  have hterm : ∀ y : Fin (nY π.1),
      policySum (fun sub =>
        if ∃ sub0, pack nA hA nY hY K Kpos Ksum child π.1 y sub =
            pack nA hA nY hY K Kpos Ksum child π.1 y0 sub0 ∧ Sc sub0
          then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y sub) else 0)
        (π.2 π.1 y) =
      if y = y0 then K π.1 y0 * hitMass Sc (π.2 π.1 y0) else 0 := by
    intro y
    by_cases hy : y = y0
    · rw [hy]
      have hfun : ∀ sub,
          (if ∃ sub0, pack nA hA nY hY K Kpos Ksum child π.1 y0 sub =
              pack nA hA nY hY K Kpos Ksum child π.1 y0 sub0 ∧ Sc sub0
            then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y0 sub) else 0) =
            K π.1 y0 * (if Sc sub then leafMass sub else 0) := by
        intro sub
        by_cases hs : Sc sub
        · have hmem : ∃ sub0, pack nA hA nY hY K Kpos Ksum child π.1 y0 sub =
              pack nA hA nY hY K Kpos Ksum child π.1 y0 sub0 ∧ Sc sub0 :=
            ⟨sub, rfl, hs⟩
          rw [ite_eq_left hmem, leafMass_pack, ite_eq_left hs]
        · rw [ite_eq_right (by
            intro hex
            rcases hex with ⟨sub0, h, hsc⟩
            have hU := congrArg (unpack nA hA nY hY K Kpos Ksum child) h
            rw [unpack_pack, unpack_pack] at hU
            have hinner := PSigma.mk.inj (eq_of_heq (PSigma.mk.inj hU).2)
            have hsub : sub = sub0 := eq_of_heq hinner.2
            exact hs (hsub ▸ hsc)), ite_eq_right hs]
          ring
      have hcongr : policySum (fun sub =>
          if ∃ sub0, pack nA hA nY hY K Kpos Ksum child π.1 y0 sub =
              pack nA hA nY hY K Kpos Ksum child π.1 y0 sub0 ∧ Sc sub0
            then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y0 sub) else 0)
          (π.2 π.1 y0) =
          policySum (fun sub => K π.1 y0 * (if Sc sub then leafMass sub else 0))
            (π.2 π.1 y0) := by
        congr 1
        funext sub
        exact hfun sub
      rw [hcongr, policySum_mul, ite_eq_left rfl]
      rfl
    · have hfun : ∀ sub,
          (if ∃ sub0, pack nA hA nY hY K Kpos Ksum child π.1 y sub =
              pack nA hA nY hY K Kpos Ksum child π.1 y0 sub0 ∧ Sc sub0
            then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y sub) else 0) = 0 := by
        intro sub
        rw [ite_eq_right]
        intro hex
        rcases hex with ⟨_, h, _⟩
        have hU := congrArg (unpack nA hA nY hY K Kpos Ksum child) h
        rw [unpack_pack, unpack_pack] at hU
        have hinner := PSigma.mk.inj (eq_of_heq (PSigma.mk.inj hU).2)
        exact hy hinner.1
      have hcongr : policySum (fun sub =>
          if ∃ sub0, pack nA hA nY hY K Kpos Ksum child π.1 y sub =
              pack nA hA nY hY K Kpos Ksum child π.1 y0 sub0 ∧ Sc sub0
            then leafMass (pack nA hA nY hY K Kpos Ksum child π.1 y sub) else 0)
          (π.2 π.1 y) = policySum (fun _ => (0 : ℝ)) (π.2 π.1 y) := by
        congr 1
        funext sub
        exact hfun sub
      rw [hcongr, policySum_zero, ite_eq_right hy]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin (nY π.1))) y0
      (fun _ => K π.1 y0 * hitMass Sc (π.2 π.1 y0)),
    ite_eq_left (Finset.mem_univ y0)]
  simp [hitMass]

def basePol (a : Fin nA) : Policy (Tree.node nA hA nY hY K Kpos Ksum child) :=
  (a, fun _ _ => defaultPolicy _)

def outOf (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child)) (a : Fin nA) :
    Fin (nY a) :=
  assignOut nA hA nY hY K Kpos Ksum child α (basePol nA hA nY hY K Kpos Ksum child a)

def subLeaf (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    Leaf (child π.1 (assignOut nA hA nY hY K Kpos Ksum child α π)) :=
  castSub nA nY child (unpack nA hA nY hY K Kpos Ksum child (α π).1).1 π.1
    (assign_compatible nA hA nY hY K Kpos Ksum child α π).1
    (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.1
    (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.2

theorem cont_cast (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child))
    {a a' : Fin nA} (h : a = a') (y : Fin (nY a)) :
    π.2 a' (cast (congrArg (fun b => Fin (nY b)) h) y) =
      cast (by
        have hsig : (⟨a, y⟩ : (b : Fin nA) × Fin (nY b)) =
            ⟨a', cast (congrArg (fun b => Fin (nY b)) h) y⟩ := by
          subst h; rfl
        exact congrArg (fun p : (b : Fin nA) × Fin (nY b) => Policy (child p.1 p.2)) hsig)
        (π.2 a y) := by
  subst h
  rfl

theorem cast_compatible {a a' : Fin nA} (h : a = a') (y : Fin (nY a))
    (sub : Leaf (child a y)) (ρ : Policy (child a y))
    (hcomp : CompatiblePolicy sub ρ) :
    CompatiblePolicy (castSub nA nY child a a' h y sub)
      (cast (by
        have hsig : (⟨a, y⟩ : (b : Fin nA) × Fin (nY b)) =
            ⟨a', cast (congrArg (fun b => Fin (nY b)) h) y⟩ := by
          subst h; rfl
        exact congrArg (fun p : (b : Fin nA) × Fin (nY b) => Policy (child p.1 p.2)) hsig) ρ) := by
  subst h
  simpa [castSub] using hcomp

theorem subLeaf_compatible (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    CompatiblePolicy (subLeaf nA hA nY hY K Kpos Ksum child α π)
      (π.2 π.1 (assignOut nA hA nY hY K Kpos Ksum child α π)) := by
  have hc := assign_compatible nA hA nY hY K Kpos Ksum child α π
  have hcast := cast_compatible nA nY child hc.1
    (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.1
    (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.2
    (π.2 (unpack nA hA nY hY K Kpos Ksum child (α π).1).1
      (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.1) hc.2
  have hcont := cont_cast nA hA nY hY K Kpos Ksum child π hc.1
    (unpack nA hA nY hY K Kpos Ksum child (α π).1).2.1
  -- hcont rewrites the target continuation; hcast is compatibility after the same cast
  simpa [subLeaf, assignOut, hcont] using hcast

theorem compat_out {a : Fin nA} {y y' : Fin (nY a)} (h : y = y')
    (sub : Leaf (child a y)) (ρ : Policy (child a y))
    (hcomp : CompatiblePolicy sub ρ) :
    CompatiblePolicy (h ▸ sub) (h ▸ ρ) := by
  subst h
  exact hcomp

theorem cont_out (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child))
    (a : Fin nA) {y y' : Fin (nY a)} (h : y = y') :
    π.2 a y' = h ▸ π.2 a y := by
  subst h
  rfl

/-! ## Induction contract -/

theorem extendPolicy_action (a : Fin nA) (y0 : Fin (nY a)) (ρ : Policy (child a y0)) :
    (extendPolicy nA hA nY hY K Kpos Ksum child a y0 ρ).1 = a := rfl

theorem pack_out (a : Fin nA) {y y' : Fin (nY a)} (h : y = y') (sub : Leaf (child a y)) :
    pack nA hA nY hY K Kpos Ksum child a y sub =
      pack nA hA nY hY K Kpos Ksum child a y' (h ▸ sub) := by
  subst h
  rfl

/-- Parent transcript is the forced output followed by its own child leaf. -/
theorem parent_decomp (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    (α π).1 =
      pack nA hA nY hY K Kpos Ksum child π.1
        (assignOut nA hA nY hY K Kpos Ksum child α π)
        (subLeaf nA hA nY hY K Kpos Ksum child α π) := by
  have ha := (assign_compatible nA hA nY hY K Kpos Ksum child α π).1
  rw [(pack_unpack nA hA nY hY K Kpos Ksum child (α π).1).symm]
  simpa [subLeaf, assignOut] using
    pack_idx nA hA nY hY K Kpos Ksum child _ _ _ _ ha

theorem parent_decomp_out (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child))
    {y : Fin (nY π.1)} (h : assignOut nA hA nY hY K Kpos Ksum child α π = y) :
    (α π).1 =
      pack nA hA nY hY K Kpos Ksum child π.1 y
        (h ▸ subLeaf nA hA nY hY K Kpos Ksum child α π) := by
  rw [parent_decomp nA hA nY hY K Kpos Ksum child α π]
  exact pack_out nA hA nY hY K Kpos Ksum child π.1 h _

/-- Lifted cylinder through the canonical one-action extension. -/
theorem hitMass_extend (a : Fin nA) (y0 : Fin (nY a)) (ρ : Policy (child a y0))
    (S : Leaf (child a y0) → Prop) :
    hitMass (fun ℓ =>
        ∃ sub, ℓ = pack nA hA nY hY K Kpos Ksum child a y0 sub ∧ S sub)
      (extendPolicy nA hA nY hY K Kpos Ksum child a y0 ρ) =
      K a y0 * hitMass S ρ := by
  have h := hitMass_lift nA hA nY hY K Kpos Ksum child
    (extendPolicy nA hA nY hY K Kpos Ksum child a y0 ρ) y0 S
  simpa [extendPolicy, extendPolicy_child] using h

def composeStrat (out : (a : Fin nA) → Fin (nY a))
    (da : (a : Fin nA) → Strategy (child a (out a))) :
    Strategy (Tree.node nA hA nY hY K Kpos Ksum child) :=
  (out, fun a y =>
    if h : y = out a then
      h ▸ da a
    else
      defaultStrategy (child a y))

theorem run_pack (d : Strategy (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    run d π =
      pack nA hA nY hY K Kpos Ksum child π.1 (d.1 π.1)
        (run (d.2 π.1 (d.1 π.1)) (π.2 π.1 (d.1 π.1))) := rfl

theorem compose_child (out : (a : Fin nA) → Fin (nY a))
    (da : (a : Fin nA) → Strategy (child a (out a))) (a : Fin nA) :
    (composeStrat nA hA nY hY K Kpos Ksum child out da).2 a (out a) = da a := by
  simp [composeStrat, cast_eq]

/-- If each child assignment is the tail of `α` and is realized by `da`, the composite realizes `α`. -/
theorem compose_realizes
    (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (out : (a : Fin nA) → Fin (nY a))
    (αa : (a : Fin nA) → SeedAssign (child a (out a)))
    (da : (a : Fin nA) → Strategy (child a (out a)))
    (hout : ∀ π, assignOut nA hA nY hY K Kpos Ksum child α π = out π.1)
    (htail : ∀ π,
      hout π ▸ subLeaf nA hA nY hY K Kpos Ksum child α π =
        (αa π.1 (π.2 π.1 (out π.1))).1)
    (hreal : ∀ a, seedRealizes (da a) = αa a) :
    seedRealizes (composeStrat nA hA nY hY K Kpos Ksum child out da) = α := by
  funext π
  apply Subtype.ext
  dsimp only [seedRealizes]
  rw [parent_decomp_out nA hA nY hY K Kpos Ksum child α π (hout π), run_pack]
  have hrun : run (da π.1) (π.2 π.1 (out π.1)) =
      (αa π.1 (π.2 π.1 (out π.1))).1 := by
    have hEq := congrFun (hreal π.1) (π.2 π.1 (out π.1))
    exact congrArg Subtype.val hEq
  simp [composeStrat, compose_child, hrun, htail]

theorem out_of_realizes
    (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (d : Strategy (Tree.node nA hA nY hY K Kpos Ksum child))
    (h : seedRealizes d = α)
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    assignOut nA hA nY hY K Kpos Ksum child α π = d.1 π.1 := by
  subst h
  simp [assignOut, seedRealizes, run_pack, unpack_pack]
  exact eq_of_heq (cast_heq _ _)

def Splits {T : Tree} (α : SeedAssign T) : Prop :=
  ∃ π ρ : Policy T, ∃ S : Leaf T → Prop,
    S (α π).1 ∧ ¬ S (α ρ).1 ∧ hitMass S π = hitMass S ρ

theorem leaf_realizable (α : SeedAssign Tree.leaf) : seedRealizable α := by
  refine ⟨defaultStrategy Tree.leaf, ?_⟩
  funext π
  apply Subtype.ext
  cases (α π).1
  rfl

theorem cast_apply {β : Fin nA → Type} {a a' : Fin nA} (h : a = a') (f : ∀ x, β x) :
    cast (congrArg β h) (f a) = f a' := by
  subst h
  rfl

theorem conflict_not_realizable
    (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π ρ : Policy (Tree.node nA hA nY hY K Kpos Ksum child))
    (hact : π.1 = ρ.1)
    (hout : cast (congrArg (fun b => Fin (nY b)) hact)
        (assignOut nA hA nY hY K Kpos Ksum child α π) ≠
      assignOut nA hA nY hY K Kpos Ksum child α ρ) :
    ¬ seedRealizable α := by
  intro ⟨d, hd⟩
  apply hout
  rw [out_of_realizes nA hA nY hY K Kpos Ksum child α d hd π,
    out_of_realizes nA hA nY hY K Kpos Ksum child α d hd ρ]
  exact cast_apply nA (β := fun b => Fin (nY b)) hact d.1

def rootAgree (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child)) : Prop :=
  ∀ (π ρ : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) (hact : π.1 = ρ.1),
    cast (congrArg (fun b => Fin (nY b)) hact)
        (assignOut nA hA nY hY K Kpos Ksum child α π) =
      assignOut nA hA nY hY K Kpos Ksum child α ρ

theorem base_action (a : Fin nA) :
    (basePol nA hA nY hY K Kpos Ksum child a).1 = a := rfl

theorem assignOut_outOf
    (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (hagree : rootAgree nA hA nY hY K Kpos Ksum child α)
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    assignOut nA hA nY hY K Kpos Ksum child α π =
      outOf nA hA nY hY K Kpos Ksum child α π.1 := by
  have h := (hagree (basePol nA hA nY hY K Kpos Ksum child π.1) π
    (base_action nA hA nY hY K Kpos Ksum child π.1)).symm
  rw [h, outOf]
  exact eq_of_heq (cast_heq _ _)

def canonPol (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    Policy (Tree.node nA hA nY hY K Kpos Ksum child) :=
  extendPolicy nA hA nY hY K Kpos Ksum child π.1
    (outOf nA hA nY hY K Kpos Ksum child α π.1)
    (π.2 π.1 (outOf nA hA nY hY K Kpos Ksum child α π.1))

theorem canon_action (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    (canonPol nA hA nY hY K Kpos Ksum child α π).1 = π.1 := rfl

theorem canon_cont (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    (canonPol nA hA nY hY K Kpos Ksum child α π).2 π.1
        (outOf nA hA nY hY K Kpos Ksum child α π.1) =
      π.2 π.1 (outOf nA hA nY hY K Kpos Ksum child α π.1) := by
  simpa [canonPol] using
    extendPolicy_child nA hA nY hY K Kpos Ksum child π.1
      (outOf nA hA nY hY K Kpos Ksum child α π.1)
      (π.2 π.1 (outOf nA hA nY hY K Kpos Ksum child α π.1))

theorem pack_leaf_inj (a : Fin nA) (y : Fin (nY a))
    (sub₁ sub₂ : Leaf (child a y))
    (h : pack nA hA nY hY K Kpos Ksum child a y sub₁ =
      pack nA hA nY hY K Kpos Ksum child a y sub₂) :
    sub₁ = sub₂ := by
  have hU := congrArg (unpack nA hA nY hY K Kpos Ksum child) h
  rw [unpack_pack, unpack_pack] at hU
  have hinner := PSigma.mk.inj (eq_of_heq (PSigma.mk.inj hU).2)
  exact eq_of_heq hinner.2

theorem tail_splits
    (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (hagree : rootAgree nA hA nY hY K Kpos Ksum child α)
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child))
    (hdif :
      (assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree π) ▸
          subLeaf nA hA nY hY K Kpos Ksum child α π ≠
        (assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree
            (canonPol nA hA nY hY K Kpos Ksum child α π)) ▸
          subLeaf nA hA nY hY K Kpos Ksum child α
            (canonPol nA hA nY hY K Kpos Ksum child α π)) :
    Splits α := by
  let ρ := canonPol nA hA nY hY K Kpos Ksum child α π
  let y := outOf nA hA nY hY K Kpos Ksum child α π.1
  let hπ := assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree π
  let hρ := assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree ρ
  let ℓπ := hπ ▸ subLeaf nA hA nY hY K Kpos Ksum child α π
  let ℓρ := hρ ▸ subLeaf nA hA nY hY K Kpos Ksum child α ρ
  let Sc : Leaf (child π.1 y) → Prop := fun s => s = ℓπ
  let S : Leaf (Tree.node nA hA nY hY K Kpos Ksum child) → Prop :=
    fun ℓ => ∃ sub, ℓ = pack nA hA nY hY K Kpos Ksum child π.1 y sub ∧ Sc sub
  refine ⟨π, ρ, S, ?_, ?_, ?_⟩
  · refine ⟨ℓπ, ?_, rfl⟩
    simpa [ℓπ, y] using parent_decomp_out nA hA nY hY K Kpos Ksum child α π hπ
  · intro hex
    rcases hex with ⟨sub, hℓ, hsc⟩
    have hdec := parent_decomp_out nA hA nY hY K Kpos Ksum child α ρ hρ
    have hpack : pack nA hA nY hY K Kpos Ksum child π.1 y sub =
        pack nA hA nY hY K Kpos Ksum child π.1 y ℓρ := by
      calc
        pack nA hA nY hY K Kpos Ksum child π.1 y sub = (α ρ).1 := hℓ.symm
        _ = pack nA hA nY hY K Kpos Ksum child ρ.1
            (outOf nA hA nY hY K Kpos Ksum child α ρ.1)
            (hρ ▸ subLeaf nA hA nY hY K Kpos Ksum child α ρ) := hdec
        _ = pack nA hA nY hY K Kpos Ksum child π.1 y ℓρ := rfl
    have hsub := pack_leaf_inj nA hA nY hY K Kpos Ksum child π.1 y sub ℓρ hpack
    exact hdif (hsc.symm.trans hsub)
  · have hπm := hitMass_lift nA hA nY hY K Kpos Ksum child π y Sc
    have hρm := hitMass_lift nA hA nY hY K Kpos Ksum child ρ y Sc
    simp only [S, y]
    calc
      hitMass (fun ℓ => ∃ sub, ℓ = pack nA hA nY hY K Kpos Ksum child π.1 y sub ∧ Sc sub) π
        = K π.1 y * hitMass Sc (π.2 π.1 y) := hπm
      _ = K ρ.1 y * hitMass Sc (ρ.2 ρ.1 y) := by
        dsimp only [ρ, y]
        change K π.1 (outOf nA hA nY hY K Kpos Ksum child α π.1) *
            hitMass Sc (π.2 π.1 (outOf nA hA nY hY K Kpos Ksum child α π.1)) =
          K π.1 (outOf nA hA nY hY K Kpos Ksum child α π.1) *
            hitMass Sc ((canonPol nA hA nY hY K Kpos Ksum child α π).2 π.1
              (outOf nA hA nY hY K Kpos Ksum child α π.1))
        rw [canon_cont]
      _ = hitMass (fun ℓ => ∃ sub, ℓ = pack nA hA nY hY K Kpos Ksum child ρ.1 y sub ∧ Sc sub) ρ :=
        hρm.symm
      _ = hitMass (fun ℓ => ∃ sub, ℓ = pack nA hA nY hY K Kpos Ksum child π.1 y sub ∧ Sc sub) ρ := rfl

theorem extend_compatible
    (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (hagree : rootAgree nA hA nY hY K Kpos Ksum child α)
    (a : Fin nA) (ρ : Policy (child a (outOf nA hA nY hY K Kpos Ksum child α a))) :
    CompatiblePolicy
      ((assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree
          (extendPolicy nA hA nY hY K Kpos Ksum child a
            (outOf nA hA nY hY K Kpos Ksum child α a) ρ)) ▸
        subLeaf nA hA nY hY K Kpos Ksum child α
          (extendPolicy nA hA nY hY K Kpos Ksum child a
            (outOf nA hA nY hY K Kpos Ksum child α a) ρ))
      ρ := by
  let y := outOf nA hA nY hY K Kpos Ksum child α a
  let π := extendPolicy nA hA nY hY K Kpos Ksum child a y ρ
  let h := assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree π
  have hc := subLeaf_compatible nA hA nY hY K Kpos Ksum child α π
  have hmove := compat_out nA nY child h (subLeaf nA hA nY hY K Kpos Ksum child α π)
    (π.2 π.1 (assignOut nA hA nY hY K Kpos Ksum child α π)) hc
  have hback := cont_out nA hA nY hY K Kpos Ksum child π π.1 h
  rw [← hback] at hmove
  change CompatiblePolicy
      ((assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree
          (extendPolicy nA hA nY hY K Kpos Ksum child a
            (outOf nA hA nY hY K Kpos Ksum child α a) ρ)) ▸
        subLeaf nA hA nY hY K Kpos Ksum child α
          (extendPolicy nA hA nY hY K Kpos Ksum child a
            (outOf nA hA nY hY K Kpos Ksum child α a) ρ))
      ((extendPolicy nA hA nY hY K Kpos Ksum child a
          (outOf nA hA nY hY K Kpos Ksum child α a) ρ).2 a
        (outOf nA hA nY hY K Kpos Ksum child α a)) at hmove
  rw [extendPolicy_child nA hA nY hY K Kpos Ksum child a
    (outOf nA hA nY hY K Kpos Ksum child α a) ρ] at hmove
  exact hmove

def childAssign
    (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (hagree : rootAgree nA hA nY hY K Kpos Ksum child α)
    (a : Fin nA) : SeedAssign (child a (outOf nA hA nY hY K Kpos Ksum child α a)) :=
  fun ρ =>
    ⟨(assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree
        (extendPolicy nA hA nY hY K Kpos Ksum child a
          (outOf nA hA nY hY K Kpos Ksum child α a) ρ)) ▸
      subLeaf nA hA nY hY K Kpos Ksum child α
        (extendPolicy nA hA nY hY K Kpos Ksum child a
          (outOf nA hA nY hY K Kpos Ksum child α a) ρ),
     extend_compatible nA hA nY hY K Kpos Ksum child α hagree a ρ⟩

theorem lift_splits
    (α : SeedAssign (Tree.node nA hA nY hY K Kpos Ksum child))
    (hagree : rootAgree nA hA nY hY K Kpos Ksum child α)
    (a : Fin nA)
    (hchild : Splits (childAssign nA hA nY hY K Kpos Ksum child α hagree a)) :
    Splits α := by
  rcases hchild with ⟨ρ₁, ρ₂, Sc, h₁, h₂, hmass⟩
  let y := outOf nA hA nY hY K Kpos Ksum child α a
  let π₁ := extendPolicy nA hA nY hY K Kpos Ksum child a y ρ₁
  let π₂ := extendPolicy nA hA nY hY K Kpos Ksum child a y ρ₂
  let S : Leaf (Tree.node nA hA nY hY K Kpos Ksum child) → Prop :=
    fun ℓ => ∃ sub, ℓ = pack nA hA nY hY K Kpos Ksum child a y sub ∧ Sc sub
  refine ⟨π₁, π₂, S, ?_, ?_, ?_⟩
  · refine ⟨(childAssign nA hA nY hY K Kpos Ksum child α hagree a ρ₁).1,
      parent_decomp_out nA hA nY hY K Kpos Ksum child α π₁
        (assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree π₁),
      h₁⟩
  · intro hex
    rcases hex with ⟨sub, hℓ, hsc⟩
    have hdec := parent_decomp_out nA hA nY hY K Kpos Ksum child α π₂
      (assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree π₂)
    have hpack : pack nA hA nY hY K Kpos Ksum child a y sub =
        pack nA hA nY hY K Kpos Ksum child a y
          (childAssign nA hA nY hY K Kpos Ksum child α hagree a ρ₂).1 := by
      calc
        pack nA hA nY hY K Kpos Ksum child a y sub = (α π₂).1 := hℓ.symm
        _ = pack nA hA nY hY K Kpos Ksum child π₂.1
            (outOf nA hA nY hY K Kpos Ksum child α π₂.1)
            ((assignOut_outOf nA hA nY hY K Kpos Ksum child α hagree π₂) ▸
              subLeaf nA hA nY hY K Kpos Ksum child α π₂) := hdec
        _ = pack nA hA nY hY K Kpos Ksum child a y
            (childAssign nA hA nY hY K Kpos Ksum child α hagree a ρ₂).1 := rfl
    exact h₂ ((pack_leaf_inj nA hA nY hY K Kpos Ksum child a y _ _ hpack) ▸ hsc)
  · have hm₁ := hitMass_extend nA hA nY hY K Kpos Ksum child a y ρ₁ Sc
    have hm₂ := hitMass_extend nA hA nY hY K Kpos Ksum child a y ρ₂ Sc
    simp only [S, π₁, π₂, y]
    calc
      hitMass (fun ℓ => ∃ sub, ℓ = pack nA hA nY hY K Kpos Ksum child a y sub ∧ Sc sub) π₁
        = K a y * hitMass Sc ρ₁ := hm₁
      _ = K a y * hitMass Sc ρ₂ := by rw [hmass]
      _ = hitMass (fun ℓ => ∃ sub, ℓ = pack nA hA nY hY K Kpos Ksum child a y sub ∧ Sc sub) π₂ :=
        hm₂.symm

end Node

theorem unrealizable_splits : ∀ {T : Tree} (α : SeedAssign T),
    ¬ seedRealizable α → Splits α := by
  intro T
  induction T with
  | leaf =>
      intro α h
      exact absurd (leaf_realizable α) h
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro α h
      by_cases hconf : rootAgree nA hA nY hY K Kpos Ksum child α
      · by_cases htail : ∀ π,
            (assignOut_outOf nA hA nY hY K Kpos Ksum child α hconf π) ▸
                subLeaf nA hA nY hY K Kpos Ksum child α π =
              (assignOut_outOf nA hA nY hY K Kpos Ksum child α hconf
                  (canonPol nA hA nY hY K Kpos Ksum child α π)) ▸
                subLeaf nA hA nY hY K Kpos Ksum child α
                  (canonPol nA hA nY hY K Kpos Ksum child α π)
        · have hbad : ∃ a, ¬ seedRealizable
              (childAssign nA hA nY hY K Kpos Ksum child α hconf a) := by
            by_contra hall
            push_neg at hall
            let da : (a : Fin nA) → Strategy (child a (outOf nA hA nY hY K Kpos Ksum child α a)) :=
              fun a => Classical.choose (hall a)
            have hda : ∀ a, seedRealizes (da a) =
                childAssign nA hA nY hY K Kpos Ksum child α hconf a :=
              fun a => Classical.choose_spec (hall a)
            have htail' : ∀ π,
                (assignOut_outOf nA hA nY hY K Kpos Ksum child α hconf π) ▸
                    subLeaf nA hA nY hY K Kpos Ksum child α π =
                  (childAssign nA hA nY hY K Kpos Ksum child α hconf π.1
                    (π.2 π.1 (outOf nA hA nY hY K Kpos Ksum child α π.1))).1 := by
              intro π
              simpa [childAssign, canonPol] using htail π
            exact h ⟨composeStrat nA hA nY hY K Kpos Ksum child
                (outOf nA hA nY hY K Kpos Ksum child α) da,
              compose_realizes nA hA nY hY K Kpos Ksum child α
                (outOf nA hA nY hY K Kpos Ksum child α)
                (childAssign nA hA nY hY K Kpos Ksum child α hconf) da
                (fun π => assignOut_outOf nA hA nY hY K Kpos Ksum child α hconf π)
                htail' hda⟩
          obtain ⟨a, ha⟩ := hbad
          exact lift_splits nA hA nY hY K Kpos Ksum child α hconf a
            (ih a (outOf nA hA nY hY K Kpos Ksum child α a) _ ha)
        · push_neg at htail
          obtain ⟨π, hdif⟩ := htail
          exact tail_splits nA hA nY hY K Kpos Ksum child α hconf π hdif
      · unfold rootAgree at hconf
        push_neg at hconf
        obtain ⟨π, ρ, hact, hout⟩ := hconf
        unfold Splits
        exact ⟨π, ρ, conflict_splits nA hA nY hY K Kpos Ksum child α π ρ hact hout⟩

theorem seedMass_eq_subsetSum {m : ℕ} (w : Fin m → ℝ) (A : Finset (Fin m)) :
    seedMass w (fun i => i ∈ A) = subsetSum w A := by
  simp [seedMass, subsetSum, Finset.sum_filter]

/-- An index that no single strategy realises lies in the arithmetic defect. -/
theorem bad_mem_defect {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) {T : Tree}
    (f : Decoder (m := m) T) (hf : Accurate w ε f) (i : Fin m)
    (hbad : ¬ seedRealizable (oneAssign f i)) : inDefect w ε i := by
  obtain ⟨π, ρ, S, hπ, hρ, hmass⟩ := unrealizable_splits (oneAssign f i) hbad
  classical
  let A := Finset.univ.filter (fun j : Fin m => S (f π j).1)
  let B := Finset.univ.filter (fun j : Fin m => S (f ρ j).1)
  have hAeq : seedMass w (fun j => S (f π j).1) = subsetSum w A := by
    simp [seedMass, subsetSum, A, Finset.sum_filter]
  have hBeq : seedMass w (fun j => S (f ρ j).1) = subsetSum w B := by
    simp [seedMass, subsetSum, B, Finset.sum_filter]
  have hA : |subsetSum w A - hitMass S π| ≤ ε := by
    simpa [hAeq] using hf π S
  have hB : |subsetSum w B - hitMass S ρ| ≤ ε := by
    simpa [hBeq] using hf ρ S
  have hgap : |subsetSum w A - subsetSum w B| ≤ 2 * ε := by
    calc
      |subsetSum w A - subsetSum w B|
        ≤ |subsetSum w A - hitMass S π| + |hitMass S π - subsetSum w B| := abs_sub_le _ _ _
      _ = |subsetSum w A - hitMass S π| + |hitMass S ρ - subsetSum w B| := by rw [hmass]
      _ = |subsetSum w A - hitMass S π| + |subsetSum w B - hitMass S ρ| := by
        rw [abs_sub_comm (hitMass S ρ)]
      _ ≤ ε + ε := add_le_add hA hB
      _ = 2 * ε := by ring
  have hiA : i ∈ A := by
    simp [A, oneAssign] at hπ
    simpa [A] using hπ
  have hiB : i ∉ B := by
    simp [B, oneAssign] at hρ
    simpa [B] using hρ
  have hne : A ≠ B := by
    intro hAB
    exact hiB (hAB ▸ hiA)
  have hsym : i ∈ seedSym A B := by
    rw [mem_seedSym]
    exact Or.inl ⟨hiA, hiB⟩
  exact ⟨A, B, hne, hgap, hsym⟩

end CausalSpectrum
end


