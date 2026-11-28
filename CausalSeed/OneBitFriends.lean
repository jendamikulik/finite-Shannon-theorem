/-
The theorem of one bit and two friends.

Two friends start from the same history and ask the same first question;
the prescribed answer is a fair bit. Each may then choose a second question
from the first answer; the prescribed answer to every further question is
`0`, and the conversation ends.

Proved here, with no sorry:

* one fair bit is an exact causal seed: the shared decoder returns the seed
  on the first question and `0` thereafter; for every deterministic adaptive
  policy `π`, the transcript `(S, π S, 0)` has the prescribed law, each of
  the two atoms of mass `1/2`, and the seed has Shannon entropy `H(S) = 1`;
* every transcript of every policy has surprisal `1`, so the envelope is
  `L = 1`;
* one bit is necessary: the first reply of any exact seed is a deterministic
  function of the seed and is a fair bit, and the entropy of a function is
  at most the entropy of the seed, hence `H(S') ≥ H(B') = 1`, so `C = 1`;
* correct marginals do not give a shared realization: if one friend asks `a`
  and the other asks `b ≠ a`, the anti-coupling `(U, a, 0)` with `(1-U, b, 0)`
  for a fair bit `U` has both prescribed marginals, and no shared causal
  decoder induces it, because a shared decoder returns the same first reply,
  at the same history, on every seed atom.

Not formalized: a general tree, the greedy overhead, electrons, or worldlines.
The same sharpness `L(T) = C(T) = 1` for the two-friend tree already appears
in `ManyFriends.lean`.
-/
import CausalSeed.Identity

noncomputable section

open Classical Finset

namespace CausalSpectrum
namespace OneBitFriends

/-! ### Transcripts and policies -/

/-- A bit. -/
abbrev Bit := Fin 2

/-- A conversation transcript: first reply, second question, second reply. -/
abbrev Transcript (A : Type) := Bit × A × Bit

/-- A deterministic adaptive policy: the second question after the first reply. -/
abbrev Policy (A : Type) := Bit → A

/-- The prescribed transcript of policy `π` on first reply `b`. -/
def prescribed {A : Type} (π : Policy A) (b : Bit) : Transcript A :=
  (b, π b, 0)

theorem prescribed_injective {A : Type} (π : Policy A) {b b' : Bit}
    (h : prescribed π b = prescribed π b') : b = b' :=
  congrArg (fun x : Transcript A => x.1) h

theorem prescribed_ne {A : Type} (π : Policy A) :
    prescribed π 0 ≠ prescribed π 1 :=
  fun h => Fin.zero_ne_one (prescribed_injective π h)

/-- The prescribed law of `π`: each of the two transcripts has mass `1/2`. -/
def prescribedLaw {A : Type} [DecidableEq A] (π : Policy A) : Transcript A → ℝ :=
  fun x => if prescribed π 0 = x then (1 : ℝ) / 2
           else if prescribed π 1 = x then (1 : ℝ) / 2
           else 0

theorem prescribedLaw_cases {A : Type} [DecidableEq A] (π : Policy A)
    (x : Transcript A) :
    prescribedLaw π x =
      (if prescribed π 0 = x then (1 : ℝ) / 2 else 0) +
        (if prescribed π 1 = x then (1 : ℝ) / 2 else 0) := by
  by_cases h0 : prescribed π 0 = x
  · have h1 : prescribed π 1 ≠ x := fun h => prescribed_ne π (h0.trans h.symm)
    simp [prescribedLaw, h0, h1]
  · by_cases h1 : prescribed π 1 = x
    · simp [prescribedLaw, h0, h1]
    · simp [prescribedLaw, h0, h1]

theorem prescribedLaw_at {A : Type} [DecidableEq A] (π : Policy A) (b : Bit) :
    prescribedLaw π (prescribed π b) = 1 / 2 := by
  fin_cases b <;> simp [prescribedLaw, prescribed_ne π]

theorem prescribedLaw_zero {A : Type} [DecidableEq A] (π : Policy A)
    (x : Transcript A) (h0 : prescribed π 0 ≠ x) (h1 : prescribed π 1 ≠ x) :
    prescribedLaw π x = 0 := by
  simp [prescribedLaw, h0, h1]

/-! ### One fair bit, shared decoder -/

/-- The fair bit, as a seed law. -/
def fair : Bit → ℝ := fun _ => 1 / 2

theorem fair_nonneg (s : Bit) : 0 ≤ fair s := by
  simp only [fair]
  norm_num

theorem fair_sum : ∑ s : Bit, fair s = 1 := by
  simp [fair]

/-- Shared decoder: return the seed as the first reply, and `0` later. -/
def decode {A : Type} (s : Bit) (π : Policy A) : Transcript A :=
  (s, π s, 0)

theorem decode_eq_prescribed {A : Type} (s : Bit) (π : Policy A) :
    decode s π = prescribed π s := rfl

/-- Law induced by a finite seed `μ` and a first-reply map `φ`. Later replies
are the constant `0`. -/
def induced {A : Type} [DecidableEq A] {α : Type} [Fintype α]
    (μ : α → ℝ) (φ : α → Bit) (π : Policy A) : Transcript A → ℝ :=
  fun x => ∑ s, if (φ s, π (φ s), 0) = x then μ s else 0

/-- The fair seed with the identity decoder is exact for every policy. -/
theorem induced_fair {A : Type} [DecidableEq A] (π : Policy A) :
    induced fair id π = prescribedLaw π := by
  funext x
  simp only [induced, fair, id_eq, Fin.sum_univ_two]
  simpa [prescribed] using (prescribedLaw_cases π x).symm

/-- A seed law and first-reply map are exact when every policy receives its
prescribed transcript law. -/
def IsExact (A : Type) [DecidableEq A] {α : Type} [Fintype α]
    (μ : α → ℝ) (φ : α → Bit) : Prop :=
  ∀ π : Policy A, induced μ φ π = prescribedLaw π

theorem fair_exact (A : Type) [DecidableEq A] : IsExact A fair (id : Bit → Bit) :=
  induced_fair

/-! ### Entropy of the fair seed, and the envelope -/

theorem infoMass_half : infoMass ((1 : ℝ) / 2) = 1 := by
  unfold infoMass
  have hlogb : Real.logb 2 ((1 : ℝ) / 2) = -1 := by
    rw [Real.logb]
    have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    rw [hlog]
    field_simp
  rw [hlogb]
  norm_num

theorem fair_entropy : pmfEntropy fair = 1 := by
  unfold pmfEntropy
  have hterm : ∀ b : Bit, entTerm (fair b) = (1 / 2 : ℝ) := by
    intro b
    rw [show fair b = (1 : ℝ) / 2 by rfl,
      entTerm_of_pos (by norm_num : (0 : ℝ) < 1 / 2), infoMass_half]
    norm_num
  rw [sum_congr rfl fun b _ => hterm b, sum_const, card_univ, Fintype.card_fin]
  norm_num

/-- Each realized transcript of every policy has surprisal `1`. -/
theorem surprisal_one {A : Type} [DecidableEq A] (π : Policy A) (b : Bit) :
    infoMass (prescribedLaw π (prescribed π b)) = 1 := by
  rw [prescribedLaw_at, infoMass_half]

/-- Expected surprisal of a policy, summed over its two prescribed transcripts. -/
noncomputable def policySurprisal {A : Type} [DecidableEq A] (π : Policy A) : ℝ :=
  ∑ b : Bit, prescribedLaw π (prescribed π b) *
    infoMass (prescribedLaw π (prescribed π b))

/-- The envelope of this family is `L = 1`: every policy has expected surprisal
`1`. -/
theorem L_eq_one {A : Type} [DecidableEq A] (π : Policy A) :
    policySurprisal π = 1 := by
  unfold policySurprisal
  simp only [prescribedLaw_at, infoMass_half, Fin.sum_univ_two]
  norm_num

/-! ### One bit is necessary -/

/-- First-reply law of a seed and a first-reply map. -/
def firstLaw {α : Type} [Fintype α] (μ : α → ℝ) (φ : α → Bit) : Bit → ℝ :=
  fun b => ∑ s, if φ s = b then μ s else 0

/-- The first-reply law of an exact seed is the fair bit, as soon as there
is at least one action (so that a policy exists). -/
theorem firstLaw_of_exact (A : Type) [DecidableEq A] [Nonempty A]
    {α : Type} [Fintype α] (μ : α → ℝ) (φ : α → Bit) (h : IsExact A μ φ) :
    firstLaw μ φ = fair := by
  inhabit A
  let π : Policy A := fun _ => default
  funext b
  have hx : induced μ φ π (prescribed π b) = prescribedLaw π (prescribed π b) := by
    rw [h π]
  have hInd : induced μ φ π (prescribed π b) = firstLaw μ φ b := by
    unfold induced firstLaw prescribed
    refine sum_congr rfl fun s _ => ?_
    by_cases hs : φ s = b
    · simp [hs]
    · simp [hs, Prod.mk.injEq]
  have hPre : prescribedLaw π (prescribed π b) = (1 : ℝ) / 2 := prescribedLaw_at π b
  simpa [hInd, hPre, fair] using hx

/-- Entropy of a function is at most the entropy of the seed. -/
theorem entropy_ge_firstReply {α : Type} [Fintype α] (μ : α → ℝ)
    (h0 : ∀ s, 0 ≤ μ s) (φ : α → Bit) :
    pmfEntropy (firstLaw μ φ) ≤ pmfEntropy μ :=
  pmfEntropy_push_le μ h0 φ

theorem firstLaw_fair_entropy {α : Type} [Fintype α] (μ : α → ℝ) (φ : α → Bit)
    (hfair : firstLaw μ φ = fair) : pmfEntropy (firstLaw μ φ) = 1 := by
  rw [hfair, fair_entropy]

/-- If the first reply is a fair bit, the seed has entropy at least `1`. -/
theorem entropy_ge_one_of_fair_reply {α : Type} [Fintype α] (μ : α → ℝ)
    (h0 : ∀ s, 0 ≤ μ s) (φ : α → Bit) (hfair : firstLaw μ φ = fair) :
    1 ≤ pmfEntropy μ := by
  have hge := entropy_ge_firstReply μ h0 φ
  rw [firstLaw_fair_entropy μ φ hfair] at hge
  exact hge

/-- One bit is necessary: every exact seed (on a nonempty action type) has
entropy at least `1`. -/
theorem one_bit_necessary (A : Type) [DecidableEq A] [Nonempty A]
    {α : Type} [Fintype α] (μ : α → ℝ) (h0 : ∀ s, 0 ≤ μ s) (φ : α → Bit)
    (h : IsExact A μ φ) : 1 ≤ pmfEntropy μ :=
  entropy_ge_one_of_fair_reply μ h0 φ (firstLaw_of_exact A μ φ h)

/-- The causal cost of this family is `C = 1`: the fair bit is an exact seed
of entropy `1`, and every exact seed has entropy at least `1`. -/
theorem C_eq_one :
    (∀ (A : Type) [DecidableEq A], IsExact A fair (id : Bit → Bit)) ∧
      pmfEntropy fair = 1 ∧
      ∀ (A : Type) [DecidableEq A] [Nonempty A] {α : Type} [Fintype α]
        (μ : α → ℝ), (∀ s, 0 ≤ μ s) →
          ∀ φ : α → Bit, IsExact A μ φ → 1 ≤ pmfEntropy μ :=
  ⟨fair_exact, fair_entropy, one_bit_necessary⟩

/-! ### Correct marginals do not imply a shared realization -/

/-- The complementary bit. -/
def flipBit (b : Bit) : Bit := 1 - b

theorem flipBit_ne (b : Bit) : flipBit b ≠ b := by
  fin_cases b <;> decide

theorem flipBit_involutive (b : Bit) : flipBit (flipBit b) = b := by
  fin_cases b <;> decide

/-- The anti-coupling: friend `A` records `(U, a, 0)` and friend `B` records
`(1-U, b, 0)`, for a fair bit `U`. -/
def antiCouple {A : Type} [DecidableEq A] (a b : A) :
    Transcript A × Transcript A → ℝ :=
  fun p =>
    if p = (prescribed (fun _ => a) 0, prescribed (fun _ => b) 1) then (1 : ℝ) / 2
    else if p = (prescribed (fun _ => a) 1, prescribed (fun _ => b) 0) then (1 : ℝ) / 2
    else 0

theorem antiCouple_at {A : Type} [DecidableEq A] (a b : A) (u : Bit) :
    antiCouple a b (prescribed (fun _ => a) u, prescribed (fun _ => b) (flipBit u)) =
      1 / 2 := by
  fin_cases u <;> simp [antiCouple, prescribed, flipBit]

theorem anti_atoms_ne {A : Type} [DecidableEq A] (a b : A) :
    (prescribed (fun _ => a) 0, prescribed (fun _ => b) 1) ≠
      (prescribed (fun _ => a) 1, prescribed (fun _ => b) 0) := by
  intro h
  have := congrArg (fun p : Transcript A × Transcript A => p.1.1) h
  exact Fin.zero_ne_one this

/-- The `A`-marginal of the anti-coupling is the prescribed law of the constant
policy `a`. -/
theorem anti_marginal_A {A : Type} [DecidableEq A] (a _b : A) (x : Transcript A) :
    (∑ u : Bit,
        if (prescribed (fun _ => a) u) = x then (1 : ℝ) / 2 else 0) =
      prescribedLaw (fun _ => a) x := by
  simpa [Fin.sum_univ_two] using (prescribedLaw_cases (fun _ => a) x).symm

/-- The `B`-marginal of the anti-coupling is the prescribed law of the constant
policy `b`. (The first replies run through `1` and `0`, still each of mass
`1/2`.) -/
theorem anti_marginal_B {A : Type} [DecidableEq A] (_a b : A) (x : Transcript A) :
    (∑ u : Bit,
        if (prescribed (fun _ => b) (flipBit u)) = x then (1 : ℝ) / 2 else 0) =
      prescribedLaw (fun _ => b) x := by
  -- flipBit swaps the two bits, so the sum is the same as over `v`.
  have hflip : flipBit (0 : Bit) = 1 ∧ flipBit (1 : Bit) = 0 := by decide
  simp only [Fin.sum_univ_two, hflip.1, hflip.2]
  have := (prescribedLaw_cases (fun _ => b) x).symm
  -- right-hand side is (if π0 = x then 1/2 else 0) + (if π1 = x then 1/2 else 0)
  -- left after simp is (if π1 = x then 1/2 else 0) + (if π0 = x then 1/2 else 0)
  simpa [add_comm] using this

/-- Joint law induced by a shared causal decoder: both friends read the same
first reply `φ s` from a common seed atom. -/
def inducedCouple {A : Type} [DecidableEq A] {α : Type} [Fintype α]
    (μ : α → ℝ) (φ : α → Bit) (πA πB : Policy A) :
    Transcript A × Transcript A → ℝ :=
  fun p => ∑ s, if ((φ s, πA (φ s), 0), (φ s, πB (φ s), 0)) = p then μ s else 0

/-- A shared decoder returns the same first reply to both friends, on every
atom of positive mass. -/
theorem shared_first_replies {A : Type} [DecidableEq A] {α : Type} [Fintype α]
    (μ : α → ℝ) (φ : α → Bit) (πA πB : Policy A)
    (p : Transcript A × Transcript A) (hpos : inducedCouple μ φ πA πB p ≠ 0) :
    p.1.1 = p.2.1 := by
  unfold inducedCouple at hpos
  contrapose! hpos
  refine sum_eq_zero fun s _ => ?_
  split_ifs with h
  · have h1 : p.1.1 = φ s := by
      simpa using congrArg (fun q : Transcript A × Transcript A => q.1.1) h.symm
    have h2 : p.2.1 = φ s := by
      simpa using congrArg (fun q : Transcript A × Transcript A => q.2.1) h.symm
    exact (hpos (h1.trans h2.symm)).elim
  · rfl

/-- The anti-coupling puts mass `1/2` on a pair of opposite first replies, so
no shared decoder can place mass there. -/
theorem anti_atom_not_induced {A : Type} [DecidableEq A] {α : Type} [Fintype α]
    (μ : α → ℝ) (φ : α → Bit) (a b : A) :
    inducedCouple μ φ (fun _ => a) (fun _ => b)
      (prescribed (fun _ => a) 0, prescribed (fun _ => b) 1) = 0 := by
  unfold inducedCouple prescribed
  refine sum_eq_zero fun s _ => ?_
  split_ifs with h
  · have h0 : φ s = 0 := by
      simpa using congrArg (fun q : Transcript A × Transcript A => q.1.1) h
    have h1 : φ s = 1 := by
      simpa using congrArg (fun q : Transcript A × Transcript A => q.2.1) h
    exact (Fin.zero_ne_one (h0.symm.trans h1)).elim
  · rfl

/-- Correct marginals do not imply a shared realization. The anti-coupling of
constant policies `a` and `b ≠ a` has both prescribed marginals, and equals
no joint induced by a shared causal decoder. -/
theorem anti_not_shared {A : Type} [DecidableEq A] (a b : A) (_hne : a ≠ b)
    {α : Type} [Fintype α] (μ : α → ℝ) (φ : α → Bit) :
    inducedCouple μ φ (fun _ => a) (fun _ => b) ≠ antiCouple a b := by
  intro h
  have hmass := congrFun h (prescribed (fun _ => a) 0, prescribed (fun _ => b) 1)
  have h0 := anti_atom_not_induced μ φ a b
  have h1 : antiCouple a b (prescribed (fun _ => a) 0, prescribed (fun _ => b) 1) =
      (1 : ℝ) / 2 := by
    simpa [flipBit] using antiCouple_at a b 0
  rw [h0, h1] at hmass
  exact (by norm_num : (0 : ℝ) ≠ 1 / 2) hmass

/-- Combined statement: the anti-coupling has the two prescribed marginals,
and is not the joint of any shared causal decoder. -/
theorem marginals_not_shared {A : Type} [DecidableEq A] (a b : A) (hne : a ≠ b) :
    (∀ x, (∑ u : Bit, if prescribed (fun _ => a) u = x then (1 : ℝ) / 2 else 0) =
        prescribedLaw (fun _ => a) x) ∧
      (∀ x, (∑ u : Bit, if prescribed (fun _ => b) (flipBit u) = x then (1 : ℝ) / 2 else 0) =
          prescribedLaw (fun _ => b) x) ∧
      ∀ {α : Type} [Fintype α] (μ : α → ℝ) (φ : α → Bit),
        inducedCouple μ φ (fun _ => a) (fun _ => b) ≠ antiCouple a b :=
  ⟨anti_marginal_A a b, anti_marginal_B a b, fun μ φ => anti_not_shared a b hne μ φ⟩

end OneBitFriends
end CausalSpectrum

end
