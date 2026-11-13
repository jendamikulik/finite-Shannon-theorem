/-
All-knowing now, everything thinks.

The now is the answer sheet of one finite world. A thought is one
coordinate of that sheet. Reading every coordinate costs nothing more
than the sheet, because each coordinate is a function of it. A loop
asks those coordinates one at a time; the seed stays fixed and the
conditional entropy of the sheet does not rise. On the two-bit sheet
the three gaps are `2`, `1` and `0`.

An independent later question is not a coordinate of the sheet.
`H(N, C) = H(N) + H(C)`, so the now does not shrink the question, while
`H(Z | N, C) = 0`: once the question is asked, the answer is the
corresponding coordinate. A fixed sheet whose two entries differ makes
that missing bit exactly one.

Not proved: that a mind is this sheet; that a later free choice already
sits in the record; anything about noncommuting observables; anything
about the zeros of `ξ`.
-/
import CausalSeed.Sharing
import CausalSeed.ValueGap

noncomputable section

open Classical Sharing Finset

namespace CausalSpectrum
namespace AllKnowing

/-! ### The sheet and one thought -/

variable {Ω Q Y : Type}

/-- Every answer, indexed by the question. -/
def sheet (A : Q → Ω → Y) (ω : Ω) : Q → Y := fun q => A q ω

/-- One coordinate of a sheet. -/
def thought (q : Q) (s : Q → Y) : Y := s q

theorem thought_of_sheet (A : Q → Ω → Y) (q : Q) :
    thought q ∘ sheet A = A q := rfl

/-- The next question appends one answer of the same world. -/
def ask (A : Q → Ω → Y) (h : List (Q × Y)) (q : Q) (ω : Ω) : List (Q × Y) :=
  h ++ [(q, A q ω)]

theorem loop_same_seed (A : Q → Ω → Y) (q₀ q₁ : Q) (ω : Ω) :
    ask A (ask A [] q₀ ω) q₁ ω = [(q₀, A q₀ ω), (q₁, A q₁ ω)] := by
  simp [ask]

/-- Two worlds agree on a set of questions. -/
def agrees (asked : Finset Q) (A : Q → Ω → Y) (ω ω' : Ω) : Prop :=
  ∀ q ∈ asked, A q ω = A q ω'

theorem agrees_mono {asked asked' : Finset Q} (hsub : asked ⊆ asked')
    (A : Q → Ω → Y) {ω ω' : Ω} (h : agrees asked' A ω ω') :
    agrees asked A ω ω' :=
  fun q hq => h q (hsub hq)

/-- The asked coordinates already determine the whole sheet. -/
def separates (asked : Finset Q) (A : Q → Ω → Y) : Prop :=
  ∀ ω ω', agrees asked A ω ω' → sheet A ω = sheet A ω'

theorem separates_univ [Fintype Q] [DecidableEq Q] (A : Q → Ω → Y) :
    separates univ A := by
  intro ω ω' h
  funext q
  exact h q (mem_univ q)

/-- End of the loop: agreement on a separating family is agreement of sheets. -/
theorem end_of_loop {asked : Finset Q} {A : Q → Ω → Y}
    (hsep : separates asked A) {ω ω' : Ω} (h : agrees asked A ω ω') :
    sheet A ω = sheet A ω' :=
  hsep ω ω' h

/-- First entry, then one of two continuations. The continuation is a `Bool`. -/
def record (B C₀ C₁ : Ω → Y) (π : Bool) (ω : Ω) : Y × Y :=
  (B ω, if π then C₀ ω else C₁ ω)

theorem first_shared (B C₀ C₁ : Ω → Y) (π π' : Bool) (ω : Ω) :
    (record B C₀ C₁ π ω).1 = (record B C₀ C₁ π' ω).1 := rfl

/-- The later coordinate can differ while the first stays put. -/
theorem later_can_differ :
    record (fun _ : Bool => false) (fun b => b) (fun b => !b) false true ≠
      record (fun _ : Bool => false) (fun b => b) (fun b => !b) true true := by
  simp [record]

/-! ### Conditional entropy of a coordinate -/

variable [Fintype Ω] [DecidableEq Ω] [Fintype Q] [DecidableEq Q]
  [Fintype Y] [DecidableEq Y]

/-- Joint law of the sheet and one of its coordinates. -/
def pushGraph (μ : Ω → ℝ) (A : Q → Ω → Y) (q : Q) : (Q → Y) × Y → ℝ :=
  fun p => ∑ ω, if (sheet A ω, A q ω) = p then μ ω else 0

theorem pushGraph_nonneg {μ : Ω → ℝ} (h0 : ∀ ω, 0 ≤ μ ω) (A : Q → Ω → Y) (q : Q)
    (p : (Q → Y) × Y) : 0 ≤ pushGraph μ A q p :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact h0 _
    · exact le_refl 0

theorem pushGraph_total {μ : Ω → ℝ} (htot : ∑ ω, μ ω = 1) (A : Q → Ω → Y) (q : Q) :
    ∑ p, pushGraph μ A q p = 1 := by
  unfold pushGraph
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  simp [htot]

theorem pushGraph_off {μ : Ω → ℝ} (A : Q → Ω → Y) (q : Q) (s : Q → Y) (y : Y)
    (hy : y ≠ s q) : pushGraph μ A q (s, y) = 0 := by
  unfold pushGraph
  refine Finset.sum_eq_zero fun ω _ => ?_
  have hne : (sheet A ω, A q ω) ≠ (s, y) := by
    intro h
    have hAq : A q ω = s q := by
      simpa [sheet] using congrFun (congrArg Prod.fst h) q
    have hy' : A q ω = y := congrArg Prod.snd h
    exact hy (hy'.symm.trans hAq)
  simp [hne]

/-- Every coordinate is a function of the sheet. `H(A_q | N) = 0`. -/
theorem thought_given_now {μ : Ω → ℝ} (h0 : ∀ ω, 0 ≤ μ ω) (htot : ∑ ω, μ ω = 1)
    (A : Q → Ω → Y) (q : Q) : condEntropy (pushGraph μ A q) = 0 := by
  exact condEntropy_of_dependent (pushGraph_nonneg h0 A q) (fun s => s q)
    fun s y hy => pushGraph_off A q s y hy

/-- Joint law of the sheet with itself. -/
def pushDiag (μ : Ω → ℝ) (A : Q → Ω → Y) : (Q → Y) × (Q → Y) → ℝ :=
  fun p => ∑ ω, if (sheet A ω, sheet A ω) = p then μ ω else 0

theorem pushDiag_nonneg {μ : Ω → ℝ} (h0 : ∀ ω, 0 ≤ μ ω) (A : Q → Ω → Y)
    (p : (Q → Y) × (Q → Y)) : 0 ≤ pushDiag μ A p :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact h0 _
    · exact le_refl 0

theorem pushDiag_total {μ : Ω → ℝ} (htot : ∑ ω, μ ω = 1) (A : Q → Ω → Y) :
    ∑ p, pushDiag μ A p = 1 := by
  unfold pushDiag
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  simp [htot]

theorem pushDiag_off {μ : Ω → ℝ} (A : Q → Ω → Y) (x y : Q → Y) (hy : y ≠ x) :
    pushDiag μ A (x, y) = 0 := by
  unfold pushDiag
  refine Finset.sum_eq_zero fun ω _ => ?_
  have hne : (sheet A ω, sheet A ω) ≠ (x, y) := by
    intro h
    exact hy ((congrArg Prod.snd h).symm.trans (congrArg Prod.fst h))
  simp [hne]

/-- Reading the whole sheet again costs nothing. `H(Θ | N) = 0`. -/
theorem everything_given_now {μ : Ω → ℝ} (h0 : ∀ ω, 0 ≤ μ ω)
    (htot : ∑ ω, μ ω = 1) (A : Q → Ω → Y) : condEntropy (pushDiag μ A) = 0 := by
  exact condEntropy_of_dependent (pushDiag_nonneg h0 A) id
    fun x y hy => pushDiag_off A x y hy

/-! ### Two bits: the loop shrinks by one coordinate at a time -/

/-- Fair bit. -/
def fair : Bool → ℝ := bernoulli (1 / 2)

theorem fair_nonneg (b : Bool) : 0 ≤ fair b :=
  bernoulli_nonneg (by norm_num) (by norm_num) b

theorem fair_total : ∑ b, fair b = 1 :=
  bernoulli_total (1 / 2)

theorem fair_entropy : H fair = 1 := by
  rw [fair, bernoulli_entropy (by norm_num) (by norm_num), ValueGap.binEntropy_half]

/-- One world, two independent fair bits. -/
def world : Bool × Bool → ℝ := indepJoint fair fair

theorem world_nonneg (ω : Bool × Bool) : 0 ≤ world ω :=
  indepJoint_nonneg fair_nonneg fair_nonneg ω

theorem world_total : ∑ ω, world ω = 1 :=
  indepJoint_total fair_total fair_total

theorem world_entropy : H world = 2 := by
  unfold world
  have hcost := indep_cost fair_nonneg fair_nonneg fair_total fair_total
  have hH := sharing_criterion (indepJoint fair fair) world_nonneg world_total
  have hsum : H fair + H fair = 2 := by rw [fair_entropy]; norm_num
  linarith

/-- The sheet of the two bits. `0` reads the first, `1` the second. -/
def toSheet : (Bool × Bool) ≃ (Fin 2 → Bool) where
  toFun
    | (b, c) => fun q => if q = 0 then b else c
  invFun f := (f 0, f 1)
  left_inv := by
    intro ω
    cases ω
    simp
  right_inv := by
    intro f
    funext q
    fin_cases q <;> simp

/-- Law of the sheet. -/
def nowLaw (f : Fin 2 → Bool) : ℝ := world (toSheet.symm f)

theorem now_nonneg (f : Fin 2 → Bool) : 0 ≤ nowLaw f :=
  world_nonneg _

theorem now_total : ∑ f, nowLaw f = 1 := by
  simpa [nowLaw] using (Equiv.sum_comp toSheet.symm world).trans world_total

theorem now_entropy : H nowLaw = 2 := by
  unfold nowLaw
  exact (H_bijection toSheet world).trans world_entropy

/-- Questions on the two-bit world. -/
def ans : Fin 2 → Bool × Bool → Bool
  | 0, ω => ω.1
  | 1, ω => ω.2

theorem one_question_does_not_separate :
    ¬ separates (insert (0 : Fin 2) ∅) ans := by
  intro h
  have hagree : agrees (insert 0 ∅) ans (false, false) (false, true) := by
    intro q hq
    simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hq
    subst hq
    rfl
  have hsheet := h (false, false) (false, true) hagree
  have := congrFun hsheet 1
  simp [sheet, ans] at this

theorem both_questions_separate : separates (univ : Finset (Fin 2)) ans :=
  separates_univ ans

/-- Nothing has been asked: the sheet given a trivial history. -/
def gapEmpty : Unit × (Fin 2 → Bool) → ℝ :=
  fun p => ∑ f, if (((), f) : Unit × (Fin 2 → Bool)) = p then nowLaw f else 0

theorem gapEmpty_apply (f : Fin 2 → Bool) : gapEmpty ((), f) = nowLaw f := by
  unfold gapEmpty
  rw [Finset.sum_eq_single f]
  · simp
  · intro f' _ hne
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ f) h

theorem gapEmpty_nonneg (p : Unit × (Fin 2 → Bool)) : 0 ≤ gapEmpty p := by
  cases p with
  | mk u f =>
    cases u
    rw [gapEmpty_apply]
    exact now_nonneg f

theorem gapEmpty_total : ∑ p, gapEmpty p = 1 := by
  unfold gapEmpty
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  simp [now_total]

theorem gapEmpty_entropy : H gapEmpty = 2 := by
  unfold H pmfEntropy
  rw [Fintype.sum_prod_type]
  have hunit : ∀ f, entTerm (gapEmpty ((), f)) = entTerm (nowLaw f) := by
    intro f
    simp [gapEmpty_apply]
  simp only [hunit, Finset.univ_unique, Finset.sum_singleton]
  simpa [H, pmfEntropy] using now_entropy

theorem gapEmpty_marginal : marginal gapEmpty = fun _ => 1 := by
  funext u
  cases u
  unfold marginal
  simp only [gapEmpty_apply, Finset.univ_unique, Finset.sum_singleton]
  exact now_total

theorem gapEmpty_image_entropy : H (marginal gapEmpty) = 0 := by
  rw [gapEmpty_marginal]
  unfold H pmfEntropy
  simp [Finset.univ_unique, entTerm_one]

theorem gapEmpty_cond : condEntropy gapEmpty = 2 := by
  have hchain := chain_rule gapEmpty_nonneg gapEmpty_total
  linarith [gapEmpty_entropy, gapEmpty_image_entropy]

/-- One coordinate has been asked. The second factor is still the sheet. -/
def residual : Bool × (Fin 2 → Bool) → ℝ :=
  fun p => ∑ f, if (f 0, f) = p then nowLaw f else 0

theorem residual_apply (b : Bool) (f : Fin 2 → Bool) :
    residual (b, f) = if f 0 = b then nowLaw f else 0 := by
  unfold residual
  rw [Finset.sum_eq_single f]
  · simp
  · intro f' _ hne
    have hpair : (f' 0, f') ≠ (b, f) := by
      intro h
      exact hne (congrArg Prod.snd h)
    simp [hpair]
  · intro h
    exact absurd (Finset.mem_univ f) h

theorem residual_nonneg (p : Bool × (Fin 2 → Bool)) : 0 ≤ residual p := by
  rcases p with ⟨b, f⟩
  rw [residual_apply]
  split_ifs
  · exact now_nonneg f
  · exact le_refl 0

theorem residual_total : ∑ p, residual p = 1 := by
  unfold residual
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  simp [now_total]

theorem residual_entropy : H residual = 2 := by
  unfold H pmfEntropy
  rw [Fintype.sum_prod_type]
  have hterm : ∀ b f, entTerm (residual (b, f)) =
      if b = f 0 then entTerm (nowLaw f) else 0 := by
    intro b f
    rw [residual_apply]
    by_cases h : f 0 = b
    · simp [h]
    · rw [if_neg h, entTerm_zero, if_neg (Ne.symm h)]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hcollapse : ∑ f, ∑ b, (if b = f 0 then entTerm (nowLaw f) else 0) =
      ∑ f, entTerm (nowLaw f) := by
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_eq_single (f 0)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ (f 0)) h
  rw [hcollapse]
  simpa [H, pmfEntropy] using now_entropy

theorem nowLaw_quarter (f : Fin 2 → Bool) : nowLaw f = 1 / 4 := by
  have hsym : toSheet.symm f = (f 0, f 1) := rfl
  rw [nowLaw, hsym]
  simp only [world, indepJoint, fair, bernoulli]
  cases h0 : f 0 <;> cases h1 : f 1 <;> norm_num

theorem residual_marginal (b : Bool) : marginal residual b = fair b := by
  unfold marginal
  simp_rw [residual_apply, nowLaw_quarter]
  have hcomp := Equiv.sum_comp toSheet (fun f => if f 0 = b then (1 : ℝ) / 4 else 0)
  have hpoint : ∀ ω : Bool × Bool,
      (if (toSheet ω) 0 = b then (1 : ℝ) / 4 else 0) =
        if ω.1 = b then (1 : ℝ) / 4 else 0 := by
    rintro ⟨b', c⟩
    simp [toSheet]
  rw [← hcomp]
  simp_rw [hpoint, Fintype.sum_prod_type]
  have hinner : ∀ b' : Bool, ∑ c : Bool, (if b' = b then (1 : ℝ) / 4 else 0) =
      if b' = b then (1 : ℝ) / 2 else 0 := by
    intro b'
    cases b' <;> cases b <;>
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool] <;> norm_num
  simp_rw [hinner]
  cases b <;> simp [fair, bernoulli, Finset.sum_const, Finset.card_univ, Fintype.card_bool] <;>
    norm_num

theorem residual_image_entropy : H (marginal residual) = 1 := by
  have hfun : marginal residual = fair := funext residual_marginal
  simpa [hfun] using fair_entropy

theorem residual_cond : condEntropy residual = 1 := by
  have hchain := chain_rule residual_nonneg residual_total
  linarith [residual_entropy, residual_image_entropy]

/-- Both coordinates have been asked. -/
def gapBoth : (Fin 2 → Bool) × (Fin 2 → Bool) → ℝ :=
  fun p => ∑ f, if (f, f) = p then nowLaw f else 0

theorem gapBoth_nonneg (p : (Fin 2 → Bool) × (Fin 2 → Bool)) : 0 ≤ gapBoth p :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact now_nonneg _
    · exact le_refl 0

theorem gapBoth_total : ∑ p, gapBoth p = 1 := by
  unfold gapBoth
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  simp [now_total]

theorem gapBoth_off (x y : Fin 2 → Bool) (hy : y ≠ x) : gapBoth (x, y) = 0 := by
  unfold gapBoth
  refine Finset.sum_eq_zero fun f _ => ?_
  have hne : (f, f) ≠ (x, y) := by
    intro h
    exact hy ((congrArg Prod.snd h).symm.trans (congrArg Prod.fst h))
  simp [hne]

theorem gapBoth_cond : condEntropy gapBoth = 0 :=
  condEntropy_of_dependent gapBoth_nonneg id gapBoth_off

/-- The gaps after asking nothing, the first bit, and both bits. -/
theorem loop_gap :
    condEntropy gapEmpty = 2 ∧ condEntropy residual = 1 ∧ condEntropy gapBoth = 0 :=
  ⟨gapEmpty_cond, residual_cond, gapBoth_cond⟩

theorem loop_shrinks :
    condEntropy gapBoth ≤ condEntropy residual ∧
      condEntropy residual ≤ condEntropy gapEmpty := by
  rcases loop_gap with ⟨h0, h1, h2⟩
  constructor <;> linarith

/-! ### The question is not a coordinate of the now -/

/-- Fair choice of which coordinate to read. -/
def coin : Fin 2 → ℝ := fun _ => 1 / 2

def coinEq : Fin 2 ≃ Bool where
  toFun i := i = 1
  invFun b := if b then 1 else 0
  left_inv := by
    intro i
    fin_cases i <;> simp
  right_inv := by
    intro b
    cases b <;> simp

theorem coin_nonneg (i : Fin 2) : 0 ≤ coin i := by
  simp [coin]

theorem coin_total : ∑ i, coin i = 1 := by
  simp [coin, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem coin_entropy : H coin = 1 := by
  have hbij := H_bijection coinEq.symm fair
  have hcoin : coin = fun i => fair (coinEq i) := by
    funext i
    fin_cases i <;> simp [coin, fair, bernoulli, coinEq] <;> norm_num
  simpa [hcoin] using hbij.trans fair_entropy

/-- Sheet and an independent choice of coordinate. -/
def choose : (Fin 2 → Bool) × Fin 2 → ℝ := indepJoint nowLaw coin

theorem choose_nonneg (p : (Fin 2 → Bool) × Fin 2) : 0 ≤ choose p :=
  indepJoint_nonneg now_nonneg coin_nonneg p

theorem choose_total : ∑ p, choose p = 1 :=
  indepJoint_total now_total coin_total

theorem indep_condEntropy
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {p : X → ℝ} {q : Y → ℝ}
    (hq : ∑ y, q y = 1) (hp : ∑ x, p x = 1) :
    condEntropy (indepJoint p q) = H q := by
  unfold condEntropy
  have hterm : ∀ x, marginal (indepJoint p q) x * H (condProb (indepJoint p q) x) =
      p x * H q := by
    intro x
    by_cases hx : p x = 0
    · rw [indep_marginal hq, hx, zero_mul, zero_mul]
    · have hfun : condProb (indepJoint p q) x = q := by
        funext y
        rw [condProb, indepJoint, indep_marginal hq, if_neg hx]
        exact mul_div_cancel_left₀ (q y) hx
      rw [hfun, indep_marginal hq]
  simp_rw [hterm, ← Finset.sum_mul, hp, one_mul]

theorem choose_entropy : H choose = H nowLaw + H coin := by
  unfold choose
  have hcost := indep_cost now_nonneg coin_nonneg now_total coin_total
  have hH := sharing_criterion (indepJoint nowLaw coin) choose_nonneg choose_total
  linarith

theorem choose_cond : condEntropy choose = H coin :=
  indep_condEntropy coin_total now_total

/-- The answer read at the chosen coordinate. -/
def readout : ((Fin 2 → Bool) × Fin 2) × Bool → ℝ :=
  fun p => ∑ s, if (s, s.1 s.2) = p then choose s else 0

theorem readout_nonneg (p : ((Fin 2 → Bool) × Fin 2) × Bool) : 0 ≤ readout p :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact choose_nonneg _
    · exact le_refl 0

theorem readout_off (s : (Fin 2 → Bool) × Fin 2) (y : Bool) (hy : y ≠ s.1 s.2) :
    readout (s, y) = 0 := by
  unfold readout
  refine Finset.sum_eq_zero fun s' _ => ?_
  have hne : (s', s'.1 s'.2) ≠ (s, y) := by
    intro h
    have hs : s' = s := congrArg Prod.fst h
    have hy' : s'.1 s'.2 = y := congrArg Prod.snd h
    exact hy (hy'.symm.trans (by simp [hs]))
  simp [hne]

theorem readout_cond : condEntropy readout = 0 :=
  condEntropy_of_dependent readout_nonneg (fun s => s.1 s.2) readout_off

/-- The now does not contain the question. Given both, the answer is free. -/
theorem no_backward_message :
    H choose = H nowLaw + H coin ∧
      condEntropy choose = H coin ∧
      H coin = 1 ∧
      condEntropy readout = 0 :=
  ⟨choose_entropy, choose_cond, coin_entropy, readout_cond⟩

theorem not_read_choice_from_now : ¬ FunctionallyDependent choose := by
  intro h
  have hzero := (condEntropy_eq_zero_iff choose_nonneg choose_total).2 h
  have hone : condEntropy choose = 1 := by
    rw [choose_cond, coin_entropy]
  linarith

/-! ### A fixed sheet with two different entries costs one bit -/

/-- Morning table: the two stored bits differ. -/
def table : Fin 2 → Bool
  | 0 => false
  | 1 => true

theorem table_diff : table 0 ≠ table 1 := by
  simp [table]

/-- Joint of the fair choice and the bit it reads on `table`. -/
def tableJoint : Fin 2 × Bool → ℝ :=
  fun p => ∑ c, if (c, table c) = p then coin c else 0

theorem tableJoint_nonneg (p : Fin 2 × Bool) : 0 ≤ tableJoint p :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact coin_nonneg _
    · exact le_refl 0

theorem tableJoint_total : ∑ p, tableJoint p = 1 := by
  unfold tableJoint
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact coin_total

theorem tableJoint_off (c : Fin 2) (y : Bool) (hy : y ≠ table c) :
    tableJoint (c, y) = 0 := by
  unfold tableJoint
  refine Finset.sum_eq_zero fun c' _ => ?_
  have hne : (c', table c') ≠ (c, y) := by
    intro h
    have hc : c' = c := congrArg Prod.fst h
    have hy' : table c' = y := congrArg Prod.snd h
    exact hy (hy'.symm.trans (by simp [hc]))
  simp [hne]

theorem tableJoint_cond : condEntropy tableJoint = 0 :=
  condEntropy_of_dependent tableJoint_nonneg table tableJoint_off

theorem tableJoint_marginal (c : Fin 2) : marginal tableJoint c = coin c := by
  unfold marginal
  rw [Finset.sum_eq_single (table c)]
  · unfold tableJoint
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hne
      have hpair : (c', table c') ≠ (c, table c) := by
        intro h
        exact hne (congrArg Prod.fst h)
      simp [hpair]
    · intro h
      exact absurd (Finset.mem_univ c) h
  · intro y _ hy
    exact tableJoint_off c y hy
  · intro h
    exact absurd (Finset.mem_univ (table c)) h

theorem table_marginal_entropy : H (marginal tableJoint) = 1 := by
  have hfun : marginal tableJoint = coin := funext tableJoint_marginal
  simpa [hfun] using coin_entropy

/-- `H(Z | R) - H(Z | R, C) = 1` for this fixed table.
`R` is constant, so the first term is the entropy of the fair choice,
and the second term is `tableJoint`'s conditional entropy. -/
theorem table_gap :
    H (marginal tableJoint) - condEntropy tableJoint = 1 := by
  rw [table_marginal_entropy, tableJoint_cond]
  norm_num

end AllKnowing
end CausalSpectrum
