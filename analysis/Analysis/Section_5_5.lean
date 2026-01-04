import Mathlib.Tactic
import Analysis.Section_5_4


/-!
# Analysis I, Section 5.5: The least upper bound property

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds).  Here we use the `upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

open Real in
/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  rw [upperBound_def]
  constructor
  · intro h
    exact h _ ⟨zero_le_one, le_refl _⟩
  intro hM x hx
  exact hx.right.trans hM


/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl

open Real in
/-- Example 5.5.3 -/
example : ¬ ∃ M : Real, M ∈ upperBounds (.Ioi 0) := by
  by_contra!
  obtain ⟨M, hM⟩ := this
  rw [mem_upperBounds] at hM
  by_cases Mpos : M ≤ 0
  · replace hM := hM 1
    refine zero_lt_one.not_ge (hM ?_ |>.trans Mpos)
    exact Set.mem_Ioi.mpr zero_lt_one
  replace hM := mem_upperBounds.mp hM (M + 1) (not_le.mp Mpos |>.trans (lt_add_one M))
  exact (lt_add_one M).not_ge hM

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) :=
  fun _M => mem_upperBounds.mpr fun _x hx => hx.elim

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
  M' ∈ upperBounds E := by
    refine mem_upperBounds.mpr fun x hx => ?_
    exact mem_upperBounds.mp hb x hx |>.trans h

/-- Definition 5.5.5 (least upper bound).  Here we use the `isLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc 0 1) (1 : Real) := by
  refine ⟨fun x hx => hx.right, ?_⟩
  intro M hM
  exact hM ⟨zero_le_one, le_refl _⟩

/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  by_contra!
  obtain ⟨M, _, hM⟩ := this
  specialize hM (a := M - 1) (fun x h => h.elim)
  exact (sub_one_lt M).not_ge hM

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by 
  grind [Real.isLUB_def]

/-- definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

/-- Exercise 5.5.2 -/
theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: K*((1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: L*((1/(n+1):ℚ):Real) ∉ upperBounds E) :
  ∃ m, L < m
  ∧ m ≤ K
  ∧ m * ((1/(n+1):ℚ):Real) ∈ upperBounds E
  ∧ (m-1) * ((1/(n+1):ℚ):Real) ∉ upperBounds E := by
    sorry
    /- induction n -/
    /- case zero => -/
      /- by_contra!  -/
      /- have _1 := this K hLK (le_refl _) hK -/
      /- have (k: ℕ) : (K - k: Real) ∈ upperBounds E := by -/
      /-   induction k -/
      /-   case zero => simpa using hK -/
      /-   case succ k ih => -/


/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
  (hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
  (hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
    m = m' := by sorry

/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by
    rw [coe] at ha ⊢
    peel 7 ha with ε εpos N j hj k hk ha
    rw [Pi.abs_apply, Pi.abs_apply]
    refine le_trans ?_ ha
    exact abs_abs_sub_abs_le _ _

open Sequence (IsCauchy) in
theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
  (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by
    rw [LIM_eq_LIM (IsCauchy.abs ha) (IsCauchy.abs hb)]
    rw [LIM_eq_LIM ha hb] at h
    rw [Sequence.equiv_iff] at h ⊢
    peel 5 h with ε εpos N n hn h
    refine le_trans ?_ h
    exact abs_abs_sub_abs_le _ _

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
  LIM a = LIM |a| := by
    rw [LIM_eq_LIM ha (Sequence.IsCauchy.abs ha), Sequence.equiv_iff]
    obtain ⟨b, ⟨c, cpos, hb⟩, hb', h⟩ := h
    rw [zero_sub, neg_eq_iff_eq_neg, neg_LIM _ hb', 
      LIM_eq_LIM ha (Sequence.IsCauchy.neg _ hb'), Sequence.equiv_iff] at h
    intro ε εpos
    obtain ⟨M, Mpos, hM⟩ := Sequence.isBounded_of_isCauchy hb'
    replace hM := Sequence.boundedBy_iff.mp hM
    by_cases hMeq: M = ε / 2
    · sorry
    obtain ⟨N, h⟩ := h (|ε / 2 - M|) (abs_sub_pos.mpr fun h ↦ hMeq h.symm)
    refine ⟨N, fun n hn => ?_⟩
    calc
    _ = |(a n - |a n|)| := by rw [Pi.abs_apply]
    _ ≤ |a n| + |(|a n|)| := abs_sub _ _
    _ = 2 * |a n| := by rw [abs_abs, ← two_mul]
    _ = 2 * |a n| := by ring_nf
    _ ≤ 2 * (ε / 2) := by
      refine Rat.mul_le_mul_of_nonneg_left ?_ zero_le_two 
      have := cpos.trans_le (le_neg_of_le_neg <| hb n) |> neg_of_neg_pos
      replace hM := _root_.abs_of_neg this ▸ hM n |> neg_le_of_neg_le
      calc
      _ = |a n + b n - b n| := by ring_nf
      _ ≤ |a n + b n| + |b n| := abs_sub _ _
      _ = |a n + b n| - b n := by rw [_root_.abs_of_neg this, ← _root_.sub_eq_add_neg]
      /- _ ≤ |ε / 2 - M| - -M := sub_le_sub _ hM -/
      /- _ ≤ |ε/2 - M| + M := add_le_add (by simpa using h n hn) (hM n |>.trans (le_abs_self _))  -/
      /- _ ≤ |ε/2 - M + M| := by sorry -/
      _ = _ := by sorry
    _ = _ := by sorry

theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by
  wlog h: 0 < LIM a
  · rcases le_iff_lt_or_eq.mp (not_lt.mp h) with h|h
    · specialize this (.neg _ ha) (by rwa [← neg_LIM _ ha, neg_pos])
      rwa [← neg_LIM _ ha, abs_neg, abs_neg] at this
    symm
    rw [h, abs_zero, ofNat_def, LIM_eq_LIM (.abs ha) (.const _), Sequence.equiv_iff]
    rw [ofNat_def, LIM_eq_LIM ha (.const _), Sequence.equiv_iff] at h
    peel 5 h with ε εpos N n hn h
    simpa using h
  rw [← LIM.abs_eq_pos h ha, _root_.abs_of_pos h]

open Sequence.IsCauchy (coe) in
theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
  (h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by 
    obtain ⟨N, h⟩ := h
    obtain ⟨q, hq⟩ := rat_between (sub_one_lt x)
    let a' (n) := if N ≤ n then a n else q
    have ha': Sequence.IsCauchy a' := coe _ |>.mpr (by
      rw [coe] at hcauchy
      rintro ε εpos
      obtain ⟨N', h⟩ := hcauchy ε εpos
      refine ⟨max N' N, fun j hj k hk => ?_⟩
      convert (config := .unfoldSameFun) 
        h j (le_of_max_le_left hj) k (le_of_max_le_left hk)
      all_goals
        unfold a'
        rw [if_pos]
        exact le_of_max_le_right (by assumption)
    )
    have haa': Sequence.Equiv a a' := Sequence.equiv_iff _ _ |>.mpr (by
      refine fun ε εpos => ⟨N, fun n hn => ?_⟩
      unfold a'
      rw [if_pos hn, sub_self, abs_zero]
      exact εpos.le
    )
    rw [LIM_eq_LIM hcauchy ha' |>.mpr haa']
    refine LIM_of_le ha' fun n => ?_
    unfold a'
    split_ifs with hn 
    · exact h _ hn
    exact hq.right.le

/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := by sorry

/--
The sequence m₁, m₂, … is well-defined.
This proof uses a different indexing convention than the text
-/
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real)
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  . rw [bddAbove_def] at hbound; obtain ⟨ M, hbound ⟩ := hbound
    choose K _ hK using le_mul hpos M
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by grind [upperBound_def]
    have claim1_3 : (K:Real) > (L:Real) := by
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]
    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      . qify; rwa [←gt_iff_lt, gt_of_coe]
      simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  grind [upperBound_discrete_unique]

lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    split_ands
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [←neg_le_neg_iff] at bound3; rw [Pi.sub_apply] at bound1; grind
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- This proof is written to follow the structure of the original text.
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem
  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hb : (b:Sequence).IsCauchy := .harmonic'
  have hm1 (n:ℕ) := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  have claim2 (N:ℕ) := LUB_claim2 N (by aesop) hm1 hm2
  have claim3 : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1
  set S := LIM a; use S
  have claim4 : S = LIM (a - b) := by
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub claim3 hb, S, this]
  rw [isLUB_def, upperBound_def]
  constructor
  . intro x hx
    refine LIM_of_ge claim3 fun n => ?_
    simp_all only [one_div, Rat.cast_div, Rat.cast_intCast, Rat.cast_add, Rat.cast_natCast, Rat.cast_one,
      Rat.cast_sub, Rat.cast_inv, Pi.sub_apply, ge_iff_le, x₀, b, a, m, S]
    exact hm1 _ hx
  intro y hy
  have claim5 (n:ℕ) : y ≥ (a-b) n := by contrapose! hm2; use n; apply upperBound_upper _ hy; order
  rw [claim4]
  refine LIM_of_le ?_ claim5
  exact claim3.sub hb

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers ⊤ to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers ⊥ to denote the -∞ element.-/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := neg_infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [hnon, hb, sup]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]

/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two : ∃ x:Real, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  set E := { y:Real | y ≥ 0 ∧ y^2 < 2 }
  have claim1: 2 ∈ upperBounds E := by
    rw [upperBound_def]
    intro y hy; simp [E] at hy; contrapose! hy
    intro hpos
    calc
      _ ≤ 2 * 2 := by norm_num
      _ ≤ y * y := by gcongr
      _ = y^2 := by ring
  have claim1' : BddAbove E := by rw [bddAbove_def]; use 2
  have claim2: 1 ∈ E := by simp [E]
  observe claim2': E.Nonempty
  set x := ((ExtendedReal.sup E):Real)
  have claim3 : IsLUB E x := by grind [ExtendedReal.sup_of_bounded]
  have claim4 : x ≥ 1 := by grind [isLUB_def, upperBound_def]
  have claim5 : x ≤ 2 := by grind [isLUB_def]
  have claim6 : x.IsPos := by rw [isPos_iff]; linarith
  use x; obtain h | h | h := trichotomous' (x^2) 2
  . have claim11: ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 - 4*ε > 2 := by
      set ε := min (1/2) ((x^2-2)/8)
      have hx : x^2 - 2 > 0 := by linarith
      have hε : 0 < ε := by positivity
      observe hε1: ε ≤ 1/2
      observe hε2: ε ≤ (x^2-2)/8
      refine' ⟨ ε, hε, _, _ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim11
    have claim12: (x-ε)^2 > 2 := calc
      _ = x^2 - 2 * ε * x + ε * ε := by ring
      _ ≥ x^2 - 2 * ε * 2 + 0 * 0 := by gcongr
      _ = x^2 - 4 * ε := by ring
      _ > 2 := hε3
    have why (y:Real) (hy: y ∈ E) : x - ε ≥ y := by sorry
    have claim13: x-ε ∈ upperBounds E := by rwa [upperBound_def]
    have claim14: x ≤ x-ε := by grind [isLUB_def]
    linarith
  . have claim7 : ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 + 5*ε < 2 := by
      set ε := min (1/2) ((2-x^2)/10)
      have hx : 2 - x^2 > 0 := by linarith
      have hε: 0 < ε := by positivity
      have hε1: ε ≤ 1/2 := min_le_left _ _
      have hε2: ε ≤ (2 - x^2)/10 := min_le_right _ _
      refine ⟨ ε, hε, ?_, ?_ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim7
    have claim8 : (x+ε)^2 < 2 := calc
      _ = x^2 + (2*x)*ε + ε*ε := by ring
      _ ≤ x^2 + (2*2)*ε + 1*ε := by gcongr
      _ = x^2 + 5*ε := by ring
      _ < 2 := hε3
    have claim9 : x + ε ∈ E := by simp [E, claim8]; linarith
    have claim10 : x + ε ≤ x := by grind [isLUB_def, upperBound_def]
    linarith
  assumption

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := by sorry

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by sorry

theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by
  sorry

open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

/-- Exercise 5.5.5 -/
theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by sorry

/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the `sSup` operation to build a conditionally complete lattice structure on `Real`-/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

end Chapter5
