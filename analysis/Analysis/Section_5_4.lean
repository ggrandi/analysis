import Mathlib.Tactic
import Analysis.Section_5_3

/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1: ℚ)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- remove the case that x = 0 and assume that x ≠ 0
  by_cases hzero: x = 0; exact Or.inl hzero; right
  obtain ⟨a, ha, rfl⟩ := eq_lim x

  -- use hzero to say that a cannot be ε-close to 0 for any ε
  rw [ofNat_def, LIM_eq_LIM ha (Sequence.IsCauchy.const _), Sequence.equiv_iff] at hzero
  push_neg at hzero
  simp at hzero
  obtain ⟨ε, εpos, hzero⟩ := hzero

  -- use the fact that a is cauchy to the N when it starts being (ε/2)-steady
  rw [isPos_def, isNeg_def]
  obtain ⟨N, hN⟩ := Sequence.IsCauchy.coe _ |>.mp ha (ε / 2) (by positivity)
  unfold Section_4_3.dist at hN

  -- Create a new function that is easier to work with for the 
  -- purpose of showing whether something is BoundedAwayPos/BoundedAwayNeg
  let a' (x: ℚ) (n: ℕ) := if n < N then x else a n

  -- can now reduce the problem to finding whether the equivalent function is
  -- BoundedAwayPos/BoundedAwayNeg
  --
  -- we choose the value of x such that it can simplify a case later
  suffices (∃x, BoundedAwayPos (a' x)) ∨ (∃x, BoundedAwayNeg (a' x)) by
    have haa' (x) : Sequence.Equiv a (a' x) := Sequence.equiv_iff _ _ |>.mpr 
      fun ε εpos => ⟨N, fun n hn => by simp [a', not_lt.mpr hn, le_of_lt εpos]⟩
    have ha' (x) : Sequence.IsCauchy (a' x) := Sequence.isCauchy_of_equiv (haa' x) |>.mp ha
    have haa'_lim_eq {x} := LIM_eq_LIM ha (ha' x) |>.mpr (haa' x)
    rcases this with this|this
    · exact Or.inl ⟨a' _, this.choose_spec, ha' _, haa'_lim_eq⟩
    · exact Or.inr ⟨a' _, this.choose_spec, ha' _, haa'_lim_eq⟩

  -- use hzero to obtain a point after N when a n > ε
  replace ⟨n, hn, hzero⟩ := hzero N

  -- since all the values in the sequence have the same sign, we use the known
  -- point as the first point to compare in the definition of IsCauchy
  specialize hN n hn
  by_cases han0 : a n > 0
  · refine Or.inl ⟨ε / 2, ε / 2, by positivity, fun n' => ?_⟩
    -- because ∀n < N, a' n = ε/2, we can simplify the case away
    by_cases hn': n' < N <;> simp [a', hn']
    -- the other point we use is n'
    specialize hN n' (not_lt.mp hn')
    calc ε / 2
    _ = ε - ε / 2 := by ring
    _ ≤ |a n| - |a n - a n'| := sub_le_sub (le_of_lt hzero) hN
    _ ≤ _ := le_abs_self _
    _ ≤ |a n - (a n - a n')| := abs_abs_sub_abs_le _ _
    _ = |a n'| := by ring_nf
    _ = a n' := by
      rw [abs_of_nonneg]
      -- we will assume by contradiction that a n' < 0
      by_contra! h
      rw [abs_of_pos han0] at hzero
      -- we know that a n - a n' > 0 by transitivity
      rw [abs_of_pos (sub_pos_of_lt <| h.trans han0)] at hN
      -- we can now set up a contradiction that ε < ε / 2
      refine (not_lt_of_gt ?_) (div_two_lt_of_pos εpos)
      calc ε
      _ < a n := hzero
      _ = a n - a n' + a n' := by ring
      _ < ε / 2 := add_lt_of_le_of_neg hN h
  replace han0 : a n < 0 := by
    apply not_lt.mp at han0
    rw [abs_of_nonpos han0] at hzero
    linarith
  refine Or.inr ⟨-(ε / 2), ε / 2, by positivity, fun n' => ?_⟩
  by_cases hn': n' < N <;> simp [a', hn']
  apply le_neg.mpr
  specialize hN n' (not_lt.mp hn')
  calc ε / 2
  _ = ε - ε / 2 := by ring
  _ ≤ |a n| - |a n - a n'| := sub_le_sub (le_of_lt hzero) hN
  _ ≤ _ := le_abs_self _
  _ ≤ |a n - (a n - a n')| := abs_abs_sub_abs_le _ _
  _ = |a n'| := by ring_nf
  _ = _ := by
    rw [abs_of_nonpos]
    by_contra! h
    rw [abs_of_neg han0] at hzero
    rw [abs_of_neg (by linarith)] at hN
    linarith

open Sequence.IsCauchy (const) in
theorem Real.nonzero_of_pos {x:Real} : (hx: x.IsPos) → x ≠ 0 := by
  rintro ⟨a, ha, ha', rfl⟩
  rw [ofNat_def, ne_eq, LIM_eq_LIM ha' (const _), Sequence.equiv_iff]
  push_neg
  simp
  obtain ⟨ε, εpos, ha⟩ := ha
  refine ⟨ε / 2, by positivity, fun N => ⟨N, le_refl _, ?_⟩⟩
  calc ε/2
  _ < ε := div_two_lt_of_pos εpos
  _ ≤ a N := ha N
  _ ≤ |a N| := le_abs_self _

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := not_and'.mpr nonzero_of_pos

open Sequence.IsCauchy (const) in
theorem Real.nonzero_of_neg {x:Real} : (hx: x.IsNeg) → x ≠ 0 := by
  rintro ⟨a, ha, ha', rfl⟩
  rw [ofNat_def, ne_eq, LIM_eq_LIM ha' (const _), Sequence.equiv_iff]
  push_neg
  simp
  obtain ⟨ε, εpos, ha⟩ := ha
  refine ⟨ε / 2, by positivity, fun N => ⟨N, le_refl _, ?_⟩⟩
  calc ε/2
  _ < ε := div_two_lt_of_pos εpos
  _ ≤ -a N := le_neg_of_le_neg (ha N)
  _ ≤ |a N| := neg_le_abs _

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := not_and'.mpr nonzero_of_neg

open Sequence.IsCauchy (const) in
/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  refine not_and.mpr fun hpos hneg => ?_
  have hnonzero := nonzero_of_pos hpos
  obtain ⟨a, ha, ha', rfl⟩ := hpos
  obtain ⟨b, hb, hb', h⟩ := hneg
  rw [LIM_eq_LIM ha' hb'] at h
  obtain ⟨lower, lower_pos, ha⟩ := ha
  obtain ⟨upper, upper_pos, hb⟩ := hb
  by_cases hlu : lower = upper
  · subst upper
    replace ⟨n, hn⟩ := Sequence.equiv_iff _ _ |>.mp h lower (by positivity)
    apply not_lt.mpr (hn n (le_refl _)); clear hn
    calc lower
    _ < lower + lower := lt_add_of_pos_right lower lower_pos
    _ ≤ a n - b n := by 
      rw [_root_.sub_eq_add_neg]
      refine add_le_add (ha n) ?_
      exact le_neg_of_le_neg (hb n)
    _ = |_| := by
      rw [abs_of_pos <| sub_pos_of_lt ?_]
      calc b n
      _ ≤ -lower := hb n
      _ < lower := neg_lt_self lower_pos
      _ ≤ a n := ha n
  have := (abs_sub_pos.mpr hlu)
  replace ⟨n, hn⟩ := Sequence.equiv_iff _ _ |>.mp h (|lower - upper|/2) (by positivity)
  contrapose! hn; clear hn
  refine ⟨n, le_refl _, ?_⟩
  calc |lower - upper| / 2
  _ < |lower - upper| := div_two_lt_of_pos this
  _ ≤ |lower| + |upper| := abs_sub _ _
  _ = lower + upper := by rw [abs_of_pos lower_pos, abs_of_pos upper_pos]
  _ ≤ a n - b n := by
    rw [_root_.sub_eq_add_neg]
    exact add_le_add (ha n) (le_neg_of_le_neg (hb n))
  _ ≤ |a n - b n| := le_abs_self _

open Sequence.IsCauchy (neg) in
/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  suffices ∀{a}, BoundedAwayNeg a ↔ BoundedAwayPos (-a) by
    constructor
    · rintro ⟨a, ha, ha', h⟩
      refine ⟨-a, this.mp ha, neg _ ha', h ▸ neg_LIM _ ha'⟩
    · rintro ⟨a, ha, ha', h⟩
      refine ⟨-a, ?_, neg _ ha', ?_⟩
      · rw [← neg_neg a] at ha
        exact this.mpr ha
      · rw [← neg_LIM _ ha', ← h, neg_neg]
  intro a
  peel 3
  exact le_neg

open Sequence.IsCauchy (add) in
/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  obtain ⟨a, ⟨N, hN, ha⟩, ha', rfl⟩ := hx
  obtain ⟨b, ⟨M, hM, hb⟩, hb', rfl⟩ := hy
  refine ⟨a + b, ?_, add ha' hb', LIM_add ha' hb'⟩
  exact ⟨N + M, by positivity, fun n => add_le_add (ha n) (hb n)⟩

open Sequence.IsCauchy (mul) in
/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  obtain ⟨a, ⟨N, hN, ha⟩, ha', rfl⟩ := hx
  obtain ⟨b, ⟨M, hM, hb⟩, hb', rfl⟩ := hy
  refine ⟨a * b, ?_, mul ha' hb', LIM_mul ha' hb'⟩
  refine ⟨N * M, by positivity, fun n => ?_⟩
  exact mul_le_mul (ha _) (hb _) hM.le (le_trans hN.le (ha _))

open Sequence.IsCauchy (const) in
theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  refine ⟨?_, fun hq => 
    ⟨Function.const _ q, ⟨q, hq, fun _ => le_refl _⟩, const _, ratCast_def _ ▸ rfl⟩⟩
  rintro ⟨a, ha, ha', hq⟩
  rw [ratCast_def, LIM_eq_LIM (const _) ha', Sequence.equiv_iff] at hq
  obtain ⟨ε, εpos, ha⟩ := ha
  obtain ⟨n, hq⟩ := hq (ε/2) (by positivity)
  replace hq := hq n (le_refl _)
  replace ha := ha n
  contrapose! hq
  calc ε/2
  _ < ε := div_two_lt_of_pos εpos
  _ = ε - 0 := sub_zero _ |>.symm
  _ ≤ a n - q := sub_le_sub ha hq
  _ ≤ |a n - q| := le_abs_self _
  _ = |q - a n| := abs_sub_comm _ _

abbrev Real.ratCast_pos := pos_of_coe

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  rw [neg_iff_pos_of_neg, neg_ratCast, pos_of_coe]
  exact neg_pos

abbrev Real.ratCast_neg := neg_of_coe

open Classical in
/-- Need to use classical logic here because isPos and isNeg are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa only [not_exists, not_and,
    forall_exists_index, gt_iff_lt, ge_iff_le, and_imp, hx, and_true] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa only [not_exists, not_and,
    forall_exists_index, gt_iff_lt, ge_iff_le, and_imp, true_and] using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa only [neg_iff_pos_of_neg,
    neg_zero, not_exists, not_and, forall_exists_index, gt_iff_lt, ge_iff_le, and_imp,
    true_and] using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  rw [gt_iff_lt, lt_iff, neg_iff_pos_of_neg, neg_sub]

theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  rw [ge_iff_le, le_iff, gt_iff_lt, eq_comm]

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  rw [lt_iff, ratCast_sub, ratCast_neg]
  exact sub_neg.symm

theorem Real.ratCast_lt {p q: ℚ}: (p: Real) < (q: Real) ↔ p < q := lt_of_coe p q |>.symm

theorem Real.ratCast_le {p q: ℚ}: (p: Real) ≤ (q: Real) ↔ p ≤ q := by
  rw [le_iff, le_iff_lt_or_eq]
  exact or_congr ratCast_lt (ratCast_inj _ _)

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff' {x:Real} : x.IsPos ↔ 0 < x := by
  rw [lt_iff, zero_sub, neg_iff_pos_of_neg, neg_neg]

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by
  rw [isPos_iff']

theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by
  rw [lt_iff, sub_zero]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  rcases trichotomous (x - y) with h|h|h
  · exact Or.inr <| Or.inr <| sub_eq_zero.mp h
  · exact Or.inl (gt_iff _ _ |>.mpr h)
  · exact Or.inr <| Or.inl (lt_iff _ _ |>.mpr h)

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw [gt_iff, lt_iff]
  exact not_pos_neg _

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  rw [gt_iff, ← sub_eq_zero, and_comm]
  exact not_zero_pos _

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  rw [lt_iff, ← sub_eq_zero, and_comm]
  exact not_zero_neg _

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ y > x := by
  rw [gt_iff, lt_iff, ← neg_sub x y, neg_iff_pos_of_neg]

theorem Real.lt_iff' {x y: Real} : x < y ↔ ∃r, 0 < r ∧ x + r = y := by
  rw [lt_iff, isNeg_def]
  constructor
  · intro ⟨a, ha, ha', h⟩
    refine ⟨LIM (-a), isPos_iff _ |>.mp ?_, ?_⟩
    · rw [← neg_LIM _ ha', ← neg_iff_pos_of_neg]
      exact ⟨a, ha, ha', rfl⟩
    rw [← neg_LIM _ ha', ← h]
    ring
  rintro ⟨r, hr, rfl⟩
  obtain ⟨a, ⟨c, hc, ha⟩, ha', rfl⟩ := isPos_iff'.mpr hr
  refine ⟨-a, ⟨c, hc, ?_⟩, Sequence.IsCauchy.neg _ ha', ?_⟩
  · peel 1 ha with n ha
    rw [Pi.neg_apply]
    exact neg_le_neg_iff.mpr ha
  rw [← neg_LIM _ ha']
  ring

theorem Real.le_iff' {x y: Real} : x ≤ y ↔ ∃r, 0 ≤ r ∧ x + r = y := by
  simp_rw [le_iff, or_and_right, exists_or, existsAndEq, add_zero, true_and]
  exact or_congr_left lt_iff'

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  obtain ⟨a, ha, hy⟩ := lt_iff'.mp hxy
  obtain ⟨b, hb, hz⟩ := lt_iff'.mp hyz
  refine lt_iff'.mpr ⟨a + b, isPos_iff'.mp ?_, ?_⟩
  exact pos_add (isPos_iff'.mpr ha) (isPos_iff'.mpr hb)
  rw [← hz, ← hy, add_assoc]

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  obtain ⟨a, ha, hx⟩ := lt_iff'.mp hxy
  exact lt_iff'.mpr ⟨a, ha, hx ▸ add_right_comm _ _ _⟩

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  obtain ⟨a, ha, hx⟩ := lt_iff'.mp hxy
  refine lt_iff'.mpr ⟨a * z, isPos_iff'.mp ?_, ?_⟩
  · exact pos_mul (isPos_iff'.mpr ha) hz
  rw [← hx]
  ring

theorem Real.mul_lt_mul_left {x y z:Real} (hxy: x < y) (hz: z.IsPos) :  z * x < z * y := by
  conv => congr <;> rw [mul_comm]
  exact mul_lt_mul_right hxy hz

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  /- obtain ⟨a, ha, rfl⟩ := le_iff'.mp hxy -/
  rcases le_iff _ _ |>.mp hxy with ha|ha
  · refine le_iff _ _ |>.mpr (Or.inl ?_)
    exact mul_lt_mul_left ha hz
  refine le_iff _ _ |>.mpr (Or.inr ?_)
  rw [ha]

theorem Real.mul_le_mul_right {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : x * z ≤ y * z := by
  conv => congr <;> rw [mul_comm]
  exact mul_le_mul_left hxy hz

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  obtain ⟨a, ⟨M, Mpos, ha⟩, ha', rfl⟩ := hx
  obtain ⟨b, ⟨N, Npos, hb⟩, hb', rfl⟩ := hy
  refine ⟨a * b, ⟨M * N, by positivity, fun n => ?_⟩, Sequence.IsCauchy.mul ha' hb', LIM_mul ha' hb'⟩
  rw [Pi.mul_apply, le_neg, neg_mul_eq_mul_neg]
  specialize ha n
  replace hb := le_neg.mp <| hb n
  exact mul_le_mul ha hb Npos.le (Mpos.le.trans ha)

open Classical in
/--
  (Not from textbook) Real has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl a := le_iff _ _ |>.mpr (Or.inr rfl)
  le_trans := fun x y z hxy hyz => by
    obtain ⟨a, ha, hy⟩ := le_iff'.mp hxy
    obtain ⟨b, hb, hz⟩ := le_iff'.mp hyz
    apply le_iff'.mpr ⟨a + b, ?_, ?_⟩
    rcases le_iff _ _ |>.mp ha with ha|rfl
    <;> rcases le_iff _ _ |>.mp hb with hb|rfl
    · refine le_iff _ _ |>.mpr (Or.inl <| isPos_iff'.mp ?_)
      exact pos_add (isPos_iff'.mpr ha) (isPos_iff'.mpr hb)
    · rwa [add_zero]
    · rwa [zero_add]
    · rw [zero_add]
      exact le_iff _ _ |>.mpr (Or.inr rfl)
    rw [← hz, ← hy, add_assoc]
  lt_iff_le_not_ge := fun x y => by
    rw [le_iff, le_iff, not_or, or_and_right]
    conv => rhs; rhs; rw [and_comm, and_assoc]; rhs; rw [eq_comm, and_comm, and_not_self_iff]
    rw [and_false, or_false]
    refine ⟨fun h => ⟨h, ?_, ?_⟩, fun h => h.left⟩ 
    · exact not_and.mp (not_gt_and_lt _ _) h
    · exact not_and.mp (not_gt_and_eq _ _) h
  le_antisymm := fun x y hxy hyx => by
    rcases le_iff _ _ |>.mp hxy with hxy|hxy
    <;> rcases le_iff _ _ |>.mp hyx with hyx|hyx
    <;> try assumption
    · have := lt_trans hxy hyx
      rw [lt_iff, sub_self] at this
      refine (?_: ¬ _) this |>.elim
      push_neg
      intro a ⟨c, cpos, ha⟩ ha'
      rw [ofNat_def, ne_eq, LIM_eq_LIM (Sequence.IsCauchy.const _) ha', Sequence.equiv_iff]
      push_neg
      refine ⟨c / 2, by positivity, fun n => ⟨n, le_refl _, ?_⟩⟩
      calc 
      _ < c := div_two_lt_of_pos cpos
      _ ≤ -a n := le_neg_of_le_neg (ha n)
      _ ≤ |a n| := neg_le_abs _
      _ = |_| := by rw [CharP.cast_eq_zero, zero_sub, abs_neg]
    · rw [hyx]
  le_total := fun x y => by
    rcases trichotomous' x y with h|h|rfl
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr rfl)
  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) Linear Orders come with a definition of absolute value |.|
  Show that it agrees with our earlier definition.
-/
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  unfold _root_.abs
  rcases trichotomous x with rfl|h|h
  · rw [abs_of_zero, neg_zero, max_self]
  · rw [max_def, if_neg, abs_of_pos _ h]
    rw [not_le, lt_iff, ← neg_add_eq_sub, ← neg_add, ← two_mul, ← neg_mul, mul_comm]
    refine mul_pos_neg h ?_
    refine ⟨Function.const _ (-2), ?_, Sequence.IsCauchy.const _, ?_⟩
    · refine ⟨1, by positivity, fun n => ?_⟩
      norm_num
    · rw [ofNat_def, neg_LIM _ (Sequence.IsCauchy.const _)]
      congr
  · rw [max_def, if_pos, abs_of_neg _ h]
    rw [le_iff]
    left
    rw [lt_iff, sub_neg_eq_add, ← two_mul]
    refine mul_pos_neg ?_ h
    refine ⟨Function.const _ (2), ?_, Sequence.IsCauchy.const _, ?_⟩
    · refine ⟨1, by positivity, fun n => ?_⟩
      norm_num
    · rw [ofNat_def]; rfl

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw [div_eq]
  apply pos_mul hx
  exact inv_of_pos hy

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

theorem Real.inv_of_ge {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x ≥ y) : x⁻¹ ≤ y⁻¹ := by
  rcases le_iff _ _ |>.mp hxy with hxy|hxy
  · exact Or.inl (inv_of_gt hx hy hxy)
  · subst y
    exact le_refl _

/-- (Not from textbook) Real has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := fun x y hxy z => by 
    obtain ⟨r, hr, hy⟩ := le_iff'.mp hxy
    exact le_iff'.mpr ⟨r, hr, hy ▸ by ring⟩
  add_le_add_right := fun x y hxy z => by 
    obtain ⟨r, hr, hy⟩ := le_iff'.mp hxy
    exact le_iff'.mpr ⟨r, hr, hy ▸ by ring⟩
  mul_lt_mul_of_pos_left := by
    intro x hx y z hyz
    obtain ⟨r, hr, hz⟩ := lt_iff'.mp hyz
    refine lt_iff'.mpr ⟨x * r, ?_, by rw [← hz, mul_add]⟩
    rw [← gt_iff_lt, ← isPos_iff]
    refine pos_mul ?_ ?_
    · exact isPos_iff _ |>.mpr hx
    · exact isPos_iff _ |>.mpr hr
  mul_lt_mul_of_pos_right := by
    intro x hx y z hyz
    obtain ⟨r, hr, hz⟩ := lt_iff'.mp hyz
    refine lt_iff'.mpr ⟨r * x, ?_, by rw [← hz, add_mul]⟩
    rw [← gt_iff_lt, ← isPos_iff]
    refine pos_mul ?_ ?_
    · exact isPos_iff _ |>.mpr hr
    · exact isPos_iff _ |>.mpr hx
  le_of_add_le_add_left := fun x y z h => by
    obtain ⟨r, hr, hz⟩ := le_iff'.mp h
    rw [add_assoc, add_right_inj] at hz
    exact le_iff'.mpr ⟨r, hr, hz⟩
  zero_le_one := by
    refine le_iff _ _ |>.mp (Or.inl <| isPos_iff _ |>.mp ?_)
    refine ⟨Function.const _ 1, ?_, Sequence.IsCauchy.const _, ?_⟩
    · refine ⟨1, rfl, fun n => ?_⟩
      exact le_refl _
    · rw [ofNat_def]; rfl

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

open Sequence.IsCauchy (add sub const harmonic') in
/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  let f1 := (Function.const _ 1) + (fun n: ℕ => 1/((n:ℚ) + 1))
  have hf1: Sequence.IsCauchy f1 := add (const _) harmonic'
  let f2 := (Function.const _ 1) - (fun n: ℕ => 1/((n:ℚ) + 1))
  have hf2: Sequence.IsCauchy f2 := sub (const _) harmonic'
  use f1, f2
  refine ⟨hf1, hf2, ?_, ?_⟩
  · intro n
    unfold f1 f2
    rw [← neg_add_eq_sub, add_comm]
    apply add_lt_add_left
    apply neg_lt_self
    exact Nat.one_div_pos_of_nat
  refine (Eq.not_lt (eq_comm.mp ?_))
  rw [LIM_eq_LIM hf1 hf2, Sequence.equiv_iff]
  intro ε εpos
  unfold f1 f2
  simp
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have : (n + 1: ℚ) > 0 := Nat.cast_add_one_pos n
  simp [← two_mul, _root_.abs_of_pos this]
  calc (_: ℚ)
  _ ≤ 2 * (N + 1: ℚ)⁻¹ := by
    refine Rat.mul_le_mul_of_nonneg_left ?_ rfl
    apply inv_le_inv₀ ?_ ?_ |>.mpr ?_
    · exact this
    · exact Nat.cast_add_one_pos N
    refine add_le_add_left ?_ 1
    exact Rat.natCast_le_natCast.mpr hn
  _ ≤ 2 * (ε / 2) := by
    refine Rat.mul_le_mul_of_nonneg_left ?_ rfl
    refine inv_le_of_inv_le₀ (by positivity) ?_
    rw [inv_div]
    refine le_of_lt <| hN.trans ?_
    exact lt_add_one _
  _ = ε := by field_simp

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  apply existsUnique_of_exists_of_unique
  · wlog h : x.IsPos
    · by_cases hx: x = 0
      · use 0
        simp [hx]
      replace h := trichotomous x |>.resolve_left hx |>.resolve_left h
      rw [neg_iff_pos_of_neg] at h
      obtain ⟨n, hl, hu⟩ := this _ h
      by_cases heq: -x = n
      · refine ⟨-n, ?_, ?_⟩
        · rw [Int.cast_neg, neg_le, heq]
        rw [Int.cast_neg, ← heq, neg_neg]
        exact lt_add_one x
      refine ⟨-(n + 1), ?_, ?_⟩
      · rw [neg_lt, ← Int.cast_one, ← Int.cast_add] at hu
        rw [Int.cast_neg]
        exact hu.le
      simp_rw [neg_add, Int.cast_add, Int.cast_neg, Int.cast_one, neg_add_cancel_right, lt_neg]
      exact lt_of_le_of_ne hl (Ne.symm heq)
    obtain ⟨M, Mpos, hM⟩ := le_mul (ε := 1) (isPos_iff'.mpr (by norm_num)) x
    rw [mul_one, gt_iff_lt] at hM
    induction M
    case zero => contradiction
    case succ M ih =>
      by_cases hx: M ≤ x
      exact ⟨M, hx, by simpa using hM⟩
      have : 0 < M := Nat.cast_pos.mp <| 
        lt_trans (isPos_iff'.mp h) (not_le.mp hx)
      exact ih this (not_le.mp hx) 
  intro n m hn hm
  have h1 := lt_of_le_of_lt hn.left hm.right
  have h2 := lt_of_le_of_lt hm.left hn.right
  simp_rw [show ∀n, (ofNat(n): Real) = (ofNat(n): ℤ) from fun _ => rfl, 
    intCast_def', ratCast_add, ratCast_lt, 
    ← Rat.intCast_add, Rat.intCast_lt_intCast, Int.lt_add_one_iff
  ] at h1 h2
  exact le_antisymm h1 h2

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by
  obtain ⟨M, Mpos, hM⟩ := le_mul hx 1
  refine ⟨M, Int.natCast_pos.mpr Mpos, ?_⟩
  rw [Int.cast_natCast]
  exact inv_lt_iff_one_lt_mul₀' (by rwa [Nat.cast_pos]) |>.mpr hM

/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  obtain ⟨r, hr, rfl⟩ := lt_iff'.mp hxy; clear hxy
  obtain ⟨N, Npos, hN⟩ := exist_inv_nat_le (isPos_iff'.mpr hr)
  replace Npos: 0 < (N: Real) := Int.cast_pos.mpr Npos
  obtain ⟨M, hM, hM'⟩ := floor_exist (N * x) |>.exists
  refine ⟨(M + 1) / N, ?_, ?_⟩
  <;> simp
  · exact lt_div_iff₀' Npos |>.mpr hM'
  · rw [add_div]
    refine add_lt_add_of_le_of_lt ?_ ?_
    · exact div_le_iff₀' Npos |>.mpr hM
    rwa [← inv_eq_one_div]

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  unfold _root_.abs
  rw [max_lt_iff, and_comm]
  conv =>
    lhs
    congr
    · rw [neg_sub, sub_lt_comm]
    · rw [sub_lt_iff_lt_add']

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
  unfold _root_.abs
  rw [max_le_iff, and_comm]
  conv =>
    lhs
    congr
    · rw [neg_sub, sub_le_comm]
    · rw [sub_le_iff_le_add']

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h _ εpos => le_add_of_le_of_nonneg h εpos.le⟩
  by_contra!
  obtain ⟨r, hr, rfl⟩ := lt_iff'.mp this; clear this
  refine (not_lt.mpr ?_) (div_two_lt_of_pos hr)
  apply le_of_add_le_add_left
  exact h _ (by positivity)


/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
  refine ⟨fun h => ?_, fun h ε εpos => by rw [h, sub_self, abs_zero]; exact εpos.le⟩
  by_contra! heq
  have := abs_sub_pos.mpr heq
  refine (not_lt.mpr (h _ ?_)) (div_two_lt_of_pos this)
  exact half_pos this

open Sequence.IsCauchy (const) in
/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
  LIM a ≤ x := by
    by_contra!
    obtain ⟨q, hl, hu⟩ := rat_between this; clear this
    replace h := fun n => h n |>.trans hl.le |> Rat.cast_le.mp
    replace h := ratCast_def q ▸ LIM_mono ha (const _) h
    exact h.not_gt hu

open Sequence.IsCauchy (const) in
/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
  LIM a ≥ x := by
    by_contra!
    obtain ⟨q, hl, hu⟩ := rat_between this; clear this
    replace h := fun n => hu.le.trans (h n) |> Rat.cast_le.mp
    replace h := ratCast_def q ▸ LIM_mono (const _) ha h
    exact hl.not_ge h

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

theorem Real.max_eq' (x y:Real) : max x y = if x ≤ y then y else x := by
  rw [max_eq]
  split_ifs with h h' h'
  · exact h'.antisymm h
  · exact rfl
  · exact rfl
  · replace h := not_le.mp h |>.trans (not_le.mp h')
    exact lt_irrefl _ h |>.elim

theorem Real.min_eq' (x y:Real) : min x y = if x ≥ y then y else x := by
  rw [min_eq]
  split_ifs with h h' h'
  · exact h.antisymm h'
  · exact rfl
  · exact rfl
  · replace h := not_le.mp h |>.trans (not_le.mp h')
    exact lt_irrefl _ h |>.elim

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by
  rw [max_eq, min_eq]
  split_ifs with h h' h' <;> try rw [neg_neg]
  · exact (le_of_not_ge h') |> le_of_neg_le_neg |>.antisymm h
  exact (le_of_neg_le_neg h').antisymm (le_of_not_ge h)

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by
  simp_rw [neg_max, neg_neg]

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by
  rw [max_eq, max_eq']

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by
  rw [max_eq, ite_self]

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by
  rw [max_def, max_def]
  by_cases hxy: x ≤ y <;> simp [hxy]


/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  by_cases hxy: x ≤ y
  · have : x * z ≤ y * z := by exact mul_le_mul_right hxy hz
    rw [max_def, max_def, if_pos this, if_pos hxy]
  · have : y * z ≤ x * z := by exact mul_le_mul_right (le_of_not_ge hxy) hz
    rw [max_def', max_def, if_pos this, if_neg hxy]


/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by
  rw [neg_min, neg_min, max_comm]

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by
  rw [neg_min, max_self, neg_neg]

/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by
  rw [neg_min, neg_min, neg_add, neg_add, max_add, neg_add, neg_neg]

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  rw [neg_min, neg_min, ← neg_mul, ← neg_mul, max_mul _ _ hz, ← neg_mul]

/- Additional exercise: What happens if z is negative? -/
theorem Real.max_mul' (x y :Real) {z:Real} (hz: z.IsNeg) : max (x * z) (y * z) = min x y * z := by
  rw [neg_max, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg, min_mul, neg_mul_eq_mul_neg, neg_neg]
  rwa [← neg_iff_pos_of_neg]

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by
  rw [max_def, min_def']
  by_cases h : x ≤ y
  · rw [if_pos h, if_pos]
    exact inv_of_ge hy hx h
  · rw [if_neg h, if_neg (not_le.mpr ?_)]
    exact inv_of_gt hx hy (not_le.mp h)

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
  rw [min_def, max_def']
  by_cases h : x ≤ y
  · rw [if_pos h, if_pos]
    exact inv_of_ge hy hx h
  · rw [if_neg h, if_neg (not_le.mpr ?_)]
    exact inv_of_gt hx hy (not_le.mp h)

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by
    intro x y hxy
    exact ratCast_le.mpr hxy

end Chapter5
