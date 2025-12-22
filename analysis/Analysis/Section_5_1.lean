import Mathlib.Tactic
import Analysis.Section_4_3

/-!
# Analysis I, Section 5.1: Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.1.1 (Sequence). To avoid some technicalities involving dependent types, we extend
  sequences by zero to the left of the starting point `n₀`.
-/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℚ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/--
Functions from ℕ to ℚ can be thought of as sequences starting from 0; `ofNatFun` performs this conversion.

The `coe` attribute allows the delaborator to print `Sequence.ofNatFun f` as `↑f`, which is more concise; you may safely remove this if you prefer the more explicit notation.
-/
@[coe]
def Sequence.ofNatFun (a : ℕ → ℚ) : Sequence where
    n₀ := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind

-- Notice how the delaborator prints this as `↑fun x ↦ ↑x ^ 2 : Sequence`.
#check Sequence.ofNatFun (· ^ 2)

/--
If `a : ℕ → ℚ` is used in a context where a `Sequence` is expected, automatically coerce `a` to `Sequence.ofNatFun a` (which will be pretty-printed as `↑a`)
-/
instance : Coe (ℕ → ℚ) Sequence where
  coe := Sequence.ofNatFun

abbrev Sequence.mk' (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq n := if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by grind

lemma Sequence.eval_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) :
    (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by grind

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence) n = a n := by norm_cast

@[simp]
lemma Sequence.eval_coe_at_int (n:ℤ) (a: ℕ → ℚ) : (a:Sequence) n = if n ≥ 0 then a n.toNat else 0 := by norm_cast

@[simp]
lemma Sequence.n0_coe (a: ℕ → ℚ) : (a:Sequence).n₀ = 0 := by norm_cast

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_:ℕ) ↦ (3:ℚ))

/-- Example 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (·^2)

/-- Example 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- need to temporarily leave the `Chapter5` namespace to introduce the following notation

end Chapter5

/--
A slight generalization of Definition 5.1.3 - definition of ε-steadiness for a sequence with an
arbitrary starting point n₀
-/
abbrev Rat.Steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m)

lemma Rat.steady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) := by rfl

lemma Rat.steady_iff {ε: ℚ} {a: ℕ → ℚ} :
  ε.Steady (a: Chapter5.Sequence) ↔ ∀ n m, |a n - a m| ≤ ε := by
    rw [steady_def]
    constructor
    · intro h j k
      simpa using h j (by simp) k (by simp)
    intro h j hj k hk
    lift j to ℕ
    · simpa using hj
    lift k to ℕ
    · simpa using hk
    clear hj hk
    simpa using h j k

namespace Chapter5

/--
Definition 5.1.3 - definition of ε-steadiness for a sequence starting at 0
-/
lemma Rat.Steady.coe (ε : ℚ) (a:ℕ → ℚ) :
    ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) := by
  constructor
  · intro h n m; specialize h n ?_ m ?_ <;> simp_all
  intro h n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [h n m]

/--
Not in textbook: the sequence 3, 3 ... is 1-steady
Intended as a demonstration of `Rat.Steady.coe`
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  simp [Rat.Steady.coe, Rat.Close]

/--
Compare: if you need to work with `Rat.Steady` on the coercion directly, there will be side
conditions `hn : n ≥ 0` and `hm : m ≥ 0` that you will need to deal with.
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  intro n _ m _; simp_all [Sequence.n0_coe, Sequence.eval_coe_at_int, Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is 1-steady.
-/
example : (1:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  -- Split into four cases based on whether n and m are even or odd
  -- In each case, we know the exact value of a n and a m
  split_ifs <;> simp [Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is not ½-steady.
-/
example : ¬ (0.5:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is 0.1-steady.
-/
example : (0.1:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m; unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith); rwa [abs_sub_comm]
  rw [abs_sub_comm, abs_of_nonneg]
  . rw [show (0.1:ℚ) = (10:ℚ)^(-1:ℤ) - 0 by norm_num]
    gcongr <;> try grind
    positivity
  linarith [show (10:ℚ) ^ (-(n:ℤ)-1) ≤ (10:ℚ) ^ (-(m:ℤ)-1) by gcongr; norm_num]

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is not 0.01-steady. Left as an exercise.
-/
example : ¬(0.01:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.steady_iff]
  push_neg
  use 0, 1
  norm_num

example {a b c: ℝ} (h: a / b < c) (hb: b > 0) : a < c * b := by exact (mul_inv_lt_iff₀ hb).mp h

/-- Example 5.1.5: The sequence 1, 2, 4, 8, ... is not ε-steady for any ε. Left as an exercise.
-/
example (ε:ℚ) : ¬ ε.Steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by
  rw [Rat.steady_iff]
  push_neg
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log ε / Real.log 2)
  replace hN: ε < 2 ^ N := by 
    rify
    refine Real.lt_pow_of_log_lt (by norm_num) ?_
    refine mul_inv_lt_iff₀ ?_ |>.mp hN
    refine Real.log_pos (by norm_num)
  use 0, N + 1
  calc ε
  _ < 2 ^ N := hN
  _ < 2 ^ (N + 2) - 2 := by
    /- rw [Rat.pow_succ, Rat.pow_succ, mul_two, mul_two] -/
    refine (Rat.lt_iff_sub_pos _ _).mpr ?_
    ring_nf
    refine lt_neg_add_iff_lt.mpr ?_
    refine (Rat.div_lt_iff rfl).mp ?_
    refine lt_of_lt_of_le (show 2 / 3 < 2 ^ 0 by norm_num) ?_
    refine (pow_le_pow_iff_right₀ rfl).mpr ?_
    exact Nat.zero_le N
  _ ≤ _ := le_abs_self _
  _ = _ := by rw [abs_sub_comm, zero_add, pow_one]

/-- Example 5.1.5:The sequence 2, 2, 2, ... is ε-steady for any ε > 0.
-/
example (ε:ℚ) (hε: ε>0) : ε.Steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]; simp [Rat.Close]; positivity

/--
The sequence 10, 0, 0, ... is 10-steady.
-/
example : (10:ℚ).Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]; intro n m
  -- Split into 4 cases based on whether n and m are 0 or not
  split_ifs <;> simp [Rat.Close]

/--
The sequence 10, 0, 0, ... is not ε-steady for any smaller value of ε.
-/
example (ε:ℚ) (hε:ε<10):  ¬ ε.Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  contrapose! hε; rw [Rat.Steady.coe] at hε; specialize hε 0 1; simpa [Rat.Close] using hε

/--
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁) n = a n := by simp [hn]; intro h; exact (a.vanish _ h).symm

end Chapter5

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.EventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop := ∃ N ≥ a.n₀, ε.Steady (a.from N)

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) := by rfl

theorem Rat.eventuallySteady_iff {ε: ℚ} {a: ℕ → ℚ} :
  ε.EventuallySteady (a: Chapter5.Sequence) ↔ ∃ (N: ℕ), ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
    rw [eventuallySteady_def]
    constructor
    · intro ⟨N, N_pos, h⟩
      lift N to ℕ; simpa using N_pos
      refine ⟨N, fun j hj k hk => ?_⟩
      simpa [hj, hk] using h j (by simpa using hj) k (by simpa using hk)
    · intro ⟨N, h⟩
      refine ⟨N, by simp, fun j hj k hk => ?_⟩
      lift j to ℕ using (le_trans (Int.natCast_nonneg N) (by simpa using hj))
      lift k to ℕ using (le_trans (Int.natCast_nonneg N) (by simpa using hk))
      simp at hj hk
      simpa [hj, hk] using h j hj k hk

namespace Chapter5

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is not 0.1-steady
-/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 2; simp [Rat.Close] at h; norm_num at h

/--
Example 5.1.7: The sequence a_10, a_11, a_12, ... is 0.1-steady
-/
lemma Sequence.ex_5_1_7_b : (0.1:ℚ).Steady (((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence).from 10) := by
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [Rat.Close]
  wlog h : m ≤ n
  · specialize this m n _ _ _ <;> try omega
    rwa [abs_sub_comm] at this
  rw [abs_sub_comm]
  have : ((n:ℚ) + 1)⁻¹ ≤ ((m:ℚ) + 1)⁻¹ := by gcongr
  rw [abs_of_nonneg (by linarith), show (0.1:ℚ) = (10:ℚ)⁻¹ - 0 by norm_num]
  gcongr
  · norm_cast; omega
  positivity

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is eventually 0.1-steady
-/
lemma Sequence.ex_5_1_7_c : (0.1:ℚ).EventuallySteady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) :=
  ⟨10, by simp, ex_5_1_7_b⟩

/--
Example 5.1.7

The sequence 10, 0, 0, ... is eventually ε-steady for every ε > 0. Left as an exercise.
-/
lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) :
  ε.EventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by
    refine ⟨1, by simp, ?_⟩
    intro i hi j hj
    simp at hi hj
    have hi' : i ≠ 0 := (Int.ne_of_lt hi).symm
    replace hi' : i.toNat ≠ 0 := by
      refine Int.ofNat_ne_zero.mp ?_
      rwa [Int.toNat_of_nonneg (le_of_lt hi)]
    have hj' : j ≠ 0 := (Int.ne_of_lt hj).symm
    replace hj' : j.toNat ≠ 0 := by
      refine Int.ofNat_ne_zero.mp ?_
      rwa [Int.toNat_of_nonneg (le_of_lt hj)]
    rw [
      from_eval _ hi, from_eval _ hj, 
      eval_coe_at_int, eval_coe_at_int,
      if_pos (zero_le_one.trans hi),
      if_neg hi',
      if_pos (zero_le_one.trans hj),
      if_neg hj',
    ]
    exact Section_4_3.close_mono (Section_4_3.close_refl _) (le_of_lt hε)

abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℚ), ε.EventuallySteady a

lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a := by rfl

/-- Definition of Cauchy sequences, for a sequence starting at 0 -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℚ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor <;> intro h ε hε
  · choose N hN h' using h ε hε
    lift N to ℕ using hN; use N
    intro j _ k _; simp [Rat.steady_def] at h'; specialize h' j _ k _ <;> try omega
    simp_all; exact h'
  choose N h' using h ε hε
  refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := ?_
  have mpos : 0 ≤ m := ?_
  lift n to ℕ using npos
  lift m to ℕ using mpos
  simp [hn, hm]; specialize h' n _ m _
  all_goals try omega
  norm_cast

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  constructor <;> intro h ε hε <;> choose N hN h' using h ε hε
  · refine ⟨ N, hN, ?_ ⟩; dsimp at hN; intro j _ k _
    simp only [Rat.Steady, show max n₀ N = N by omega] at h'
    specialize h' j _ k _ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
    exact h'
  refine ⟨ max n₀ N, by simp, ?_ ⟩
  intro n _ m _; simp_all
  apply h' n _ m <;> omega

noncomputable def Sequence.sqrt_two : Sequence := (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))

theorem sqrt_approx {n: ℕ}: |⌊√2 * 10 ^ n⌋ / 10 ^ n - √2| < 1 / 10 ^ n := calc
  _ = |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2 * 10 ^ n / 10 ^ n| := by 
    rw [mul_div_cancel_right₀ _ (pow_ne_zero n (by norm_num))]
  _ = |(↑⌊√2 * 10 ^ n⌋ - √2 * 10 ^ n) / 10 ^ n| := by field_simp
  _ = |(↑⌊√2 * 10 ^ n⌋ - √2 * 10 ^ n)| / 10 ^ n := by 
    rw [abs_div, abs_of_nonneg (a := 10 ^ n) (pow_nonneg (by norm_num) n)]
  _ = |(√2 * 10 ^ n - ↑⌊√2 * 10 ^ n⌋)| / 10 ^ n := by rw [← abs_neg, neg_sub]
  _ < 1 / 10 ^ n := by
    refine div_lt_div_of_pos_right ?_ (pow_pos (by norm_num) n)
    rw [abs_of_nonneg <| sub_nonneg.mpr (Int.floor_le _)]
    simp [Int.fract_lt_one]

theorem floor_sqrt_2 : Int.floor √2 = 1 := by
  apply le_antisymm
  · refine Int.floor_le_iff.mpr ?_
    refine (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  · refine Int.le_floor.mpr ?_
    refine (Real.le_sqrt' (by norm_num)).mpr (by norm_num)

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/
theorem Sequence.ex_5_1_10_a : (1:ℚ).Steady sqrt_two := by
  intro n hn m hm
  rw [Section_4_3.close_iff, sqrt_two]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn; clear hn
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm; clear hm
  rify
  simp
  by_cases hmn' : m = n
  · simp [hmn']
  wlog hmn: m ≤ n
  · specialize this m n (Ne.symm hmn') (le_of_not_ge hmn)
    rwa [abs_sub_comm] at this
  apply le_of_lt <| calc
    _ = |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2 - (↑⌊√2 * 10 ^ m⌋ / 10 ^ m - √2)| := by ring_nf
    _ ≤ |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2| + |↑⌊√2 * 10 ^ m⌋ / 10 ^ m - √2| := abs_sub _ _
    _ < 1 / 10 ^ 1 + 0.415 := by 
      refine add_lt_add ?_ ?_
      · refine lt_of_lt_of_le sqrt_approx ?_
        exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)
      by_cases hm: m = 0
      · simp only [hm, pow_zero, mul_one, div_one, abs_sub_comm]
        rw [abs_of_nonneg <| sub_nonneg.mpr (Int.floor_le _), sub_lt_iff_lt_add', floor_sqrt_2]
        exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
      refine lt_trans ?_ (show 1 / 10 ^ 1 < _ by norm_num)
      refine lt_of_lt_of_le sqrt_approx ?_
      exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)
    _ ≤ 1 := by norm_num

theorem floor_sqrt_2_times_ten : Int.floor (√2 * 10) = 14 := by
  apply le_antisymm
  · refine Int.floor_le_iff.mpr ?_
    refine lt_div_iff₀ (show (0: ℝ) < 10 by norm_num) |>.mp ?_
    exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  · refine Int.le_floor.mpr ?_
    refine div_le_iff₀ (show (0: ℝ) < 10 by norm_num) |>.mp ?_
    exact (Real.le_sqrt' (by norm_num)).mpr (by norm_num)

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/
theorem Sequence.ex_5_1_10_b : (0.1:ℚ).Steady (sqrt_two.from 1) := by
  intro n hn m hm
  rw [Section_4_3.close_iff, sqrt_two]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (by norm_num) hn)
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (by norm_num) hm)
  simp [sqrt_two] at hm hn
  rify
  simp [hn, hm]
  by_cases hmn' : m = n
  · simp [hmn']
    norm_num
  wlog hmn: m ≤ n
  · specialize this m n hn hm (Ne.symm hmn') (le_of_not_ge hmn)
    rwa [abs_sub_comm] at this
  apply le_of_lt <| calc (|↑⌊√2 * 10 ^ n⌋ / 10 ^ n - ↑⌊√2 * 10 ^ m⌋ / 10 ^ m|: ℝ)
    _ = |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2 - (↑⌊√2 * 10 ^ m⌋ / 10 ^ m - √2)| := by ring_nf
    _ ≤ |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2| + |↑⌊√2 * 10 ^ m⌋ / 10 ^ m - √2| := abs_sub _ _
    _ < 1 / 10 ^ 2 + 0.015 := by
      refine add_lt_add ?_ ?_
      · refine lt_of_lt_of_le sqrt_approx ?_
        exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)
      by_cases hm': m = 1
      · simp only [hm', abs_sub_comm, pow_one]
        rw [floor_sqrt_2_times_ten, abs_of_nonneg ?_, sub_lt_iff_lt_add']
        exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
        refine sub_nonneg.mpr ?_
        exact (Real.le_sqrt' (by norm_num)).mpr (by norm_num)
      refine lt_trans ?_ (show 1 / 10 ^ 2 < _ by norm_num)
      refine lt_of_lt_of_le sqrt_approx ?_
      exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)
    _ ≤ 0.1 := by norm_num

theorem Sequence.ex_5_1_10_c : (0.1:ℚ).EventuallySteady sqrt_two := 
  ⟨1, by simp [sqrt_two], ex_5_1_10_b⟩

/-- Proposition 5.1.11. The harmonic sequence, defined as a₁ = 1, a₂ = 1/2, ... is a Cauchy sequence. -/
theorem Sequence.IsCauchy.harmonic : (mk' 1 (fun n ↦ (1:ℚ)/n)).IsCauchy := by
  rw [IsCauchy.mk]
  intro ε hε
  -- We go by reverse from the book - first choose N such that N > 1/ε
  obtain ⟨ N, hN : N > 1/ε ⟩ := exists_nat_gt (1 / ε)
  have hN' : N > 0 := by
    observe : (1/ε) > 0
    replace : (N:ℚ) > 0 := this.trans hN
    norm_cast at this
  refine ⟨ N, by norm_cast, ?_ ⟩
  intro j hj k hk
  lift j to ℕ using (by linarith)
  lift k to ℕ using (by linarith)
  norm_cast at hj hk
  simp [show j ≥ 1 by linarith, show k ≥ 1 by linarith]

  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    /-
    We establish the following bounds:
    - 1/j ∈ [0, 1/N]
    - 1/k ∈ [0, 1/N]
    These imply that the distance between 1/j and 1/k is at most 1/N - when they are as "far apart" as possible.
    -/
    have : 1/j ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/j
    have : 1/k ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/k
    grind
  simp at *; apply hdist.trans
  rw [inv_le_comm₀] <;> try positivity
  order

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : Prop := ∀ i, |a i| ≤ M

/--
  Definition 5.1.12 (bounded sequences). Here we start sequences from 0 rather than 1 to align
  better with Mathlib conventions.
-/
lemma boundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop := ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℚ) : a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

lemma Sequence.boundedBy_iff {a: ℕ → ℚ} {M:ℚ} : (a: Sequence).BoundedBy M ↔ ∀ n, |a n| ≤ M := by
  rw [boundedBy_def]
  constructor
  · intro h n
    simpa using h n
  · intro h n
    have hM : 0 ≤ M := le_trans (abs_nonneg _) (h 0)
    by_cases hn: n < 0
    · simp [not_le.mpr hn, hM]
    simpa [not_lt.mp hn] using h n.toNat

abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.isBounded_def (a:Sequence) : a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

-- helper for when dealing with Nat Functions
lemma Sequence.isBounded_iff {a: ℕ → ℚ} : (a: Sequence).IsBounded ↔ ∃ M ≥ 0, ∀n, |a n| ≤ M := by
  rw [isBounded_def]
  peel with M hM
  exact boundedBy_iff

/-- Example 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by intro i; fin_cases i <;> norm_num

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).IsBounded := by
  by_contra h
  choose M hM_pos hM using h
  obtain ⟨ N, hN ⟩ := exists_nat_gt M
  replace hM := hM N
  simp at hM
  rw [abs_of_nonneg (by positivity)] at hM
  refine (not_lt.mpr ?_) hN
  refine le_trans ?_ hM
  refine (le_add_iff_nonneg_right (N:ℚ)).mpr rfl

/-- Example 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsBounded := by
  refine ⟨ 1, by norm_num, ?_ ⟩; intro i; by_cases h: 0 ≤ i <;> simp [h]

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  by_contra h; specialize h (1/2 : ℚ) (by norm_num)
  choose N h using h; specialize h N _ (N+1) _ <;> try omega
  by_cases h': Even N
  · simp [h'.neg_one_pow, (h'.add_one).neg_one_pow, Section_4_3.dist] at h
    norm_num at h
  observe h₁: Odd N
  observe h₂: Even (N+1)
  simp [h₁.neg_one_pow, h₂.neg_one_pow, Section_4_3.dist] at h
  norm_num at h

/-- Lemma 5.1.14 -/
lemma IsBounded.finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℚ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  refine ⟨ max M |a (Fin.last n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . exact (hM j).trans (le_max_left _ _)
  · exact le_max_right _ _

example {a b c: ℚ} : -a - b ≤ c ↔ -a ≤ c + b := by exact OrderedSub.tsub_le_iff_right (-a) b c

/-- Lemma 5.1.15 (Cauchy sequences are bounded) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  choose N hN_pos hN using h 1 rfl
  obtain ⟨N', hN'⟩ := Int.eq_ofNat_of_zero_le (Int.sub_nonneg_of_le hN_pos)
  let ⟨M, hM_pos, hM⟩ := IsBounded.finite fun (n: Fin N') => a (a.n₀ + n)
  refine ⟨max M (|a.seq N| + 1), by positivity, ?_⟩
  intro n
  by_cases hn: n < a.n₀
  · simp [a.vanish _ hn, hM_pos]
  replace hn := not_lt.mp hn
  by_cases hn': n < N
  · refine le_trans ?_ (le_max_left _ _)
    unfold Chapter5.BoundedBy at hM
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Int.sub_nonneg_of_le hn)
    replace hm := add_comm a.n₀ _ ▸ Int.sub_eq_iff_eq_add.mp hm
    simpa [← hm] using hM ⟨m, by omega⟩
  replace hn' := not_lt.mp hn'
  refine le_trans ?_ (le_max_right _ _)
  replace hN := hN N (by simp [hN_pos]) n (by simp [hn, hn'])
  simp [hN_pos, hn', Rat.Close] at hN
  rw [abs_le] at hN
  show |a.seq n| ≤ |a.seq N| + 1
  refine abs_le'.mpr ⟨?_, ?_⟩
  · apply le_trans (sub_neg_eq_add (a.seq N) 1 ▸ le_sub_comm.mp hN.left)
    apply add_le_add ?_ rfl
    exact le_abs_self _
  rw [add_comm, ← OrderedSub.tsub_le_iff_right, neg_sub_comm]
  refine le_trans ?_ hN.right
  refine sub_le_sub_right ?_ _
  exact neg_abs_le _

/-- Exercise 5.1.2 -/
theorem Sequence.isBounded_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
  (a + b:Sequence).IsBounded := by
    choose M M_pos hM using ha
    choose N N_pos hN using hb
    refine ⟨M + N, by positivity, fun n => ?_⟩
    calc
    _ = |(a: Sequence).seq n + (b: Sequence).seq n| := by 
      by_cases hn: 0 ≤ n
      · simp [hn]
      simp [hn]
    _ ≤ |(a: Sequence).seq n| + |(b: Sequence).seq n| := abs_add_le _ _
    _ ≤ M + N := add_le_add (hM _) (hN _)

theorem Sequence.isBounded_neg {a:ℕ → ℚ} (ha: (a:Sequence).IsBounded):
  (↑(-a): Sequence).IsBounded := by
    choose N N_pos hN using ha
    refine ⟨N, by positivity, fun n => ?_⟩
    calc
    _ = |(a: Sequence).seq n| := by
      by_cases hn: 0 ≤ n
      · simp [hn]
      simp [hn]
    _ ≤ N := hN n

theorem Sequence.isBounded_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
  (a - b:Sequence).IsBounded := by
    rw [sub_eq_add_neg]
    exact isBounded_add ha (isBounded_neg hb)

theorem Sequence.isBounded_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
  (a * b:Sequence).IsBounded := by
    choose M M_pos hM using ha
    choose N N_pos hN using hb
    refine ⟨M * N, by positivity, ?_⟩
    intro n
    calc
    _ = |((a: Sequence).seq n) * ((b: Sequence).seq n)| := by 
      by_cases hn: 0 ≤ n <;> simp [hn]
    _ = |(a: Sequence).seq n| * |(b: Sequence).seq n| := abs_mul _ _
    _ ≤ M * N := mul_le_mul (hM _) (hN _) (abs_nonneg _) M_pos

end Chapter5
