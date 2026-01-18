import Mathlib.Tactic
import Analysis.Section_5_5

set_option profiler true


/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from `Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction m
  case zero => simp
  case succ m ih =>
    rw [← add_assoc, pow_succ, pow_succ, ← mul_assoc, ih]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction m
  case zero => simp
  case succ m ih =>
    rw [pow_succ, ih, pow_add, Nat.mul_succ]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction n
  case zero => simp_rw [pow_zero, mul_one]
  case succ m ih =>
    rw [pow_succ, pow_succ, pow_succ, ih]
    ring

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zero_pow hn.ne']⟩
  induction n
  case zero => contradiction
  case succ n ih =>
    clear hn
    by_cases hn : n = 0
    · rwa [hn, zero_add, pow_one] at h
    obtain h | h := mul_eq_zero.mp (pow_succ _ _ ▸ h) 
      <;> try assumption
    exact ih (Nat.zero_lt_of_ne_zero hn) h

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction n
  case zero => exact pow_zero x ▸ zero_le_one
  case succ n ih =>
    rw [pow_succ]
    positivity

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction n
  case zero => exact pow_zero x ▸ zero_lt_one
  case succ n ih =>
    rw [pow_succ]
    positivity

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction n
  case zero => simp
  case succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hxy hy (pow_nonneg _ <| hy.trans hxy)

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [pow_succ, pow_succ]
  exact mul_lt_mul' (pow_ge_pow _ _ _ hxy.le hy) hxy hy (pow_pos _ <| hy.trans_lt hxy)

theorem Real.pow_ge_pow_iff {x y:Real} {n:ℕ} (hx: x ≥ 0) (hy: y ≥ 0) (hn: n > 0): x ≥ y ↔ x^n ≥ y^n := by
  refine ⟨fun h => pow_ge_pow _ _ _ h hy, fun h => ?_⟩
  contrapose! h
  exact pow_gt_pow y x n h hx hn

theorem Real.pow_gt_pow_iff {x y:Real} {n:ℕ} (hx: x ≥ 0) (hy: y ≥ 0) (hn: n > 0): x > y ↔ x^n > y^n := by
  refine ⟨fun h => pow_gt_pow _ _ _ h hy hn, fun h => ?_⟩
  contrapose! h
  exact pow_ge_pow y x n h hx

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := by
  induction n
  case zero => simp 
  case succ n ih =>
    rw [pow_succ, pow_succ, abs_mul, ih]

theorem Real.pow_inv (x: Real) (n: ℕ) : (x⁻¹) ^ n = (x ^ n)⁻¹ := by
  induction n
  case zero => 
    rw [pow_zero, pow_zero, inv_one]
  case succ n ih =>
    rw [pow_succ, pow_succ, ih, mul_inv]

theorem Real.pow_div (x y: Real) (n: ℕ) : (x / y) ^ n = x ^ n / y ^ n := calc
  _ = x ^ n * (y⁻¹) ^ n := mul_pow _ _ _
  _ = x ^ n * (y^n) ⁻¹ := by rw [pow_inv]

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from `DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

lemma Real.zpow_neg' {x:Real} (n:ℤ) : x^(-n) = 1 / (x^n) := by
  cases n
  case ofNat => simp
  case negSucc n => 
    simp
    rw [← Nat.cast_add_one, pow_eq_pow]

theorem Real.zpow_succ' {x:Real} (n:ℕ) : x^(n + 1:ℤ) = x^n * x := by 
  rw [← Nat.cast_add_one, pow_eq_pow, pow_succ]

theorem Real.zpow_succ {x:Real} (n: ℤ) (hx: x ≠ 0) : x^(n + 1) = x^n * x := by 
  cases n
  case ofNat n => exact zpow_succ' _
  case negSucc n =>
    rw [Int.negSucc_eq, neg_add, 
      neg_add_cancel_right, zpow_neg, 
      ← neg_add, ← Nat.cast_add_one,
      zpow_neg, pow_succ, ← div_div, 
      div_mul_cancel₀ _ hx
    ]

theorem Real.zpow_pred {x:Real} (n: ℤ) (hx: x ≠ 0) : x^(n - 1) = x^n / x := by 
  rw [show n - 1 = -(-n + 1) by ring, zpow_neg', zpow_succ _ hx, 
    ← div_div, zpow_neg', one_div_div, div_one]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  induction m
  case zero => simp
  case succ m ih => 
    rw [zpow_succ', ← add_assoc, zpow_succ _ hx, ← ih, pow_eq_pow, mul_assoc]
  case pred m ih =>
    rw [add_sub, zpow_pred _ hx, zpow_pred _ hx, ← ih, mul_div_assoc]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) : (n m:ℤ) → (x^n)^m = x^(n*m)
  | (n: ℕ), (m: ℕ) => Int.natCast_mul _ _ |>.symm ▸ by simp_rw [pow_eq_pow, pow_mul]
  | .negSucc n, (m: ℕ) => by
    simp only [Int.negSucc_eq, Int.neg_mul, ← Int.natCast_succ, ← Int.natCast_mul, 
      zpow_neg', pow_eq_pow, pow_div, one_pow, pow_mul]
  | (n: ℕ), .negSucc m => by
    simp only [Int.negSucc_eq, Int.mul_neg, ← Int.natCast_succ, ← Int.natCast_mul, 
      zpow_neg', pow_eq_pow, pow_mul]
  | .negSucc n, .negSucc m => by
    simp only [Int.negSucc_eq, Int.neg_mul_neg, ← Int.natCast_succ, ← Int.natCast_mul,
      zpow_neg, pow_eq_pow, pow_div, one_pow, one_div_one_div, pow_mul]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) : (n:ℤ) → (x*y)^n = x^n * y^n
  | (n: ℕ) => by
    simp_rw [pow_eq_pow, mul_pow]
  | .negSucc n => by
    simp_rw [Int.negSucc_eq, ← Nat.cast_add_one, zpow_neg, mul_pow, mul_div, mul_one, div_div]

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := match n with
  | (n: ℕ) => pow_eq_pow _ _ ▸ pow_pos n hx
  | .negSucc n => by
    rw [Int.negSucc_eq, ← Nat.cast_add_one, zpow_neg]
    exact one_div_pos.mpr <| pow_pos _ hx

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  lift n to ℕ using hn.le
  exact pow_ge_pow _ _ _ hxy hy.le

theorem Real.zpow_gt_zpow {x y:Real} {n:ℤ} (hxy: x > y) (hy: y > 0) (hn: n > 0): x^n > y^n := by
  lift n to ℕ using hn.le
  exact pow_gt_pow _ _ _ hxy hy.le (Int.natCast_pos.mp hn)

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  obtain ⟨n, rfl⟩ : ∃n', n = -n' := ⟨-n, Int.neg_neg _ ▸ rfl⟩
  lift n to ℕ using (Int.pos_of_neg_neg hn).le; clear hn
  rw [zpow_neg, zpow_neg, one_div_le_one_div]
  · exact pow_ge_pow _ _ _ hxy hy.le
  · exact pow_pos _ (hy.trans_le hxy)
  · exact pow_pos _ hy

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem Real.pow_inj {x y: Real} {n:ℕ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  wlog h: y ≤ x
  · replace h := not_le.mp h 
    exact this hy hx hn (eq_comm.mp hxy) (le_of_lt h) |> eq_comm.mp
  by_contra h'
  refine (ne_of_lt ?_).symm hxy
  replace h := h.lt_of_ne' h'
  exact pow_gt_pow _ _ n h (le_of_lt hy) (Nat.zero_lt_of_ne_zero hn)

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) 
  : x = y := match n with
    | (n: ℕ) => pow_inj hx hy (hn <| congrArg Nat.cast ·) hxy
    | .negSucc (n) => by
      simp_rw [Int.negSucc_eq, ← Int.natCast_add_one, zpow_neg, one_div, inv_inj] at hxy
      exact pow_inj hx hy (Nat.zero_ne_add_one n).symm hxy

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) : (n:ℤ) → |x|^n = |x^n|
  | (n: ℕ) => pow_abs _ _
  | .negSucc n => by
    rw [Int.negSucc_eq, ← Nat.cast_add_one, zpow_neg, zpow_neg, abs_div, pow_abs, abs_one]

/-- Definition 5.6.2.  We permit ``junk values'' when `x` is negative or `n` vanishes. -/
noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  refine ⟨0, le_refl _, ?_⟩
  rwa [zero_pow <| Nat.ne_zero_of_lt hn]

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      have := pow_gt_pow _ _ _ hy' zero_le_one hn
      rwa [one_pow] at this
    exact h.not_gt <| hy'.trans_le hy.right
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    refine pow_gt_pow _ _ _ hy' (zero_le_one.trans_lt h).le hn |>.trans_le' ?_
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one.mpr hn
    clear y hy hy' hn
    rw [pow_succ, mul_comm]
    have := pow_ge_pow _ _ n h.le zero_le_one
    calc
    _ = x * 1 := by ring
    _ ≤ x * x^n := by
      refine mul_le_mul (le_refl _) ?_ zero_le_one (zero_le_one.trans h.le)
      rwa [one_pow] at this
  linarith

theorem Real.pow_sub_pow_lt {a b: Real} {n: ℕ} (hn: 1 < n) (hapos: 0 ≤ a) (hab: a < b) :
  b ^ n - a ^ n < (b - a) * n * (b ^ (n - 1)) := by
    obtain ⟨n, rfl⟩ : ∃n', n' + 2 = n := ⟨n - 2, Nat.sub_add_cancel hn⟩; clear hn
    rw [mul_assoc]
    induction n
    case zero =>
      simp
      calc b^2 - a^2
      _ = (b - a) ^ 2 + (b - a) * 2 * a := by ring_nf
      _ < 2 * (b - a) ^ 2 + (b - a) * 2 * a := by 
        refine add_lt_add_right _ ?_ 
        refine lt_two_mul_self ?_
        refine sq_pos_of_pos ?_
        exact sub_pos.mpr hab
      _ = (b - a) * (2 * b) := by ring_nf
    case succ n ih =>
      set m := n + 2 
      simp [show n + 1 + 2 = m + 1 by rfl]
      refine div_lt_iff₀' (sub_pos.mpr hab) |>.mp ?_
      calc (b ^ (m + 1) - a ^ (m + 1)) / (b - a)
        _ = b * ((b ^ m - a ^ m) / (b - a)) + a ^ m * (b - a) / (b - a) := by ring_nf
        _ = b * ((b ^ m - a ^ m) / (b - a)) + a ^ m := by 
          rw [mul_div_cancel_right₀ _ (sub_ne_zero_of_ne hab.ne')]
        _ < b * (m * b ^ (m - 1)) + b ^ m := by
          refine add_lt_add (mul_lt_mul_of_pos_left ?_ <| hapos.trans_lt hab) ?_
          exact div_lt_iff₀' (sub_pos.mpr hab) |>.mpr ih
          exact pow_gt_pow _ _ _ hab hapos (Nat.zero_lt_succ _)
        _ = (m + 1) * b ^ m := by 
          rw [← mul_assoc, mul_comm, ← mul_assoc, ← pow_succ, 
            Nat.sub_add_cancel, add_mul, one_mul, mul_comm]
          exact Nat.le_add_left ..

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by
    rw [
      eq_comm, 
      ← isLUB_sSup (rootset_nonempty hx _ hn) (rootset_bddAbove _ hn),
      iff_comm
    ]
    refine ⟨?_, fun ⟨h_upper_bound, hM⟩ => ?_⟩
    · rintro rfl
      refine ⟨fun y' hy' => ?_, fun y' hy' => hy' ⟨hy, le_refl _⟩⟩
      exact pow_ge_pow_iff hy hy'.left hn |>.mpr hy'.right
    obtain hx | hx := hx.eq_or_lt
    · subst x; clear hx
      rw [← zero_pow (Nat.ne_zero_of_lt hn)]
      congr
      refine (hM ?_).antisymm hy
      intro x ⟨hxpos, hx⟩
      rwa [← zero_pow (Nat.ne_zero_of_lt hn), 
        ← ge_iff_le, ← pow_ge_pow_iff (le_refl _) hxpos hn] at hx
    obtain hn | hn := hn.eq_or_lt
    · simp only [← hn, pow_one] at hM h_upper_bound ⊢
      exact h_upper_bound ⟨hx.le, le_refl _⟩ |>.antisymm' (hM fun y hy => hy.2)
    by_contra!
    obtain h | h := trichotomous' (y^n) x |>.elim Or.inl (·.resolve_right this |> Or.inr)
    · clear * - hx hy hM hn h
      rw [mem_lowerBounds] at hM
      contrapose! hM; clear hM
      replace hy : 0 < y := pow_gt_pow_iff hy (le_refl _) hn.le |>.mpr (by
        rw [zero_pow (Nat.ne_zero_of_lt hn)]
        exact hx.trans h
      )
      let ε := (y ^ n - x) / (n * y ^ (n - 1))
      have εpos : 0 < ε := by
        unfold ε
        refine div_pos ?_ (mul_pos ?_ ?_)
        exact sub_pos.mpr h       
        exact Nat.cast_pos'.mpr hn.le
        exact pow_pos _ hy  
      have ε_lt_y : ε < y := by
        unfold ε
        refine div_lt_iff₀ (by positivity) |>.mpr ?_
        conv =>
          rhs
          field_simp
          rw [mul_comm y, mul_assoc, mul_comm y, ← pow_succ, Nat.sub_add_cancel hn.le]
        refine (sub_lt_self _ hx).trans ?_
        exact lt_mul_left (hx.trans h) (Nat.one_lt_cast.mpr hn)
      refine ⟨y - ε, ?_, sub_lt_self y εpos⟩
      intro t ⟨tnonneg, ht⟩
      contrapose! ht
      rw [← sub_lt_sub_iff_left (y^n)]
      have := sub_pos.mpr ε_lt_y |>.le
      calc y ^ n - t ^ n
        _ < y ^ n - (y - ε) ^ n := sub_lt_sub_left (pow_gt_pow _ _ _ ht this hn.le) _
        _ < (y - (y - ε)) * n * y ^ (n - 1) := pow_sub_pow_lt hn this (sub_lt_self y εpos)
        _ = (y ^ n - x) / (n * y ^ (n - 1)) * n * y ^ (n - 1) := by simp [ε]
        _ = y ^ n - x := by field_simp
    · rw [mem_upperBounds] at h_upper_bound
      contrapose! h_upper_bound
      clear * - hx hy hn h
      let ε := min 1 ((x - y^n) / (n * (y + 1)^(n - 1)))
      have εpos : 0 < ε := by
        unfold ε
        refine lt_min zero_lt_one ?_
        refine div_pos ?_ (by positivity)
        exact sub_pos.mpr h
      refine ⟨y + ε, ⟨by positivity, ?_⟩, lt_add_of_pos_right _ εpos⟩
      refine sub_le_sub_iff_right (y^n) |>.mp ?_
      calc (y + ε) ^ n - y ^ n
      _ ≤ (y + ε - y) * ↑n * (y + ε) ^ (n - 1) := 
        (pow_sub_pow_lt hn hy <| lt_add_of_pos_right _ εpos).le
      _ = ε * (↑n * (y + ε) ^ (n - 1)) := by ring
      _ ≤ ε * (↑n * (y + 1) ^ (n - 1)) := by
        refine mul_le_mul_iff_right₀ (by positivity) |>.mpr ?_
        refine mul_le_mul_iff_right₀ (by positivity) |>.mpr ?_
        refine pow_ge_pow _ _ _ ?_ (by positivity)
        refine add_le_add_right ?_ _
        refine min_le_of_left_le (by norm_num)
      _ = (min 1 ((x - y^n) / (n * (y + 1)^(n - 1)))) * (n * (y + 1) ^ (n - 1)) := rfl
      _ ≤ (x - y^n) / (n * (y + 1)^(n - 1)) * (n * (y + 1) ^ (n - 1)) := by
        refine mul_le_mul_iff_left₀ (by positivity) |>.mpr ?_
        refine min_le_of_right_le (le_refl _)
      _ ≤ x - y^n := by
        refine div_mul_cancel₀ (G₀ := Real) _ ?_ ▸ (le_refl _)
        refine ne_of_gt ?_
        refine mul_pos (Nat.cast_pos'.mpr hn.le) ?_
        refine pow_pos (n - 1) ?_
        exact hy.trans_lt (lt_add_one _)

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  set y := x.root n with ← hy
  rw [← isLUB_sSup (rootset_nonempty hx _ hn) (rootset_bddAbove _ hn)] at hy
  refine hy.left ?_
  refine ⟨le_refl _, ?_⟩
  rwa [zero_pow (Nat.ne_zero_of_lt hn)]

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x.root n) ^ n = x :=
  eq_root_iff_pow_eq hx.le (root_nonneg hx.le hn) hn |>.mp rfl

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x ^ n).root n = x :=
  eq_root_iff_pow_eq (pow_nonneg _ hx) hx hn |>.mpr rfl |>.symm

theorem Real.root_of_zero {n:ℕ} (hn: n ≥ 1) : Real.root 0 n = 0 := by
  have : {y: Real | y ≥ 0 ∧ y ^ n ≤ 0} = {0} := by
    have zero_pow_n := zero_pow (M₀ := Real) (Nat.ne_zero_of_lt hn) |>.symm
    ext y
    constructor
    · rintro ⟨hnonneg, hy⟩
      refine hnonneg.antisymm' ?_
      refine pow_ge_pow_iff (le_refl _) hnonneg hn |>.mpr ?_
      exact zero_pow_n ▸ hy
    · rintro rfl
      exact ⟨le_refl _, zero_pow_n ▸ le_refl 0⟩
  convert this ▸ csSup_singleton 0

theorem Real.root_inj {x y: Real} {n:ℕ} (hx : x ≥ 0) (hy : y ≥ 0) (hn: n ≥ 1) 
  (hxy: x.root n = y.root n) : x = y := by
    simpa [hx, hy, hn, Real.pow_of_root] using congr($hxy ^ n)

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  obtain hx | hx := hx.eq_or_lt
  · refine iff_of_false (not_lt.mpr ?_) hx.symm.le.not_gt
    rw [← hx, root_of_zero hn]
  refine iff_of_true ?_ hx
  refine pow_gt_pow_iff ?_ (le_refl _) hn |>.mpr ?_
  · exact root_nonneg hx.le hn
  rwa [Real.pow_of_root hx.le hn, zero_pow (Nat.ne_zero_of_lt hn)]

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) 
  : x > y ↔ x.root n > y.root n := by
    constructor
    · intro h
      refine pow_gt_pow_iff (root_nonneg hx hn) (root_nonneg hy hn) hn |>.mpr ?_
      simpa [hx, hy, hn, Real.pow_of_root] using h
    · intro h; contrapose! h
      refine pow_ge_pow_iff (root_nonneg hy hn) (root_nonneg hx hn) hn |>.mpr ?_
      simpa [hx, hy, hn, Real.pow_of_root] using h

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by sorry

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by sorry

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by sorry

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by sorry

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by sorry

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by sorry

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by sorry

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  -- This proof is written to follow the structure of the original text.
  wlog ha: a > 0 generalizing a b a' b'
  . simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    . replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by sorry
    simp_all
  have : a' > 0 := by sorry
  field_simp at hq
  lift a to ℕ using by order
  lift a' to ℕ using by order
  norm_cast at *
  set y := x.root (a*b')
  have h1 : y = (x.root b').root a := by rw [root_root, mul_comm] <;> linarith
  have h2 : y = (x.root b).root a' := by rw [root_root, ←hq] <;> linarith
  have h3 : y^a = x.root b' := by rw [h1]; apply pow_of_root (root_nonneg _ _) <;> linarith
  have h4 : y^a' = x.root b := by rw [h2]; apply pow_of_root (root_nonneg _ _) <;> linarith
  rw [←h3, pow_mul, mul_comm, ←pow_mul, h4]

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  . have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by sorry

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by sorry

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  sorry

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  sorry

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  sorry

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  sorry

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  sorry

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  sorry

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  sorry

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  sorry

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by sorry

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  sorry

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  sorry

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.

end Chapter5
