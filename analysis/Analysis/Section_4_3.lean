import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers `ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by grind

abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by grind

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by grind

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by
  apply max_le
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  rw [neg_add]
  · exact add_le_add (le_max_right _ _) (le_max_right _ _)

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  constructor
  · intro h
    exact max_le_iff.mpr ⟨h.right, neg_le.mp h.left⟩
  · intro h
    replace h := max_le_iff.mp h
    exact ⟨neg_le.mp h.right, h.left⟩

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by
  exact abs_le_iff _ _ |>.mpr (le_refl _)


/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by
  simp_rw [← abs_eq_abs, abs]
  by_cases hx' : x = 0
  · simp [hx']
  by_cases hy' : y = 0
  · simp [hy']
  by_cases hx : x > 0
  <;> by_cases hy : y > 0
  · simp [hx, hy]
  · replace hy' := lt_of_le_of_ne (not_lt.mp hy) hy'
    simp [hx, hy, hy']
  · replace hx' := lt_of_le_of_ne (not_lt.mp hx) hx'
    simp [hx, hy, hx']
  . replace hx' := lt_of_le_of_ne (not_lt.mp hx) hx'
    replace hy' := lt_of_le_of_ne (not_lt.mp hy) hy'
    simp [hx, hy, hx', hy', mul_pos_of_neg_of_neg hx' hy']

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by
  show max _ _ = max _ _
  rw [max_comm, neg_neg]


/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := abs_nonneg _

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  rw [abs_eq_zero_iff, sub_eq_zero]

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  show |_| = |_|
  rw [← abs_neg, neg_sub]

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  show |_| ≤ |_| + |_|
  rw [← sub_add_sub_cancel x y z]
  exact abs_add _ _

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  simp [close_iff]
  norm_num

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  simp [close_iff]
  norm_num

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  simp [close_iff, le_of_lt hε]

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by
  simp [close_iff]

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  refine ⟨fun h ε hε => by simp [close_iff, h, le_of_lt hε], ?_⟩
  intro h
  simp [close_iff] at h
  by_contra hxy
  have : |x - y| > 0 := abs_sub_pos.mpr hxy
  set q := |x - y|
  replace h := h _ (half_pos this)
  have : q / 2 < q := div_two_lt_of_pos this
  exact (not_lt.mpr h) this

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  simp [close_iff, dist_symm]

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) : (ε + δ).Close x z := 
  le_trans (dist_le _ _ _) <| add_le_add hxy hyz

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
  (ε + δ).Close (x+z) (y+w) := calc
    _ = |x - y + (z - w)| := by ring_nf
    _ ≤ |x - y| + |z - w| := abs_add _ _
    _ ≤ ε + δ             := add_le_add hxy hzw


/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := calc
      _ = |x - y - (z - w)| := by ring_nf
      _ ≤ |x - y| + |z - w| := abs_sub _ _
      _ ≤ ε + δ             := add_le_add hxy hzw

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
  ε'.Close x y := le_trans hxy hε

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
    wlog hbetween': y ≤ w ∧ w ≤ z
    · replace hbetween := hbetween.elim (hbetween' · |>.elim) id
      exact this hxz hxy (Or.inl hbetween) hbetween
    obtain ⟨hyw, hwz⟩ := hbetween'; clear hbetween
    by_cases h: z = y
    · replace h : w = y := le_antisymm (h ▸ hwz) hyw
      exact h ▸ hxy
    replace h : y < z := lt_of_le_of_ne (hyw.trans hwz) (Ne.symm h)
    have h' : z - y > 0 := (Rat.lt_iff_sub_pos _ _).mp h
    set t := (w - y) / (z - y)
    obtain hw : (1 - t) * y + t * z = w := calc
      _ = y + t * (z - y) := by ring
      _ = w := by simp [t, ne_of_lt h' |>.symm]
    have ht: 0 ≤ t ∧ t ≤ 1 := by
      constructor
      · have : 0 ≤ w - y := (Rat.le_iff_sub_nonneg y w).mp hyw
        exact Rat.div_nonneg this (le_of_lt h')
      · refine (div_le_one h').mpr ?_
        exact tsub_le_tsub_right hwz y
    rw [← hw]
    calc
    _ = |(1 - t) * (x - y) + t * (x - z)| := by ring_nf
    _ ≤ |(1 - t) * (x - y)| + |t * (x - z)| := abs_add _ _
    _ = |1 - t| * |x - y| + |t| * |x - z| := by rw [abs_mul, abs_mul]
    _ = (1 - t) * |x - y| + t * |x - z| := by 
      rw [abs_of_nonneg ht.left, abs_of_nonneg _]
      exact (Rat.le_iff_sub_nonneg t 1).mp ht.right
    _ ≤ (1 - t) * ε + t * ε := add_le_add 
      (Rat.mul_le_mul_of_nonneg_left hxy ((Rat.le_iff_sub_nonneg _ _).mp ht.right))
      (Rat.mul_le_mul_of_nonneg_left hxz ht.left)
    _ = ε := by ring

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
  (ε*|z|).Close (x * z) (y * z) := calc
    _ = |(x - y) * z| := by ring_nf
    _ = |x - y| * |z| := abs_mul _ _
    _ ≤ ε * |z| := mul_le_mul hxy (le_refl _) (abs_nonneg _) (abs_nonneg _ |>.trans hxy)

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
  (ε*|z|+δ*|y|).Close (x * z) (y * w) := calc
    _ = |(x - y) * z + (z - w) * y| := by ring_nf
    _ ≤ |(x - y) * z| + |(z - w) * y| := abs_add _ _
    _ = |x - y| * |z| + |z - w| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ ε * |z| + δ * |y| := add_le_add
      (Rat.mul_le_mul_of_nonneg_right hxy (abs_nonneg _))
      (Rat.mul_le_mul_of_nonneg_right hzw (abs_nonneg _))

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := Rat.pow_zero x

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction m
  case zero =>
    rw [pow_zero]
    ring
  case succ m ih =>
    rw [pow_succ, ← mul_assoc, ih]
    ring

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction m
  case zero => ring
  case succ m ih =>
    rw [pow_succ, ih]
    ring

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction n
  case zero =>
    rw [pow_zero, pow_zero, pow_zero, one_mul]
  case succ m ih =>
    rw [pow_succ, ih]
    ring

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction n
    case zero => contradiction
    case succ n ih =>
      obtain h|h := Rat.mul_eq_zero.mp (pow_succ _ _ ▸ h)
      · by_cases hn : n = 0
        · rw [hn, pow_zero] at h
          contradiction
        exact ih (Nat.zero_lt_of_ne_zero hn) h
      exact h
  · subst x
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_lt hn).symm
    rw [pow_succ, mul_zero]

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction n
  case zero => rw [pow_zero]; rfl
  case succ n ih =>
    rw [pow_succ]
    exact Rat.mul_nonneg ih hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction n
  case zero => rw [pow_zero]; rfl
  case succ n ih =>
    rw [pow_succ]
    exact Rat.mul_pos ih hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction n
  case zero => rw [pow_zero, pow_zero]
  case succ n ih =>
    rw [pow_succ, pow_succ]
    refine mul_le_mul ih hxy hy ?_
    exact pow_nonneg _ (hy.trans hxy)

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  induction n
  case zero => contradiction
  case succ n ih =>
    by_cases hn': n = 0
    · rwa [hn', zero_add, pow_one, pow_one]
    replace hn: n > 0 := lt_of_le_of_ne (Nat.zero_le n) (Ne.symm hn')
    rw [pow_succ, pow_succ]
    refine mul_lt_mul' (le_of_lt <| ih hn) hxy hy ?_
    exact pow_pos _ (lt_of_le_of_lt hy hxy)

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by
  induction n
  case zero => rw [pow_zero, pow_zero, abs_one]
  case succ n ih =>
    rw [pow_succ, pow_succ, ih, abs_mul]

theorem pow_inv (x: ℚ) (n: ℕ) : (x⁻¹) ^ n = (x ^ n)⁻¹ := by
  induction n
  case zero => 
    rw [pow_zero, pow_zero, inv_one]
  case succ n ih =>
    rw [pow_succ, pow_succ, Rat.inv_mul_rev, ← ih, mul_comm]

theorem pow_div (x y: ℚ) (n: ℕ) : (x / y) ^ n = x ^ n / y ^ n := calc
  _ = x ^ n * (y⁻¹) ^ n := mul_pow _ _ _
  _ = x ^ n * (y^n) ⁻¹ := by rw [pow_inv]

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp
theorem zpow_neg' (x:ℚ) (n:ℤ) : x^(-n) = 1/(x^n) := by simp

example (x: ℚ) : 1 / x = x⁻¹ := one_div x

example (x: ℚ) : x⁻¹ = x^(-(1: ℤ)) := (zpow_neg_one x).symm

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

theorem zpow_zero (x:ℚ) : x^(0:ℤ) = 1 := by
  rw [show (0: ℤ) = (0: ℕ) from rfl, pow_eq_zpow, pow_zero]
theorem zpow_neg_one (x:ℚ) : x^(-1:ℤ) = 1 / x := by simp
theorem zpow_one (x:ℚ) : x^(1:ℤ) = x := by simp

example (n m: ℚ) : 1 / n *m = 1 * m /n   := by exact Eq.symm (mul_div_right_comm 1 m n)

theorem zpow_succ' (x:ℚ) (n:ℕ) : x^((n: ℤ) + 1) = x^(n: ℤ) * x := Field.zpow_succ' n x

example (a b : ℚ) (hb : b ≠ 0) : a / b * b = a := by exact Rat.div_mul_cancel hb

theorem zpow_succ {x:ℚ} (hx: x ≠ 0) : (n:ℤ) → x^(n + 1) = x^n * x
  | .ofNat n => by simp [zpow_succ']
  | -1 => by simp [hx]
  | .negSucc (n + 1) => by
    rw [Int.negSucc_eq, 
      show -((n.succ: ℤ) + 1) + 1 = -n.succ by omega,
      show -((n.succ: ℤ) + 1) = -n.succ.succ by omega,
    ]
    conv =>
      rhs
      rw [zpow_neg, pow_succ, ← div_div, Rat.div_mul_cancel hx, ← zpow_neg]

theorem zpow_pred {x:ℚ} (hx: x ≠ 0) (n:ℤ) : x^(n - 1) = x^n / x := calc
  _ = x ^ (-(-n + 1)) := by ring_nf
  _ = 1 / x ^ (-n + 1) := zpow_neg' _ _
  _ = _ := by rw [zpow_succ hx, ← div_div, ← zpow_neg', neg_neg]

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  induction m
  case zero => simp_rw [zpow_zero, mul_one, add_zero]
  case succ m ih =>
    rw [zpow_succ hx, ← mul_assoc, ← add_assoc, ih, zpow_succ hx]
  case pred m ih =>
    rw [zpow_pred hx, ← mul_div_assoc, ← add_sub_assoc, ih, ← zpow_pred hx]

theorem zpow_eq_zero (x: ℚ) (n: ℤ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  refine ⟨?_, fun h => ?_⟩
  · intro h
    induction n
    case zero => contradiction
    case succ n ih =>
      obtain h|h := Rat.mul_eq_zero.mp (pow_succ _ _ ▸ h)
      · by_cases hn' : n = 0
        · rw [hn', pow_zero] at h
          contradiction
        exact ih (lt_of_le_of_ne (Int.natCast_nonneg n) (by omega)) h
      exact h
    case pred n ih =>
      by_cases hn' : n = 0
      · simpa [hn'] using h
      by_contra hx'
      obtain h|h := Rat.mul_eq_zero.mp (zpow_pred hx' _ ▸ h)
      · refine hx' <| ih ?_ h
        omega
      exact hx' <| inv_eq_zero.mp h
  · subst x
    obtain ⟨n, rfl⟩ : ∃(n': ℕ), n = n' := ⟨n.natAbs, (Int.natAbs_of_nonneg (le_of_lt hn)).symm⟩
    replace hn: 0 < n := Int.natCast_pos.mp hn
    rw [pow_eq_zpow, zero_pow (ne_of_lt hn).symm]

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ)  : (n m:ℤ) → (x^n)^m = x^(n*m)
  | (n: ℕ), (m: ℕ) => Int.natCast_mul _ _ |>.symm ▸ by simp_rw [pow_eq_zpow, pow_mul]
  | .negSucc n, (m: ℕ) => by
    simp only [Int.negSucc_eq, Int.neg_mul, ← Int.natCast_succ, ← Int.natCast_mul, 
      zpow_neg', pow_eq_zpow, pow_div, one_pow, pow_mul]
  | (n: ℕ), .negSucc m => by
    simp only [Int.negSucc_eq, Int.mul_neg, ← Int.natCast_succ, ← Int.natCast_mul, 
      zpow_neg', pow_eq_zpow, pow_mul]
  | .negSucc n, .negSucc m => by
    simp only [Int.negSucc_eq, Int.neg_mul_neg, ← Int.natCast_succ, ← Int.natCast_mul,
      zpow_neg, pow_eq_zpow, pow_div, one_pow, one_div_one_div, pow_mul]

example {a b c d: ℚ} : (a / b) * (c / d) = (a * c) / (b * d) := by exact div_mul_div_comm a b c d

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) : (n:ℤ) → (x*y)^n = x^n * y^n
  | (n: ℕ) => by 
    simp_rw [pow_eq_zpow, mul_pow]
  | .negSucc n => by 
    simp_rw [Int.negSucc_eq, ← Int.natCast_succ, zpow_neg, div_mul_div_comm, one_mul, mul_pow]


/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := match n with
  | (n: ℕ) => by
      simp_rw [pow_eq_zpow, pow_pos n hx]
  | .negSucc n => by
      simp_rw [Int.negSucc_eq, zpow_neg', zpow_succ (ne_of_lt hx).symm]
      refine one_div_pos.mpr ?_
      refine mul_pos ?_ hx
      exact pow_eq_zpow _ _ ▸ pow_pos _ hx

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  obtain ⟨n, rfl⟩ : ∃(n': ℕ), n = n' := Int.eq_ofNat_of_zero_le (le_of_lt hn)
  exact pow_ge_pow _ _ _ hxy (le_of_lt hy)

example {a b: ℚ} (ha: a > 0) (hb: b > 0) : 1 / a ≤ 1 / b ↔ b ≤ a := by exact one_div_le_one_div ha hb

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  obtain ⟨n, rfl⟩ : ∃(n': ℕ), n = -n' := Int.exists_eq_neg_ofNat (le_of_lt hn)
  rw [zpow_neg, zpow_neg]
  refine one_div_le_one_div ?_ ?_ |>.mpr ?_
  exact pow_pos _ (lt_of_lt_of_le hy hxy)
  exact pow_pos _ hy
  exact pow_ge_pow _ _ _ hxy (le_of_lt hy)

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem pow_inj {x y:ℚ} {n:ℕ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  wlog h: y ≤ x
  · replace h := not_le.mp h 
    exact this hy hx hn (eq_comm.mp hxy) (le_of_lt h) |> eq_comm.mp
  by_contra h'
  replace h := lt_of_le_of_ne h (Ne.symm h')
  have := pow_gt_pow _ _ n h (le_of_lt hy) (Nat.zero_lt_of_ne_zero hn)
  exact (ne_of_lt this).symm hxy

theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := match n with
  | (n: ℕ) => by
    rw [pow_eq_zpow, pow_eq_zpow] at hxy
    exact pow_inj hx hy (fun a ↦ hn (congrArg Nat.cast a)) hxy
  | .negSucc n => by 
    simp_rw [Int.negSucc_eq, ← Int.natCast_succ, zpow_neg, one_div, inv_inj] at hxy
    exact pow_inj hx hy (Nat.zero_ne_add_one n).symm hxy


/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) : (n:ℤ) → |x|^n = |x^n|
  | (n: ℕ) => by
    simp_rw [pow_eq_zpow, pow_abs]
  | .negSucc n => by
    simp_rw [Int.negSucc_eq, ← Int.natCast_succ, zpow_neg, abs_div, pow_abs, abs_one]

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by sorry
