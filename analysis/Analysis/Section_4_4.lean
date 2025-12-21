import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · use ⌊x⌋
    exact Int.floor_eq_iff.mp rfl
  intro x1 x2 hx1 hx2
  have hx1' := lt_of_le_of_lt hx1.left hx2.right
  have hx2' := lt_of_le_of_lt hx2.left hx1.right
  norm_cast at hx1' hx2'
  omega

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  by_cases hx : x < 0
  · exact ⟨0, hx⟩
  replace hx := not_lt.mp hx
  have hnum : x.num ≥ 0 := Rat.num_nonneg.mpr hx
  have hden : (x.den: ℤ) > 0 := Int.natCast_pos.mpr <| Rat.den_pos x
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnum
  refine ⟨n + 1, ?_⟩
  apply Rat.lt_iff _ _ |>.mpr
  simp []
  norm_cast
  rw [Rat.num_natCast, Int.natCast_succ, add_mul, ← hn, one_mul]
  conv => lhs; rw [← add_zero x.num]
  refine Int.add_lt_add_of_le_of_lt ?_ hden
  exact le_mul_of_one_le_right hnum hden

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  by_contra h; choose a ha using h
  replace this (n k):  k ≤ a n := by
    induction k generalizing n
    case zero => exact zero_le _
    case succ k ih =>
      exact lt_of_le_of_lt (ih _) (ha _)
  exact (not_succ_le_self _) (this (0) (a 0 + 1))

/-- Exercise 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  use fun n => -n
  intro n
  simp

/-- Exercise 4.4.2 (b) -/
def Rat.pos_infinite_descent : Decidable (∃ a:ℕ → {x: ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  use fun n => ⟨1 / (n + 1), by 
    refine (Rat.lt_div_iff ?_).mpr ?_
    · exact Nat.cast_add_one_pos n
    simp
  ⟩
  intro n
  refine Subtype.mk_lt_mk.mpr ?_
  refine Nat.one_div_lt_one_div ?_
  exact lt_add_one n

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  by_cases hn: 2 ∣ n
  · refine Or.inl ?_
    exact even_iff_exists_two_mul.mpr hn
  refine Or.inr <| odd_iff_exists_bit1.mpr ?_
  have : 2 ∣ n - 1 := by omega
  use (n - 1) / 2
  rw [Nat.mul_div_cancel' this]
  omega

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  unfold Even Odd
  by_contra h
  obtain ⟨⟨r, hr⟩, ⟨k, hk⟩⟩ := h
  omega

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by grind
  wlog hpos : x > 0
  . apply this _ _ _ (show -x>0 by simp; order) <;> grind
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    have hnum_pos : x.num > 0 := num_pos.mpr hpos
    have hden_pos : x.den > 0 := den_pos x
    refine ⟨ Int.pos_iff_toNat_pos.mp hnum_pos, hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast, mul_comm] at hx; norm_cast at hx
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    · rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      · exact lt_of_pow_lt_pow_left' 2 <| calc
          _ < 2 * q^2 := lt_two_mul_self <| Nat.pow_pos hpos
          _ = (2 * k)^2 := by rw [hq]
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      obtain ⟨n, rfl⟩ := hp
      use 2 * n ^ 2 + 2 * n
      ring
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    grind
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
