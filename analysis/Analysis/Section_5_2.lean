import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

example {a b c: Prop} : (a → b → c) ↔ (b → a → c) := by exact imp.swap

theorem Rat.closeSeq_symm {ε: ℚ} {a b: Sequence} :
  ε.CloseSeq a b ↔ ε.CloseSeq b a := by
    peel with n
    rw [imp.swap]
    peel with hb ha
    exact Section_4_3.close_symm _ _ _

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by 
  intro n hn1 hn2
  simp at hn1 hn2
  lift n to ℕ using hn1; clear hn2
  calc (|(-1) ^ n - 1.1 * (-1) ^ n|: ℚ)
  _ = |(1 - 1.1) * (-1) ^ n| := by ring_nf
  _ = |(1 - 1.1)| * |(-1) ^ n| := abs_mul _ _
  _ = |(1 - 1.1)| * |(-1)| ^ n := by rw [abs_pow]
  _ = 0.1 := by norm_num
  _ ≤ 0.1 := le_refl _

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  by_contra h
  specialize h 0 (le_refl _) 1 (by simp)
  unfold Rat.Close at h
  norm_num at h

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  by_contra h
  specialize h 0 (le_refl _) 1 (by simp)
  unfold Rat.Close at h
  norm_num at h

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

lemma Rat.eventuallyClose_symm {ε: ℚ} {a b: Sequence} :
    ε.EventuallyClose a b ↔ ε.EventuallyClose b a := by
      peel with N
      exact closeSeq_symm

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
  ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
    simp [eventuallyClose_def, closeSeq_def]
    refine ⟨?_, ?_⟩
    · rintro ⟨N, hN⟩
      refine ⟨N.toNat, fun n hn => ?_⟩
      replace hn : N ≤ n := Int.toNat_le.mp hn
      specialize hN n (Int.natCast_nonneg _) hn (Int.natCast_nonneg _) hn
      simpa [hn] using hN
    · rintro ⟨N, hN⟩
      refine ⟨N, fun n hn hNn _ _ => ?_⟩
      lift n to ℕ using hn
      specialize hN n (Int.ofNat_le.mp hNn)
      simpa [hNn] using hN

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
    by_contra h
    specialize h 0 (le_refl _) (le_refl _)
    unfold Rat.Close at h
    conv at h =>
      lhs
      norm_num
    norm_num at h

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
    refine ⟨1, ?_⟩
    intro n hn hn'; clear hn'
    simp at hn
    lift n to ℕ; omega
    unfold Rat.Close
    simp [hn]
    calc (_: ℚ)
    _ = |2 * 10 ^ (-(n: ℤ) - 1)| := by ring_nf
    _ = |2 / 10 ^ (n + 1)| := by 
      rw [← neg_add', ← Int.natCast_add_one, zpow_neg, zpow_natCast]
      rfl
    _ = |2| / |10 ^ (n + 1)| := abs_div _ _
    _ = 2 / 10 ^ (n + 1) := by 
      rw [abs_of_nonneg (by norm_num), abs_of_nonneg <| Rat.pow_nonneg rfl]
    _ ≤ 2 / 10 ^ 2 := by
      refine div_le_div_iff_of_pos_left ?_ ?_ ?_ |>.mpr ?_
      · norm_num
      · exact Rat.pow_pos rfl
      · norm_num
      refine (pow_le_pow_iff_right₀ rfl).mpr ?_
      omega
    _ ≤ 0.1 := by norm_num

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
    refine ⟨2, ?_⟩
    intro n hn hn'; clear hn'
    simp at hn
    lift n to ℕ; omega
    unfold Rat.Close
    simp [hn]
    calc (_: ℚ)
    _ = |2 * 10 ^ (-(n: ℤ) - 1)| := by ring_nf
    _ = |2 / 10 ^ (n + 1)| := by 
      rw [← neg_add', ← Int.natCast_add_one, zpow_neg, zpow_natCast]
      rfl
    _ = |2| / |10 ^ (n + 1)| := abs_div _ _
    _ = 2 / 10 ^ (n + 1) := by 
      rw [abs_of_nonneg (by norm_num), abs_of_nonneg <| Rat.pow_nonneg rfl]
    _ ≤ 2 / 10 ^ 3 := by
      refine div_le_div_iff_of_pos_left ?_ ?_ ?_ |>.mpr ?_
      · norm_num
      · exact Rat.pow_pos rfl
      · norm_num
      refine (pow_le_pow_iff_right₀ rfl).mpr ?_
      omega
    _ ≤ 0.01 := by norm_num

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

lemma Sequence.equiv_symm {a b: ℕ → ℚ} :
  Equiv a b ↔ Equiv b a := by
    peel with ε hε
    exact Rat.eventuallyClose_symm

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  peel with ε hε
  exact Rat.eventuallyClose_iff ε a b

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
  (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
    revert a b;
    suffices ∀{a b}, Equiv a b → (a:Sequence).IsCauchy → (b:Sequence).IsCauchy by
      intro a b hab
      constructor
      · exact this hab
      · exact this (equiv_symm.mp hab)
    intro a b hab ha
    replace hab := equiv_iff _ _ |>.mp hab
    replace ha := IsCauchy.coe _ |>.mp ha
    refine IsCauchy.coe _ |>.mpr ?_
    intro ε hε
    replace ⟨N, ha⟩ := ha (ε/3) (by positivity)
    replace ⟨M, hab⟩ := hab (ε/3) (by positivity)
    use max N M
    intro j hj k hk
    specialize ha j (le_of_max_le_left hj) k (le_of_max_le_left hk)
    replace hj := hab j (le_of_max_le_right hj)
    replace hk := hab k (le_of_max_le_right hk)
    clear hab
    calc |b j - b k|
    _ = |-b j + b k| := by rw [abs_sub_comm, sub_eq_neg_add]
    _ = |(a j - b j) - (a k - b k) - (a j - a k)| := by ring_nf
    _ ≤ |a j - b j| + |a k - b k| + |a j - a k| := by
      refine le_trans (abs_sub _ _) ?_
      refine add_le_add_left ?_ _
      exact abs_sub _ _
    _ ≤ _ + _ + _ := add_le_add (add_le_add hj hk) ha
    _ = ε := add_thirds ε

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
  (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
    revert a b
    suffices ∀{a b: ℕ → ℚ}, ε.EventuallyClose a b → (a:Sequence).IsBounded → (b:Sequence).IsBounded by
      intro a b hab
      constructor
      · exact this hab
      · exact this (Rat.eventuallyClose_symm.mp hab)
    intro a b hab ha
    replace hab := Rat.eventuallyClose_iff _ _ _ |>.mp hab
    rw [isBounded_iff] at ha ⊢
    obtain ⟨N, hN⟩ := hab
    obtain ⟨M, M_pos, hM⟩ := ha
    obtain ⟨M', M'_pos, hM'⟩ := IsBounded.finite (n := N) (b ·)
    refine ⟨max M' (ε + M), by positivity, fun n => ?_⟩
    by_cases hn: n < N
    · exact le_trans (hM' ⟨n, hn⟩) (le_max_left _ _)
    replace hn := not_lt.mp hn
    calc |b n|
    _ = |-b n| := abs_neg _ |>.symm
    _ = |a n - b n - a n| := by ring_nf
    _ ≤ |a n - b n| + |a n| := abs_sub _ _
    _ ≤ ε + M := add_le_add (hN _ hn) (hM _)
    _ ≤ _ := le_max_right _ _

end Chapter5
