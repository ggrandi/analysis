import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, Section 6.3: Suprema and infima of sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences.

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

theorem Sequence.sup_eq (a: Sequence) : a.sup = sSup (Real.toEReal '' { x | ∃ n ≥ a.m, x = a n }) := by
  refine congrArg (sSup ·) ?_
  simp [Set.ext_iff, eq_comm]

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

theorem Sequence.inf_eq (a: Sequence) : a.inf = sInf (Real.toEReal '' { x | ∃ n ≥ a.m, x = a n }) := by
  refine congrArg (sInf ·) ?_
  simp [Set.ext_iff, eq_comm]

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by
  simp [Sequence.sup]
  refine le_antisymm (sSup_le ?_) (le_sSup ⟨1, zero_le_one, by simp⟩)
  rintro _ ⟨n, hn, rfl⟩
  lift n to ℕ using hn
  rw [← EReal.coe_one, EReal.coe_le_coe_iff, if_pos (Nat.cast_nonneg n), Int.toNat_natCast]
  suffices (-1: ℝ)^(n+1) = 1 ∨ (-1: ℝ)^(n+1) = -1 from this.elim
    (·.symm ▸ le_refl _)
    (·.symm ▸ by norm_num)
  induction n
  case zero => simp
  case succ n ih =>
    conv => congr <;> rw [pow_succ]
    obtain (ih|ih) := ih
    · rw [ih, one_mul]; exact Or.inr rfl
    · rw [ih, neg_one_mul, neg_neg]; exact Or.inl rfl


/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by
  simp [Sequence.inf]
  refine le_antisymm (sInf_le ⟨0, le_refl _, by simp⟩) (le_sInf ?_)
  rintro _ ⟨n, hn, rfl⟩
  lift n to ℕ using hn
  rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_le_coe_iff, if_pos (Nat.cast_nonneg n), Int.toNat_natCast]
  suffices (-1: ℝ)^(n+1) = 1 ∨ (-1: ℝ)^(n+1) = -1 from this.elim
    (·.symm ▸ by linarith)
    (·.symm ▸ le_refl _)
  induction n
  case zero => simp
  case succ n ih =>
    conv => congr <;> rw [pow_succ]
    obtain (ih|ih) := ih
    · rw [ih, one_mul]; exact Or.inr rfl
    · rw [ih, neg_one_mul, neg_neg]; exact Or.inl rfl

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by
  simp [Sequence.sup]
  refine le_antisymm (sSup_le ?_) (le_sSup_iff.mpr ?_)
  · rintro _ ⟨n, hn, rfl⟩
    lift n to ℕ using hn
    rw [← EReal.coe_one, EReal.coe_le_coe_iff, if_pos (Nat.cast_nonneg n), Int.toNat_natCast]
    refine inv_le_one_of_one_le₀ ?_
    exact le_add_of_nonneg_left <| Nat.cast_nonneg _
  rintro b hb
  by_contra! hb'
  sorry

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by
  simp [Sequence.inf]
  refine le_antisymm (?_) (le_sInf ?_)
  · refine sInf_le_iff.mpr ?_
    rintro b hb
    by_contra! hb'
    sorry
  rintro _ ⟨n, hn, rfl⟩
  rw [if_pos hn]
  simpa using Nat.cast_add_one_pos _ |>.le

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by
  rw [Sequence.sup_eq]
  refine EReal.sup_of_unbounded_nonempty ?_ ?_
  · by_contra! hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨n, hn⟩ := exists_nat_gt y
    refine hn.trans (lt_add_one _) |>.not_ge ?_
    exact hy ⟨n, Nat.cast_nonneg _, rfl⟩
  exact ⟨1, 0, le_refl _, by grind⟩
  

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by
  refine le_antisymm ?_ ?_
  · exact sInf_le ⟨0, le_refl _, by simp⟩
  refine le_sInf ?_
  rintro _ ⟨n, hn, rfl⟩
  simp [hn]
  sorry


abbrev Sequence.BddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a:Sequence) : Prop := ∃ M, a.BddAboveBy M

theorem Sequence.BddAbove_iff {a:Sequence}  : a.BddAbove ↔ ∃ M, ∀ n ≥ a.m, a n ≤ M := Iff.rfl

abbrev Sequence.BddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a:Sequence) : Prop := ∃ M, a.BddBelowBy M

theorem Sequence.BddBelow_iff {a:Sequence}  : a.BddBelow ↔ ∃ M, ∀ n ≥ a.m, M ≤ a n := Iff.rfl

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by
  simp_rw [isBounded_iff, BddAbove_iff, BddBelow_iff, abs_le]
  constructor
  · rintro ⟨M, Mnonneg, hM⟩
    refine ⟨⟨M, fun n _ => hM n |>.2⟩, ⟨-M, fun n _ => hM n |>.1⟩⟩
  sorry


theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by sorry

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by sorry

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := by sorry

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by sorry

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by sorry

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by sorry

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by sorry

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by sorry

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).IsMonotone := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).BddAboveBy 4 := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent := by sorry

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by sorry

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone := sorry
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by sorry
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by sorry

end Chapter6
