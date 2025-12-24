import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a: Sequence).seq
  vanish := (a: Sequence).vanish
  zero := rfl
  cauchy := ha

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by
    rw [equiv_iff] at hab hbc ⊢
    intro ε εpos
    obtain ⟨N, hN⟩ := hab (ε/2) (by positivity); clear hab
    obtain ⟨M, hM⟩ := hbc (ε/2) (by positivity); clear hbc
    refine ⟨max N M, fun n hn => ?_⟩
    calc
    _ = |a n - b n + (b n - c n)| := by ring_nf
    _ ≤ |a n - b n| + |b n - c n| := abs_add_le _ _
    _ ≤ _ + _ := add_le_add 
      (hN _ (le_trans (le_max_left _ _) hn))
      (hM _ (le_trans (le_max_right _ _) hn))
    _ = _ := add_halves _

theorem Sequence.equiv_refl (x:ℕ → ℚ) : Equiv x x := 
  equiv_iff _ _ |>.mpr fun ε εpos => ⟨0, fun n hn => by
    rw [sub_self, abs_zero]
    exact le_of_lt εpos
  ⟩

open Sequence (equiv_refl equiv_symm equiv_trans) in
/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
    refl x := equiv_refl x
    symm := by
      intro x y hxy
      exact equiv_symm.mp hxy
    trans := equiv_trans
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  rw [IsCauchy.coe]
  intro ε εpos
  use 0
  intro n _ m _
  rw [Section_4_3.dist, sub_self, abs_zero]
  exact le_of_lt εpos

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.
  This requires Classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x; intro a; use (a:ℕ → ℚ)
  have : ((a:ℕ → ℚ):Sequence) = a.toSequence := CauchySequence.coe_to_sequence a
  rw [this, LIM_def (by convert a.cauchy)]
  refine ⟨ a.cauchy, ?_ ⟩
  congr
  ext n
  simp
  replace := congr($this n)
  simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/-- Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j (le_trans (le_max_left ..) hj) k (le_trans (le_max_left ..) hk)
  have h2 := hb j (le_trans (le_max_right ..) hj) k (le_trans (le_max_right ..) hk)
  /- rw [Pi.add_apply, Pi.add_apply] -/
  /- ring_nf -/
  /- refine le_trans (abs_add_le _ _) ?_ -/
  /- refine le_trans (add_le_add h1 h2) ?_ -/
  /- exact add_halves _ -/
  calc
  _ = |a j + b j - (a k + b k)| := by rw [Pi.add_apply, Pi.add_apply]
  _ = |a j - a k + (b j - b k)| := by ring_nf
  _ ≤ |a j - a k| + |b j - b k| := abs_add_le _ _
  _ ≤ ε/2 + ε/2 := add_le_add h1 h2
  _ = ε := add_halves _

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_iff] at *
  peel 2 haa' with ε hε haa'
  choose N haa' using haa'; use N
  peel 2 haa' with n hN haa'
  rw [Pi.add_apply, Pi.add_apply]
  ring_nf
  exact haa'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
  Equiv (a + b) (a + b') := by 
    rw [add_comm _ b, add_comm _ b']
    exact add_equiv_left a hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' haa' hbb'
      show LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      all_goals try apply Sequence.IsCauchy.add 
        <;> rw [CauchySequence.coe_to_sequence] 
        <;> convert @CauchySequence.cauchy ?_
      exact Sequence.equiv_trans 
        (Sequence.add_equiv_left _ haa') 
        (Sequence.add_equiv_right _ hbb')
    )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  obtain ha' := isBounded_of_isCauchy ha
  obtain hb' := isBounded_of_isCauchy hb
  rw [isBounded_iff] at *
  rw [IsCauchy.coe] at *
  intro ε εpos
  replace ⟨Ma, Ma_pos, ha'⟩ := ha'
  replace ⟨Mb, Mb_pos, hb'⟩ := hb'
  simp_rw [Pi.mul_apply]
  by_cases hMa0: Ma = 0
  · refine ⟨0, fun n hn m hm => ?_⟩
    replace hMa (n) := abs_nonpos_iff.mp (hMa0 ▸ ha' n)
    calc |a n * b n - a m * b m|
      _ = |0 * b n - 0 * b m| := by rw [hMa, hMa]
      _ = 0 := by simp
      _ ≤ ε := le_of_lt εpos
  by_cases hMb0: Mb = 0
  · refine ⟨0, fun n hn m hm => ?_⟩
    replace hMb (n) := abs_nonpos_iff.mp (hMb0 ▸ hb' n)
    calc |a n * b n - a m * b m|
      _ = |a n * 0 - a m * 0| := by rw [hMb, hMb]
      _ = 0 := by simp
      _ ≤ ε := le_of_lt εpos
  replace Ma_pos := lt_of_le_of_ne' Ma_pos hMa0
  replace Mb_pos := lt_of_le_of_ne' Mb_pos hMb0
  replace ⟨Na, ha⟩ := ha (ε / 2 / Mb) (by positivity)
  replace ⟨Nb, hb⟩ := hb (ε / 2 / Ma) (by positivity)
  refine ⟨max Na Nb, fun n hn m hm => ?_⟩
  calc
  _ = |(a n - a m) * b n + a m * (b n - b m)| := by ring_nf
  _ ≤ |(a n - a m) * b n| + |a m * (b n - b m)| := abs_add_le _ _
  _ = |a n - a m| * |b n| + |b n - b m| * |a m| := by rw [abs_mul, abs_mul, mul_comm |a m| _]
  _ ≤ (ε / 2 / Mb) * Mb + (ε / 2 / Ma) * Ma := by
    refine add_le_add (mul_le_mul ?_ (hb' _) ?_ ?_) (mul_le_mul ?_ (ha' _) ?_ ?_) <;> try positivity
    · exact ha n (le_trans (le_max_left ..) hn) m (le_trans (le_max_left ..) hm)
    · exact hb n (le_trans (le_max_right ..) hn) m (le_trans (le_max_right ..) hm)
  _ = ε / 2 + ε / 2 := by conv =>
    lhs
    congr <;> rw [Rat.div_mul_cancel (by positivity)]
  _ = ε := add_halves _

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
    replace ⟨M, M_pos, hb⟩ := isBounded_of_isCauchy hb |> isBounded_iff.mp
    rw [equiv_iff] at *
    intro ε εpos
    simp_rw [Pi.mul_apply]
    by_cases hM0: M = 0
    · refine ⟨0, fun n hn => ?_⟩
      replace hMb (n) := abs_nonpos_iff.mp (hM0 ▸ hb n)
      simp [hMb, le_of_lt εpos]
    replace ⟨N, haa'⟩ := haa' (ε / M) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    calc
    _ = |a n - a' n| * |b n| := by rw [← sub_mul, abs_mul]
    _ ≤ (ε / M) * M := mul_le_mul (haa' _ hn) (hb _) (by positivity) (by positivity)
    _ = ε := Rat.div_mul_cancel hM0

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv
  {a b a' b':ℕ → ℚ}
  (ha : (a:Sequence).IsCauchy)
  (hb' : (b':Sequence).IsCauchy)
  (haa': Equiv a a')
  (hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
    equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      all_goals try apply Sequence.IsCauchy.mul 
        <;> rw [CauchySequence.coe_to_sequence] 
        <;> convert @CauchySequence.cauchy ?_
      exact Sequence.mul_equiv 
        (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) 
        (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
    )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

example {a b: ℚ} (hab: a < b): ∃n, n > 0 ∧ a + n = b := by exact exists_pos_add_of_lt' hab

open Sequence (IsCauchy equiv_refl equiv_iff) in
/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  simp_rw [ratCast_def, LIM_eq_LIM (IsCauchy.const q) (IsCauchy.const r)]
  refine ⟨fun h => ?_, fun h => h ▸ equiv_refl _⟩
  rw [Section_4_3.eq_if_close]
  rw [equiv_iff] at h
  peel 2 h with ε εpos h
  replace ⟨N, h⟩ := h
  exact h N (le_refl _)

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

lemma Real.ofNat_def' (n: ℕ) : (ofNat(n): Real) = ((n: ℚ): Real) := rfl
lemma Real.ofNat_def (n: ℕ) : (ofNat(n): Real) = LIM (fun _ => (n: ℚ)) := by
  rw [ofNat_def', ratCast_def]

lemma Real.natCast_def' (n: ℕ) : (n: Real) = ((n: ℚ): Real) := rfl
lemma Real.natCast_def (n: ℕ) : (n: Real) = LIM (fun _ => (n: ℚ)) := by
  rw [natCast_def', ratCast_def]

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

lemma Real.intCast_def' (n: ℤ) : (n: Real) = ((n: ℚ): Real) := rfl
lemma Real.intCast_def (n: ℤ) : (n: Real) = LIM (fun _ => (n: ℚ)) := by
  rw [intCast_def', ratCast_def]

open Sequence (IsCauchy) in
/-- ratCast distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  simp_rw [ratCast_def, LIM_add (IsCauchy.const a) (IsCauchy.const b)]
  rfl

open Sequence (IsCauchy) in
/-- ratCast distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  simp_rw [ratCast_def, LIM_mul (IsCauchy.const a) (IsCauchy.const b)]
  rfl

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

theorem neg_def (x: Real) : (-x) = ((-1:ℚ):Real) * x := rfl

/-- ratCast commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  rw [neg_def, ratCast_mul, neg_one_mul]

open Sequence (IsCauchy) in
/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by
  rw [neg_def, ratCast_def, LIM_mul (IsCauchy.const _) ha]
  congr
  funext n
  rw [Pi.mul_apply, Pi.neg_apply, neg_one_mul]

theorem Sequence.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
  ((-a:ℕ → ℚ):Sequence).IsCauchy := by
    rw [IsCauchy.coe] at *
    peel 7 ha with ε εpos N n hn m hm ha
    simpa [Section_4_3.dist, neg_add_eq_sub, abs_sub_comm] using ha

open Sequence (IsCauchy) in
/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
  AddGroup.ofLeftAxioms 
    (fun a b c => by
      obtain ⟨a, ha, rfl⟩ := eq_lim a
      obtain ⟨b, hb, rfl⟩ := eq_lim b
      obtain ⟨c, hc, rfl⟩ := eq_lim c
      rw [LIM_add ha hb, LIM_add ?_ hc, LIM_add hb hc, LIM_add ha ?_, add_assoc]
      · exact IsCauchy.add hb hc
      · exact IsCauchy.add ha hb
    ) 
    (fun a => by 
      obtain ⟨a, ha, rfl⟩ := eq_lim a
      rw [Real.ofNat_def, LIM_add (IsCauchy.const _) ha]
      congr
      funext n
      simp only [CharP.cast_eq_zero, Pi.add_apply, zero_add]
    ) 
    (fun a => by
      obtain ⟨a, ha, rfl⟩ := eq_lim a
      rw [neg_LIM _ ha, LIM_add (IsCauchy.neg _ ha) ha, Real.ofNat_def]
      congr
      funext n
      simp
    )

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  ((a-b:ℕ → ℚ):Sequence).IsCauchy := by
    rw [IsCauchy.coe] at *
    intro ε hε
    choose N1 ha using ha _ (half_pos hε)
    choose N2 hb using hb _ (half_pos hε)
    use max N1 N2
    intro j hj k hk
    have h1 := ha j (le_trans (le_max_left ..) hj) k (le_trans (le_max_left ..) hk)
    have h2 := hb j (le_trans (le_max_right ..) hj) k (le_trans (le_max_right ..) hk)
    calc
    _ = |a j - b j - (a k - b k)| := by rw [Pi.sub_apply, Pi.sub_apply]
    _ = |a j - a k - (b j - b k)| := by ring_nf
    _ ≤ |a j - a k| + |b j - b k| := abs_sub _ _
    _ ≤ ε/2 + ε/2 := add_le_add h1 h2
    _ = ε := add_halves _


open Sequence (IsCauchy) in
/-- LIM distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by
    rw [sub_eq_add_neg, neg_LIM _ hb, LIM_add ha (IsCauchy.neg _ hb), (_root_.sub_eq_add_neg _ _).symm]

open Sequence.IsCauchy (const) in
/-- ratCast distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by
  simp_rw [ratCast_def, LIM_sub (const _) (const _)]
  rfl

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := fun x y => by
    obtain ⟨x, hx, rfl⟩ := eq_lim x
    obtain ⟨y, hy, rfl⟩ := eq_lim y
    rw [LIM_add hx hy, LIM_add hy hx, add_comm]


open Sequence.IsCauchy (mul const) in
/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := fun x y => by
    obtain ⟨x, hx, rfl⟩ := eq_lim x
    obtain ⟨y, hy, rfl⟩ := eq_lim y
    rw [LIM_mul hx hy, LIM_mul hy hx, mul_comm]
  mul_assoc := fun x y z => by
    obtain ⟨x, hx, rfl⟩ := eq_lim x
    obtain ⟨y, hy, rfl⟩ := eq_lim y
    obtain ⟨z, hz, rfl⟩ := eq_lim z
    rw [LIM_mul hx hy, LIM_mul (mul hx hy) hz, LIM_mul hy hz, LIM_mul hx (mul hy hz), mul_assoc]
  one_mul := fun x => by
    obtain ⟨x, hx, rfl⟩ := eq_lim x
    rw [ofNat_def, LIM_mul (const _) hx]
    congr
    funext n
    simp
  mul_one := fun x => by
    obtain ⟨x, hx, rfl⟩ := eq_lim x
    rw [ofNat_def, LIM_mul hx (const _)]
    congr
    funext n
    simp

open Sequence.IsCauchy (add mul const) in
/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := fun x y z => by
    obtain ⟨x, hx, rfl⟩ := eq_lim x
    obtain ⟨y, hy, rfl⟩ := eq_lim y
    obtain ⟨z, hz, rfl⟩ := eq_lim z
    rw [
      LIM_add hy hz, LIM_mul hx (add hy hz), 
      LIM_mul hx hy, LIM_mul hx hz, LIM_add (mul hx hy) (mul hx hz),
      left_distrib
    ]
  right_distrib := fun x y z => by
    obtain ⟨x, hx, rfl⟩ := eq_lim x
    obtain ⟨y, hy, rfl⟩ := eq_lim y
    obtain ⟨z, hz, rfl⟩ := eq_lim z
    rw [
      LIM_add hx hy, LIM_mul (add hx hy) hz, 
      LIM_mul hx hz, LIM_mul hy hz, LIM_add (mul hx hz) (mul hy hz),
      right_distrib
    ]
  zero_mul := fun x => by
    obtain ⟨x, hx, rfl⟩ := eq_lim x
    rw [ofNat_def, LIM_mul (const _) hx]
    congr
    funext n
    simp
  mul_zero := fun x => by
    obtain ⟨x, hx, rfl⟩ := eq_lim x
    rw [ofNat_def, LIM_mul hx (const _)]
    congr
    funext n
    simp
  natCast_succ := fun n => by
    rw [show NatCast.natCast = Nat.cast by rfl, natCast_def, natCast_def, ofNat_def, LIM_add (const _) (const _)]
    congr
    funext n
    simp
  intCast_negSucc := fun n => by
    rw [
      show IntCast.intCast = Int.cast by rfl, 
      intCast_def, Int.negSucc_eq, natCast_def, neg_LIM _ (const _)]
    rfl

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := rfl
  map_one' := rfl
  map_add' := (ratCast_add · · |>.symm)
  map_mul' := (ratCast_mul · · |>.symm)

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by
  rw [bounded_away_zero_def]
  push_neg
  intro c hc
  choose n hn using exists_pow_lt_of_lt_one hc (y := 1 / 10) (by norm_num)
  use n
  calc (_: ℚ)
  _ = 10 ^ (-(n: ℤ) - 1) := by rw [abs_of_pos <| Rat.zpow_pos rfl] 
  _ = 10 ^ (-(n + 1: ℤ)) := by simp [neg_add_eq_sub]
  _ = (1 / 10) ^ n / 10 := by
    rw [zpow_neg, Rat.zpow_add_one (by norm_num)]
    simp [mul_comm, Rat.div_def]
  _ < c / 10 := div_lt_div_of_pos_right hn (by norm_num)
  _ < c := div_lt_self hc (by norm_num)

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by
  rw [bounded_away_zero_def]
  push_neg
  intro c hc
  use 0
  simp [hc]

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

open Sequence (isBounded_iff) in
/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by
  rw [isBounded_iff]
  push_neg
  intro M hM
  choose n _ hn using exists_nat_pow_near 
    (le_add_of_nonneg_left hM) 
    (show 1 < 10 by norm_num)
  use n
  calc M
  _ < M + 1 := lt_add_one _
  _ < 10 ^ (n + 1) := hn
  _ ≤ |10 ^ (n + 1)| := le_abs_self _


/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM.zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  choose ε hε hx using hx
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  choose n₀ hn₀ hx using hx N
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by
    intro j hj
    specialize hb' n₀ hn₀ j hj
    contrapose! hx with hbj
    calc |b n₀|
    _ = |b n₀ - b j + b j| := by ring_nf
    _ ≤ |b n₀ - b j| + |b j| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hb' (le_of_lt hbj)
    _ = ε := add_halves _
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then ε/2 else b n
  have not_hard : Sequence.Equiv a b := by
    rw [Sequence.equiv_iff]
    intro ε' ε'pos
    refine ⟨n₀, fun n hn => ?_⟩
    simpa [a, not_lt.mpr hn] using le_of_lt ε'pos
  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  intro n; by_cases hn: n < n₀ <;> simp [a, hn, le_abs_self _]
  grind

open Sequence (equiv_iff) in
open Sequence.IsCauchy (const) in
/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) : LIM a ≠ 0 := by
    rw [bounded_away_zero_def] at ha
    by_contra h
    rw [ofNat_def, LIM_eq_LIM ha_cauchy (const _), equiv_iff] at h
    simp at h
    replace ⟨ε, εpos, ha⟩ := ha
    replace ⟨N, h⟩ := h (ε/2) (by positivity)
    specialize ha N 
    specialize h N (le_refl _)
    replace h := le_trans ha h
    refine (not_le.mpr ?_) h
    exact div_two_lt_of_pos εpos

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc |a⁻¹ n - a⁻¹ m|
    _ = |(a m - a n) / (a n * a m)| := by 
      rw [Pi.inv_apply, Pi.inv_apply, inv_sub_inv (ha' _) (ha' _)]
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> exact ha _
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := div_le_div_of_nonneg_right ha_cauchy (by positivity)
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  exact claim2.symm.trans claim1

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  have hx : LIM a ≠ 0 := lim_of_boundedAwayZero h hc
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [instInv, hx]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  obtain ⟨x, hx_cauchy, hx, rfl⟩ := boundedAwayZero_of_nonzero hx; clear hx
  rw [
    inv_def hx hx_cauchy, 
    LIM_mul hx_cauchy (inv_isCauchy_of_boundedAwayZero hx hx_cauchy), 
    ofNat_def
  ]
  congr
  funext n
  simp [nonzero_of_boundedAwayZero hx n]

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm, self_mul_inv hx]

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

open Sequence (equiv_iff) in
open Sequence.IsCauchy (const) in
noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by
    use 0, 1
    simp_rw [ofNat_def]
    by_contra! h
    rw [LIM_eq_LIM (const _) (const _), equiv_iff] at h
    contrapose! h
    use 1 / 2
    norm_num
    exact fun N => ⟨N, le_refl _⟩
  mul_inv_cancel x := self_mul_inv
  inv_zero := inv_zero
  ratCast_def q := by
    rw [ratCast_def, intCast_def, natCast_def', div_eq, inv_ratCast, ratCast_def, 
      LIM_mul (const _) (const _)
    ]
    congr; funext n; simp
    exact Rat.num_div_den _ |>.symm
  qsmul := _
  nnqsmul := _

open Sequence (isBounded_of_isCauchy boundedBy_iff equiv_iff) in
open Sequence.IsCauchy (mul) in
theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by
  -- exact _root_.mul_right_cancel₀ hz h
  obtain ⟨x, hx, rfl⟩ := eq_lim x
  obtain ⟨y, hy, rfl⟩ := eq_lim y
  obtain ⟨z, hz, hz', rfl⟩ := boundedAwayZero_of_nonzero hz; clear hz
  rw [LIM_mul hx hz, LIM_mul hy hz,
    LIM_eq_LIM (mul hx hz) (mul hy hz), Sequence.equiv_iff
  ] at h
  rw [LIM_eq_LIM hx hy, equiv_iff]
  have hz_nonzero := nonzero_of_boundedAwayZero hz'
  obtain ⟨c, cpos, hz'⟩ := hz'
  intro ε εpos
  obtain ⟨N, h⟩ := h (ε * c) (by positivity)
  refine ⟨N, fun n hn => ?_⟩ 
  specialize h n hn
  rw [Pi.mul_apply, Pi.mul_apply] at h
  calc |x n - y n|
  _ = |x n - y n| * |z n| / |z n| := by
    nth_rw 1 [← Rat.mul_div_cancel (a := |_|) (b := |z n|) 
      (abs_ne_zero.mpr <| hz_nonzero n)]
  _ = |x n * z n - y n * z n| / |z n| := by rw [← abs_mul, sub_mul]
  _ ≤ ε * c / c := div_le_div₀ (by positivity) h cpos (hz' n)
  _ = ε := Rat.mul_div_cancel (ne_of_lt cpos).symm

theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  simp [exists_pair_ne]

open Sequence (isBounded_of_eventuallyClose) in
/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
  (b:Sequence).IsBounded :=
    isBounded_of_eventuallyClose (hab _ zero_lt_one) |>.mp ha

/--
  Same as `Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

open Sequence.IsCauchy (harmonic' const) in
/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by
  rw [ofNat_def, LIM_eq_LIM harmonic' (const _), Sequence.equiv_iff]
  intro ε εpos
  choose N hN using exists_nat_ge (ε⁻¹)
  have Npos : 0 < (N: ℚ) := by
    refine lt_of_lt_of_le ?_ hN
    exact Rat.inv_pos.mpr εpos
  refine ⟨N, fun n hn => ?_⟩
  calc (|1 / (↑n + 1) - 0|: ℚ)
  _ = |↑n + 1|⁻¹ := by rw [sub_zero, one_div, abs_inv]
  _ ≤ (↑N)⁻¹ := by
    refine inv_anti₀ Npos ?_
    norm_cast
    exact le_trans hn (Nat.le_succ _)
  _ ≤ ε := (inv_le_comm₀ εpos Npos).mp hN

end Chapter5
