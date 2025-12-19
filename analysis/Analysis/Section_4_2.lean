import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal quotients `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal quotients without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of ℕ and ℤ.

- Equivalence with the Mathlib rationals `_root_.Rat` (or `ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers `ℕ` and integers `ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := fun a => by simp
    symm := by
      intro ⟨x1, x2, hx2⟩ ⟨y1, y2, hy2⟩ h
      simp at ⊢ h
      exact h.symm
    trans := by
      intro ⟨x1, x2, hx2⟩ ⟨y1, y2, hy2⟩ ⟨z1, z2, hz2⟩ hxy hyz
      simp at ⊢ hxy hyz
      rw [← Int.mul_eq_mul_right_iff hy2]
      conv => 
        rw [Int.mul_right_comm, hxy]
        rhs
        rw [Int.mul_right_comm, ← hyz]
      ring
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [Quotient.eq, hb, hd, PreRat.instSetoid]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

/--
  Decidability of equality. Hint: modify the proof of `DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the `Quotient` API.
-/
instance Rat.decidableEq : DecidableEq Rat :=
  fun x y => Quotient.recOnSubsingleton₂ x y (fun _ _ => Quotient.eq.eq ▸ decEq _ _)

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [eq]
    calc
      _ = (a*b')*d*d' + b*b'*(c*d') := by ring
      _ = (a'*b)*d*d' + b*b'*(c'*d) := by rw [h3, h4]
      _ = _ := by ring
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro a b c d hac had
    simp [HasEquiv.Equiv, PreRat.instSetoid] at hac had
    rw [Rat.eq, ← mul_assoc, mul_right_comm a.numerator, hac, mul_assoc, had]
    ring
    · exact (mul_eq_zero.mp · |>.elim a.nonzero b.nonzero)
    · exact (mul_eq_zero.mp · |>.elim c.nonzero d.nonzero)
  )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro a b h
    simp [HasEquiv.Equiv, PreRat.instSetoid] at h
    rw [Rat.eq _ _ a.nonzero b.nonzero, Int.neg_mul, h]
    ring
  )

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

theorem Rat.neg_eq' (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = a // (-b) := by
  simp [hb, neg_eq, eq]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.intCast_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.natCast_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.ofNat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  simp [Rat.natCast_eq, ofNat_eq, add_eq]

/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  simp [Rat.intCast_eq, add_eq]

/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  simp [Rat.intCast_eq, mul_eq]

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro x y h
  simpa [Rat.intCast_eq, eq] using h

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro x y h
    simp [HasEquiv.Equiv, PreRat.instSetoid] at h
    simp [Quotient.eq]
    split_ifs with hx hy hy
    <;> simp [PreRat.instSetoid]
    · simp [hx] at h
      exact h.elim hy x.nonzero |>.elim
    · simp [hy] at h
      exact h.elim hx y.nonzero |>.elim
    · ring_nf at h ⊢
      exact h.symm
)

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms 
  (fun x y z => by
    -- this proof is written to follow the structure of the original text.
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
    have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
    have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
    rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
        add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
    ring
  )
  (fun x => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    simp [hx2, ofNat_eq, add_eq]
  ) 
  (fun x => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    simp [ofNat_eq, neg_eq, add_eq, Rat.eq, hx2]
    ring
  )

example (a b: ℤ) (ha: a ≠ 0) (hb: b ≠ 0): a * b ≠ 0 := by exact Int.mul_ne_zero ha hb

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := fun x y => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, hy2, rfl⟩ := eq_diff y
    simp [hx2, hy2, add_eq, Rat.eq]
    ring


/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := fun x y => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, hy2, rfl⟩ := eq_diff y
    simp [hx2, hy2, mul_eq, Rat.eq]
    ring
  mul_assoc := fun x y z => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, hy2, rfl⟩ := eq_diff y
    obtain ⟨z1, z2, hz2, rfl⟩ := eq_diff z
    simp [hx2, hy2, hz2, mul_eq, Rat.eq]
    ring
  one_mul := fun x => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    simp [hx2, ofNat_eq, mul_eq]
  mul_one := fun x => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    simp [hx2, ofNat_eq, mul_eq]

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := fun x y z => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, hy2, rfl⟩ := eq_diff y
    obtain ⟨z1, z2, hz2, rfl⟩ := eq_diff z
    simp [hx2, hy2, hz2, mul_eq, add_eq, Rat.eq]
    ring
  right_distrib := fun x y z => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, hy2, rfl⟩ := eq_diff y
    obtain ⟨z1, z2, hz2, rfl⟩ := eq_diff z
    simp [hx2, hy2, hz2, mul_eq, add_eq, Rat.eq]
    ring
  zero_mul := fun x => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    simp [hx2, ofNat_eq, mul_eq, Rat.eq]
  mul_zero := fun x => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    simp [hx2, ofNat_eq, mul_eq, Rat.eq]
  mul_assoc := fun x y z => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, hy2, rfl⟩ := eq_diff y
    obtain ⟨z1, z2, hz2, rfl⟩ := eq_diff z
    simp [hx2, hy2, hz2, mul_eq, Rat.eq]
    ring
  -- Usually CommRing will generate a natCast instance and a proof for this.
  -- However, we are using a custom natCast for which `natCast_succ` cannot
  -- be proven automatically by `rfl`. Luckily we have proven it already.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_eq (a:ℚ) : (a:Rat) = a.num // a.den := rfl

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro x y h
  simpa [ratCast_eq, Rat.eq, Rat.eq_iff_mul_eq_mul] using h

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by
    refine ⟨0, 1, ?_⟩
    by_contra h
    simp [ofNat_eq, eq] at h
  mul_inv_cancel := fun x h => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    simp_all [ofNat_eq, eq, inv_eq, mul_eq, mul_comm]
  inv_zero := rfl
  ratCast_def := fun q => by simp [ratCast_eq, intCast_eq, natCast_eq, div_eq, inv_eq, mul_eq]
  qsmul := (Rat.cast · * ·)
  nnqsmul := _

open Rat in
example : (3//4) / (5//6) = 9 // 10 := by
  simp [div_eq, inv_eq, mul_eq, eq]

/-- Definition of subtraction -/
theorem Rat.sub_eq (a b:Rat) : a - b = a + (-b) := by rfl

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := Int.cast_add
  map_mul' := Int.cast_mul

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

theorem Rat.add_Pos {p q : Rat} (hp: p.isPos) (hq: q.isPos) : (p + q).isPos := by
  simp [isPos] at hp hq ⊢
  obtain ⟨p1, hp1, p2, hp2, rfl⟩ := hp
  obtain ⟨q1, hq1, q2, hq2, rfl⟩ := hq
  refine ⟨p1 * q2 + p2 * q1, ?_, p2 * q2, ?_, ?_⟩
  · exact Int.add_pos (Int.mul_pos hp1 hq2) (Int.mul_pos hp2 hq1)
  · exact Int.mul_pos hp2 hq2
  simp [Int.ne_of_lt hp2 |>.symm, Int.ne_of_lt hq2 |>.symm,
    intCast_eq, div_eq, inv_eq, mul_eq, add_eq]

theorem Rat.mul_Pos {p q : Rat} (hp: p.isPos) (hq: q.isPos) : (p * q).isPos := by
  simp only [isPos, gt_iff_lt, exists_and_left] at hp hq ⊢
  obtain ⟨p1, hp1, p2, hp2, rfl⟩ := hp
  obtain ⟨q1, hq1, q2, hq2, rfl⟩ := hq
  refine ⟨p1 * q1, ?_, p2 * q2, ?_, ?_⟩
  · exact Int.mul_pos hp1 hq1
  · exact Int.mul_pos hp2 hq2
  simp [Int.ne_of_lt hp2 |>.symm, Int.ne_of_lt hq2 |>.symm,
    intCast_eq, div_eq, inv_eq, mul_eq]

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

theorem Rat.isPos_iff_neg_isNeg (q: Rat) : q.isPos ↔ (-q).isNeg := by simp [isNeg]

theorem Rat.isNeg_iff_neg_isPos (q: Rat) : q.isNeg ↔ (-q).isPos := by simp [Rat.isPos_iff_neg_isNeg]

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
  wlog hx2' : x2 > 0 
  · specialize this x1 (-x2) (Int.neg_ne_zero.mpr hx2) (by omega)
    simp [hx2, ← neg_eq'] at this
    conv at this =>
      rw [isPos_iff_neg_isNeg, neg_neg]
      rhs
      rhs
      rw [isNeg_iff_neg_isPos, neg_neg]
    itauto
  obtain (h|rfl|h) := _root_.trichotomous (r := LT.lt) x1 0
  · refine Or.inr (Or.inr ?_)
    simp [isNeg, isPos]
    exact ⟨-x1, x2, ⟨Int.neg_pos_of_neg h, hx2'⟩, by simp [hx2, intCast_eq, div_eq, inv_eq, mul_eq]⟩
  · refine Or.inl ?_
    simp [hx2, ofNat_eq, eq]
  · refine Or.inr (Or.inl ?_)
    simp [isPos]
    exact ⟨x1, h, x2, hx2', by simp [hx2, intCast_eq, div_eq, inv_eq, mul_eq]⟩

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  refine not_and.mpr ?_
  rintro rfl ⟨x1, x2, hx1, hx2, h⟩
  simp [Int.ne_of_lt hx2 |>.symm, ofNat_eq, intCast_eq, div_eq, inv_eq, mul_eq, eq] at h
  exact Int.ne_of_lt hx1 h

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  simp only [ofNat_eq, CharP.cast_eq_zero, isNeg, isPos, gt_iff_lt, intCast_eq, div_eq, ne_eq,
    one_ne_zero, not_false_eq_true, inv_eq, exists_and_left, ↓existsAndEq, and_true, not_and,
    not_exists, and_imp]
  rintro rfl x1 x2 hx1 hx2
  simp only [ne_eq, one_ne_zero, not_false_eq_true, Int.ne_of_lt hx2 |>.symm, mul_eq, mul_one,
    one_mul, neg_eq, eq, zero_mul, zero_eq_neg, Int.ne_of_gt hx1]

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  simp only [isPos, gt_iff_lt, exists_and_left, isNeg, ↓existsAndEq, and_true, not_and, not_exists,
    and_imp, forall_exists_index]
  intro x1 hx1 x2 hx2 rfl y1 y2 hy1 hy2
  simp only [intCast_eq, div_eq, ne_eq, one_ne_zero, not_false_eq_true, inv_eq,
    Int.ne_of_lt hx2 |>.symm, mul_eq, mul_one, one_mul, Int.ne_of_lt hy2 |>.symm, neg_eq, eq,
    neg_mul]
  have hx1y2 := Int.mul_pos hx1 hy2
  have hy1x2 := Int.mul_pos hy1 hx2
  omega


theorem Rat.isPos_iff' {r1 r2: ℤ} (hr2 : r2 ≠ 0) : (r1 // r2).isPos ↔ r1 ≠ 0 ∧ (0 < r1 ↔ 0 < r2) := by
  constructor
  · rintro ⟨x1, x2, hx1, hx2, h⟩
    simp [Int.ne_of_lt hx2 |>.symm, hr2, intCast_eq, div_eq, inv_eq, mul_eq, eq] at h
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
    · simp [h'] at h
      exact h.elim (Int.ne_of_gt hx1) hr2
    · replace := h ▸ Int.mul_pos h' hx2
      exact Int.pos_of_mul_pos_right this hx1
    · replace := h ▸ Int.mul_pos hx1 h'
      exact Int.pos_of_mul_pos_left this hx2
  · rintro ⟨hr1, h⟩
    by_cases h' : 0 < r1
    · refine ⟨r1, r2, h', h.mp h', ?_⟩
      simp [hr2, intCast_eq, div_eq, inv_eq, mul_eq]
    · refine ⟨-r1, -r2, ?_, ?_, ?_⟩
      · refine Int.neg_pos_of_neg ?_
        refine Int.lt_iff_le_and_ne.mpr ⟨?_, hr1⟩
        exact Int.not_lt.mp h'
      · replace h' := h.not.mp h'
        refine Int.neg_pos_of_neg ?_
        refine Int.lt_iff_le_and_ne.mpr ⟨?_, hr2⟩
        exact Int.not_lt.mp h'
      simp [hr2, intCast_eq, div_eq, inv_eq, mul_eq]

theorem Rat.isNeg_iff' {r1 r2: ℤ} (hr2 : r2 ≠ 0) : (r1 // r2).isNeg ↔ r1 ≠ 0 ∧ ¬(0 < r1 ↔ 0 < r2) := by
  simp [hr2, isNeg_iff_neg_isPos, neg_eq, Rat.isPos_iff']
  intro hr1
  omega

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.isPos_iff {x: Rat} : x.isPos ↔ 0 < x := by
  constructor
  · rintro ⟨x1, x2, hx1, hx2, rfl⟩
    simp [Int.ne_of_lt hx1 |>.symm, Int.ne_of_lt hx2 |>.symm, hx1, hx2,
      intCast_eq, div_eq, inv_eq, mul_eq, lt_iff, isNeg, isPos_iff']
  · rintro hx
    simpa [lt_iff, isNeg_iff_neg_isPos] using hx

theorem Rat.isNeg_iff {x: Rat} : x.isNeg ↔ x < 0 := by
  simp [isNeg_iff_neg_isPos, isPos_iff]
  rw [lt_iff, lt_iff, sub_neg_eq_add, zero_add, sub_zero]

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  simp [lt_iff, isPos_iff_neg_isNeg]
  
theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  rw [eq_comm, ← le_iff]

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
  rcases trichotomous (x - y) with (h|h|h)
  · refine Or.inr (Or.inr ?_)
    exact sub_eq_zero.mp h
  · refine Or.inl ?_
    exact gt_iff _ _ |>.mpr h
  · refine Or.inr (Or.inl ?_)
    exact lt_iff _ _ |>.mpr h

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y) := by
  rw [lt_iff, gt_iff]
  exact not_pos_and_neg (x - y)

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by
  rw [gt_iff, and_comm, ← sub_eq_zero]
  exact not_zero_and_pos (x - y)

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by
  rw [lt_iff, and_comm, ← sub_eq_zero]
  exact not_zero_and_neg (x - y)

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ y > x := by
  rw [lt_iff, gt_iff, isNeg_iff_neg_isPos, neg_sub]

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  simp [lt_iff, isNeg] at hxy hyz ⊢
  obtain ⟨m, hm, hxy⟩ := hxy
  obtain ⟨n, hn, hyz⟩ := hyz
  use m + n, Rat.add_Pos hm hn
  calc
    _ = x - y + (y - z) := by ring
    _ = -m + -n := by rw [hxy, hyz]
    _ = _ := by ring

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  simpa [lt_iff] using hxy

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  simp [lt_iff, ← sub_mul, isNeg] at hxy ⊢
  obtain ⟨r, hr, hxy⟩ := hxy
  refine ⟨r * z, mul_Pos hr hz, hxy ▸ by ring⟩

theorem Rat.neg_lt_neg_iff {x y: Rat} : x < y ↔ -y < -x := by
  rw [lt_iff, lt_iff]
  ring_nf

theorem Rat.neg_le_neg_iff {x y: Rat} : -x ≤ -y ↔ y ≤ x := by
  rw [le_iff, le_iff, ← Rat.neg_lt_neg_iff, neg_inj, eq_comm]

theorem Rat.le_iff' {x y:Rat} : x ≤ y ↔ ∃(r: Rat), (0 ≤ r ∧ y - x = r) := by
  rw [le_iff, lt_iff]
  constructor
  · refine (Or.elim · 
      (fun h => ⟨y - x, ?_, by ring⟩)
      (fun h => ⟨0, Or.inr rfl, by rw [h, sub_self]⟩))
    replace h := isNeg_iff.mp h
    replace h := neg_lt_neg_iff.mp h
    simp at h
    exact Or.inl h
  rintro ⟨r, hr, hxy⟩
  by_cases hr' : r = 0
  · simp [hr', sub_eq_zero] at hxy
    exact Or.inr hxy.symm
  refine Or.inl ⟨r, ?_, by simp [← hxy]⟩
  exact isPos_iff.mpr (le_iff _ _ |>.mp hr |>.elim id (hr' ·.symm |>.elim))

theorem Rat.nonneg_iff {x1 x2: ℤ} (hx2: x2 ≠ 0) : 0 ≤ x1 // x2 ↔ x1 ≠ 0 ∧ (0 < x1 ↔ 0 < x2) ∨ x1 = 0 := by
  rw [le_iff, ← isPos_iff, isPos_iff']
  simp [hx2, ofNat_eq, eq, eq_comm]
  exact hx2

theorem Rat.add_nonneg {x y:Rat} (hx: 0 ≤ x) (hy: 0 ≤ y): 0 ≤ x + y := by
  rw [le_iff, ← isPos_iff] at hx hy ⊢
  rcases hx with hx|hx
  <;> rcases hy with hy|hy
  · exact Or.inl (add_Pos hx hy)
  · exact Or.inl <| by simpa [← hy]
  · exact Or.inl <| by simpa [← hx]
  · exact Or.inr (by rw [← hx, ← hy, add_zero])

theorem Rat.eq_zero_if_nonneg_add_nonneg_eq_zero {n m: Rat} 
  (hn: 0 ≤ n) (hm: 0 ≤ m) (h: n + m = 0) : n = 0 := by
    refine le_iff _ _ |>.mp hm |>.elim (fun hm => ?_) (fun h' => by simpa [h'] using h)
    refine le_iff _ _ |>.mp hn |>.elim (fun hn => ?_) Eq.symm
    have := add_Pos (isPos_iff.mpr hn) (isPos_iff.mpr hm) |> isPos_iff.mp
    exact not_lt_and_eq _ _ ⟨this, h.symm⟩ |>.elim

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    have hbd_nonzero := Int.mul_ne_zero hb hd
    have (x y: ℤ) (hy: y ≠ 0): Quotient.mk PreRat.instSetoid (PreRat.mk x y hy) = x // y := by simp [hy, formalDiv]
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            rw [this, this]
            simp [hb, hd, le_iff, lt_iff, isNeg, sub_eq, neg_eq, add_eq, eq]
            obtain h|h := or_comm.eq ▸ Int.le_iff_lt_or_eq.mp h
            · exact Or.inr (mul_comm c b ▸ h)
            refine Or.inl ⟨_, ?_, neg_neg _ |>.symm⟩
            simp [hb, hd, h, neg_eq, Rat.isPos_iff']
            exact ⟨by omega, lt_of_le_of_ne hbd hbd_nonzero.symm⟩
          | isFalse h =>
            apply isFalse
            rw [this, this]
            replace h := not_le.mp h
            simp [hb, hd, le_iff, lt_iff, Rat.isNeg_iff', eq, sub_eq, neg_eq, add_eq]
            refine ⟨fun _ => ⟨fun _ => ?_, fun _ => h⟩, mul_comm b c ▸ ne_of_lt h |>.symm⟩
            exact lt_of_le_of_ne hbd hbd_nonzero.symm
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            rw [this, this]
            simp [hb, hd, le_iff, lt_iff, isNeg, sub_eq, neg_eq, add_eq, eq]
            have  h' := Int.not_lt_of_ge h
            obtain h|h := or_comm.eq ▸ Int.le_iff_lt_or_eq.mp h
            · exact Or.inr (mul_comm c b ▸ h.symm)
            refine Or.inl ⟨_, ?_, neg_neg _ |>.symm⟩
            simp [hb, hd, h', neg_eq, Rat.isPos_iff']
            exact ⟨by omega, Int.le_of_not_le hbd⟩
          | isFalse h =>
            apply isFalse
            rw [this, this]
            replace h := not_le.mp h
            simp [hb, hd, le_iff, lt_iff, Rat.isNeg_iff', eq, sub_eq, neg_eq, add_eq]
            refine ⟨fun _ => not_iff_not.mp ⟨fun _ => ?_, fun _ => ?_⟩, ?_⟩
            · apply not_lt.mpr
              apply Int.le_of_lt
              exact Int.lt_of_not_ge hbd
            · apply not_lt.mpr
              exact Int.le_of_lt h
            apply ne_of_lt
            exact mul_comm b c ▸ h
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := fun _ ↦ Or.inr rfl
  le_trans := fun a b c hab hbc => by
    obtain ⟨m, hm, hab⟩ := le_iff'.mp hab
    obtain ⟨n, hn, hbc⟩ := le_iff'.mp hbc
    refine le_iff'.mpr ⟨m + n, add_nonneg hm hn, ?_⟩
    simp [← hab, ← hbc]
  lt_iff_le_not_ge := fun a b => by
    simp [le_iff, or_and_right]
    conv =>
      rhs; rhs
      rw [and_comm, and_assoc, eq_comm]
      simp
    simp [lt_iff]
    intro h
    simp [isNeg_iff_neg_isPos]
    constructor
    · by_contra h'
      exact not_pos_and_neg _ ⟨h', h⟩
    · by_contra h'
      exact not_zero_and_neg _ ⟨sub_eq_zero_of_eq h'.symm, h⟩
  le_antisymm := fun a b hab hba => by
    obtain ⟨m, hm, hab⟩ := le_iff'.mp hab
    obtain ⟨n, hn, hbc⟩ := le_iff'.mp hba
    replace hbc : b - a = -n := neg_sub a b ▸ congrArg Neg.neg hbc
    rw [hab, ← sub_eq_zero, sub_neg_eq_add] at hbc
    obtain rfl: m = 0 := Rat.eq_zero_if_nonneg_add_nonneg_eq_zero hm hn hbc
    replace hab := congr($hab + a)
    simpa [eq_comm] using hab
  le_total := fun a b => by rcases trichotomous' a b with h|h|h <;> tauto
  toDecidableLE := decidableRel

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := fun a b hab c => by
    obtain ⟨r, hr, hab⟩ := le_iff'.mp hab
    exact le_iff'.mpr ⟨r, hr, by simp [hab]⟩
  add_le_add_right := fun a b hab c => by
    obtain ⟨r, hr, hab⟩ := le_iff'.mp hab
    exact le_iff'.mpr ⟨r, hr, by simp [hab]⟩
  mul_lt_mul_of_pos_left := by
    intro a ha b c hbc
    rw [← isPos_iff] at ha
    simp [lt_iff, isNeg_iff_neg_isPos] at hbc
    simp [ha, hbc, lt_iff, ← mul_sub, isNeg_iff_neg_isPos, neg_mul_eq_mul_neg, mul_Pos]
  mul_lt_mul_of_pos_right := by
    intro a ha b c hbc
    rw [← isPos_iff] at ha
    simp [lt_iff, isNeg_iff_neg_isPos] at hbc
    simp [ha, hbc, lt_iff, ← sub_mul, isNeg_iff_neg_isPos, neg_mul_eq_neg_mul, mul_Pos]
  le_of_add_le_add_left := fun a b c h => by
    obtain ⟨r, hr, h⟩ := le_iff'.mp h
    exact le_iff'.mpr ⟨r, hr, by simpa using h⟩
  zero_le_one := by simp [ofNat_eq 1, nonneg_iff]

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  exact mul_lt_mul_of_neg_right hxy (isNeg_iff.mp hz)

theorem Rat.lt_iff_of_pos_denominator {x1 y1 x2 y2: ℤ} (hx2: x2 ≠ 0) (hy2: y2 ≠ 0) (h: 0 < x2 * y2) : 
  x1 // x2 < y1 // y2 ↔ x1 * y2 < y1 * x2 := by
    simp only [lt_iff, sub_eq, ne_eq, hy2, not_false_eq_true, neg_eq, hx2, add_eq, mul_neg,
      mul_comm, Int.add_neg_eq_sub, mul_eq_zero, or_self, isNeg_iff', sub_ne_zero, Int.sub_pos, h,
      iff_true, not_lt]
    rw [and_comm, lt_iff_le_and_ne]

theorem Rat.lt_iff_of_neg_denominator {x1 y1 x2 y2: ℤ} (hx2: x2 ≠ 0) (hy2: y2 ≠ 0) (h: x2 * y2 < 0) : 
  x1 // x2 < y1 // y2 ↔ y1 * x2 < x1 * y2  := by
    simp only [lt_iff, sub_eq, ne_eq, hy2, not_false_eq_true, neg_eq, hx2, add_eq, mul_neg]
    rw [isNeg_iff_neg_isPos, 
      neg_eq' _ (Int.mul_ne_zero hx2 hy2), 
      isPos_iff' (Int.neg_ne_zero.mpr (Int.mul_ne_zero hx2 hy2))]
    simp [h, Int.add_neg_eq_sub, sub_ne_zero, mul_comm]
    exact Int.ne_of_gt

theorem num_mkRat_of_div (x1 x2 : ℤ) (hx2: x2 ≠ 0) : (↑x1 / ↑x2: ℚ).num = (if x2 > 0 then x1 else -x1) / (x2.natAbs.gcd x1.natAbs) := by
  split_ifs with h
  · obtain ⟨x2, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt h)
    replace hx2 : x2 ≠ 0 := fun h ↦ hx2 (congrArg Nat.cast h)
    simp [hx2, ← Rat.mkRat_eq_div, Rat.num_mkRat, Int.natAbs_natCast]
  replace h : -x2 > 0 := by omega
  obtain ⟨x2, hx2⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt h)
  obtain rfl := Int.eq_neg_comm.mp hx2.symm; clear hx2 h
  replace hx2 : x2 ≠ 0 := by omega
  simp [hx2, div_neg_eq_neg_div, ← Rat.mkRat_eq_div, Rat.num_mkRat, Int.natAbs_natCast]
  refine Int.neg_ediv_of_dvd ?_ |>.symm
  refine Int.ofNat_dvd_left.mpr ?_
  exact Nat.gcd_dvd_right x2 x1.natAbs

theorem den_mkRat_of_div (x1 x2 : ℤ) (hx2: x2 ≠ 0) : (↑x1 / ↑x2: ℚ).den = x2.natAbs / (x2.natAbs.gcd x1.natAbs) := by
  by_cases h : x2 > 0
  · obtain ⟨x2, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt h)
    replace hx2 : x2 ≠ 0 := fun h ↦ hx2 (congrArg Nat.cast h)
    simp [hx2, ← Rat.mkRat_eq_div, Rat.den_mkRat, Int.natAbs_natCast]
  replace h : -x2 > 0 := by omega
  obtain ⟨x2, hx2⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt h)
  obtain rfl := Int.eq_neg_comm.mp hx2.symm; clear hx2 h
  replace hx2 : x2 ≠ 0 := by omega
  simp [hx2, div_neg_eq_neg_div, ← Rat.mkRat_eq_div, Rat.den_mkRat, Int.natAbs_natCast]

theorem mkRat_of_ints (x1 x2 : ℤ) (hx2: x2 ≠ 0) : 
  (↑x1 / ↑x2: ℚ) = mkRat (if x2 > 0 then x1 else -x1) x2.natAbs := by 
    split_ifs with h
    · obtain ⟨x2, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt h)
      replace hx2 : x2 ≠ 0 := fun h ↦ hx2 (congrArg Nat.cast h)
      simp [Rat.mkRat_eq_div]
    replace h : -x2 > 0 := by omega
    obtain ⟨x2, hx2⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt h)
    obtain rfl := Int.eq_neg_comm.mp hx2.symm; clear hx2 h
    replace hx2 : x2 ≠ 0 := by omega
    simp [Rat.mkRat_eq_div, div_neg_eq_neg_div']
/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    intro ⟨a1, a2, ha2⟩ ⟨b1, b2, hb2⟩ h
    simp [ha2, hb2, mkRat_of_ints, Rat.mkRat_eq_iff] at h ⊢
    split_ifs with ha2 hb2 hb2
    · simp [le_of_lt, ha2, hb2, abs_of_nonneg, h]
    · simp [le_of_lt ha2, le_of_not_gt hb2, abs_of_nonneg, abs_of_nonpos, h]
    · simp [le_of_lt hb2, le_of_not_gt ha2, abs_of_nonneg, abs_of_nonpos, h]
    · simp [le_of_not_gt, hb2, ha2, abs_of_nonpos, h]
  )
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := by
    obtain ⟨n1, n2, hn2, rfl⟩ := eq_diff n
    simp [hn2, intCast_eq, div_eq, inv_eq, mul_eq]
  right_inv n := by simp [ratCast_eq, Rat.num_div_den]

/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by
    intro x y
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, hy2, rfl⟩ := eq_diff y
    simp only [Equiv.coe_fn_mk, Quotient.lift_mk, ne_eq, hx2, not_false_eq_true, ↓reduceDIte, hy2,
      le_iff_lt_or_eq, _root_.Rat.lt_iff, num_mkRat_of_div, gt_iff_lt, den_mkRat_of_div,
      Int.natCast_ediv, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Rat.eq_iff_mul_eq_mul, eq]
    -- This is to clean up the normalizing factors introduced by the mathlib ℚ implementation
    set xn := x2.natAbs.gcd x1.natAbs
    have hxn : ↑xn ∣ x1 ∧ ↑xn ∣ x2 := by
      refine ⟨?_, Rat.normalize.dvd_num rfl⟩
      refine Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_right x2.natAbs x1.natAbs)
    have hxn' : (xn: ℤ) ≠ 0 := ne_zero_of_dvd_ne_zero hx2 hxn.right
    have hxn'' : 0 < (xn: ℤ) := lt_of_le_of_ne (Int.natCast_nonneg _) hxn'.symm
    set yn := y2.natAbs.gcd y1.natAbs
    have hyn : ↑yn ∣ y1 ∧ ↑yn ∣ y2 := by
      refine ⟨?_, Rat.normalize.dvd_num rfl⟩
      refine Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_right y2.natAbs y1.natAbs)
    have hyn' : (yn: ℤ) ≠ 0 := ne_zero_of_dvd_ne_zero hy2 hyn.right
    have hyn'' : 0 < (yn: ℤ) := lt_of_le_of_ne (Int.natCast_nonneg _) hyn'.symm
    conv =>
      lhs
      congr
      · rw [mul_comm,
          ← Int.mul_lt_mul_left hyn'',
          ← Int.mul_lt_mul_right hxn'',
        ]
        congr; all_goals
          rw [← mul_assoc, mul_assoc, mul_comm]
        · simp [hyn, Int.mul_ediv_cancel']
          rw [Int.ediv_mul_cancel (by
            split_ifs
            · exact hxn.left
            exact Int.dvd_neg.mpr hxn.left
          )]
        · simp [hxn, Int.ediv_mul_cancel]
          rw [Int.mul_ediv_cancel' (by
            split_ifs
            · exact hyn.left
            exact Int.dvd_neg.mpr hyn.left
          )]
      · rw [mul_comm,
          ← Int.mul_eq_mul_left_iff hyn',
          ← Int.mul_eq_mul_right_iff hxn',
        ]
        congr; all_goals
          rw [← mul_assoc, mul_assoc, mul_comm]
        · simp [hyn, Int.mul_ediv_cancel']
          rw [Int.ediv_mul_cancel (by
            split_ifs
            · exact hxn.left
            exact Int.dvd_neg.mpr hxn.left
          )]
        · simp [hxn, Int.ediv_mul_cancel]
          rw [Int.mul_ediv_cancel' (by
            split_ifs
            · exact hyn.left
            exact Int.dvd_neg.mpr hyn.left
          )]
    clear hyn'' hyn' hyn yn hxn'' hxn' hxn xn
    -- Now we can change the goal from ≤ iff to a < iff
    rw [mul_comm y1 x2]
    -- Change the ≤ iff to a < iff
    conv => congr <;> rw [or_comm]
    refine or_congr ?_ ?_
    · constructor
      · rintro h
        split_ifs at h with ha2 hb2 hb2
        · simpa [ha2, hb2, abs_of_pos] using h
        · simpa [ha2, not_lt.mp hb2, abs_of_pos, abs_of_nonpos] using h
        · simpa [not_lt.mp ha2, hb2, abs_of_pos, abs_of_nonpos] using h
        · simpa [not_lt.mp ha2, not_lt.mp hb2, abs_of_nonpos] using h
      · rintro h
        split_ifs with ha2 hb2 hb2
        · simpa [ha2, hb2, abs_of_pos] using h
        · simpa [ha2, not_lt.mp hb2, abs_of_pos, abs_of_nonpos] using h
        · simpa [not_lt.mp ha2, hb2, abs_of_pos, abs_of_nonpos] using h
        · simpa [not_lt.mp ha2, not_lt.mp hb2, abs_of_nonpos] using h
    split_ifs with hx hy hy
    · simp [hx2, hy2, hx, hy, abs_of_pos, lt_iff_of_pos_denominator, mul_comm]
    · have : x2 * y2 < 0 :=
        Int.mul_neg_of_pos_of_neg hx (lt_of_le_of_ne (not_lt.mp hy) hy2)
      simp [hx2, hy2, hx, not_lt.mp hy, abs_of_pos, abs_of_nonpos, 
        this, lt_iff_of_neg_denominator, mul_comm]
    · have : x2 * y2 < 0 :=
        Int.mul_neg_of_neg_of_pos (lt_of_le_of_ne (not_lt.mp hx) hx2) hy
      simp [hx2, hy2, not_lt.mp hx, hy, abs_of_pos, abs_of_nonpos, 
        this, lt_iff_of_neg_denominator, mul_comm]
    · have : 0 < x2 * y2 := by
        suffices h: 0 < (-x2) * (-y2); simpa using h
        apply lt_of_le_of_ne
        · refine Int.mul_nonneg ?_ ?_
          · exact Int.neg_nonneg_of_nonpos <| not_lt.mp hx
          · exact Int.neg_nonneg_of_nonpos <| not_lt.mp hy
        · simp [hx2, hy2]
      simp [hx, hy, hx2, hy2, not_lt.mp, abs_of_nonpos, this, lt_iff_of_pos_denominator, mul_comm]

/- example {a b c: ℚ} : a * b / (c * b) = a / c := by apply? -/

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := fun x y => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, hy2, rfl⟩ := eq_diff y
    simp [hx2, hy2, add_eq]
    replace hx2 : (x2: ℚ) ≠ 0 := Rat.num_ne_zero.mp hx2
    replace hy2 : (y2: ℚ) ≠ 0 := Rat.num_ne_zero.mp hy2
    calc
      _ = (↑x1 * ↑y2) / (↑x2 * ↑y2) + (↑x2 * ↑y1) / (↑x2 * ↑y2) := by ring
      _ = (↑x1: ℚ) / ↑x2 + ↑y1 / ↑y2 := by conv => 
        lhs
        congr
        · rw [Rat.mul_comm ↑x2 _, ← div_div]
          simp [hy2]
        · rw [Rat.mul_comm, ← div_div]
          simp [hx2]
  map_mul' := fun x y => by
    obtain ⟨x1, x2, hx2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, hy2, rfl⟩ := eq_diff y
    simp [hx2, hy2, mul_eq]
    replace hx2 : (x2: ℚ) ≠ 0 := Rat.num_ne_zero.mp hx2
    replace hy2 : (y2: ℚ) ≠ 0 := Rat.num_ne_zero.mp hy2
    ring

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
