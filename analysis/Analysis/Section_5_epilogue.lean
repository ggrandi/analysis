import Mathlib.Tactic
import Analysis.Section_5_6

/-!
# Analysis I, Chapter 5 epilogue: Isomorphism with the Mathlib real numbers

In this (technical) epilogue, we show that the "Chapter 5" real numbers `Chapter5.Real` are
isomorphic in various standard senses to the standard real numbers `ℝ`.  This we do by matching
both structures with Dedekind cuts of the (Mathlib) rational numbers `ℚ`.

From this point onwards, `Chapter5.Real` will be deprecated, and we will use the standard real
numbers `ℝ` instead.  In particular, one should use the full Mathlib API for `ℝ` for all
subsequent chapters, in lieu of the `Chapter5.Real` API.

Filling the sorries here requires both the Chapter5.Real API and the Mathlib API for the standard
natural numbers `ℝ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5


@[ext]
structure DedekindCut where
  E : Set ℚ
  nonempty : E.Nonempty
  bounded : BddAbove E
  lower: IsLowerSet E
  nomax : ∀ q ∈ E, ∃ r ∈ E, r > q

theorem isLowerSet_iff (E: Set ℚ) : IsLowerSet E ↔ ∀ q r, r < q → q ∈ E → r ∈ E :=
  isLowerSet_iff_forall_lt

abbrev Real.toSet_Rat (x:Real) : Set ℚ := { q | (q:Real) < x }

lemma Real.toSet_Rat_nonempty (x:Real) : x.toSet_Rat.Nonempty := by
  obtain ⟨q, _, hq⟩ := rat_between (sub_one_lt x)
  exact ⟨q, hq⟩

lemma Real.toSet_Rat_bounded (x:Real) : BddAbove x.toSet_Rat := by
  obtain ⟨q, hq, _⟩ := rat_between (lt_add_one x)
  refine ⟨q, fun p hp => ?_⟩
  exact Rat.cast_lt.mp (hp.trans hq) |>.le

lemma Real.toSet_Rat_lower (x:Real) : IsLowerSet x.toSet_Rat := by
  intro a b h ha
  exact ha.trans_le' (Rat.cast_le (K := Real) |>.mpr h)

lemma Real.toSet_Rat_nomax {x:Real} : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  obtain ⟨r, hr⟩ := rat_between hq
  refine ⟨r, hr.2, ?_⟩
  exact Rat.cast_lt.mp hr.1

abbrev Real.toCut (x:Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

lemma Real.toCut_E (x: Real) : x.toCut.E = x.toSet_Rat := rfl

abbrev DedekindCut.toSet_Real (c: DedekindCut) : Set Real := (fun (q:ℚ) ↦ (q:Real)) '' c.E

lemma DedekindCut.toSet_Real_nonempty (c: DedekindCut) : c.toSet_Real.Nonempty := by
  exact Set.Nonempty.image _ c.nonempty

lemma DedekindCut.toSet_Real_bounded (c: DedekindCut) : BddAbove c.toSet_Real := by
  obtain ⟨q, hq⟩ := c.bounded
  refine ⟨q, fun p hp => ?_⟩
  obtain ⟨r, hr, rfl⟩ := Set.mem_image _ _ _ |>.mp hp
  refine Rat.cast_le.mpr ?_ 
  exact hq hr

noncomputable abbrev DedekindCut.toReal (c: DedekindCut) : Real := sSup c.toSet_Real

lemma DedekindCut.toReal_isLUB (c: DedekindCut) : IsLUB c.toSet_Real c.toReal :=
  ExtendedReal.sSup_of_bounded c.toSet_Real_nonempty c.toSet_Real_bounded

noncomputable abbrev Real.equivCut : Real ≃ DedekindCut where
  toFun := toCut
  invFun := DedekindCut.toReal
  left_inv x := by
    rw [← isLUB_sSup x.toCut.toSet_Real_nonempty x.toCut.toSet_Real_bounded]
    refine ⟨fun q hq => ?_, ?_⟩
    · obtain ⟨r, hr, rfl⟩ := Set.mem_image _ _ _ |>.mp hq
      exact hr.le
    intro y hy
    rw [mem_upperBounds] at hy
    contrapose! hy with h
    obtain ⟨r, hr⟩ := rat_between h
    refine ⟨r, Set.mem_image _ _ _ |>.mpr ⟨r, hr.right, rfl⟩, hr.left⟩
  right_inv c := by
    let x := sSup ((fun (q:ℚ) ↦ (q:Real)) '' c.E)
    let hx : sSup ((fun (q:ℚ) ↦ (q:Real)) '' c.E) = x := rfl
    rw [← isLUB_sSup c.toSet_Real_nonempty c.toSet_Real_bounded] at hx
    ext q
    show (q: Real) < x ↔ q ∈ c.E
    constructor
    · intro hq
      have : (q: Real) ∉ upperBounds c.toSet_Real := (hq.not_ge <| hx.2 ·)
      simp [mem_upperBounds] at this
      obtain ⟨x, hx⟩ := this
      exact c.lower hx.2.le hx.1
    · intro h
      obtain ⟨r, hr⟩ := c.nomax q h
      exact (Rat.cast_lt (K := Real) |>.mpr hr.2).trans_le (hx.1 ⟨r, hr.1, rfl⟩)

end Chapter5

/-- Now to develop analogous results for the Mathlib reals. -/

abbrev Real.toSet_Rat (x:ℝ) : Set ℚ := { q | (q:ℝ) < x }

lemma Real.toSet_Rat_nonempty (x:ℝ) : x.toSet_Rat.Nonempty := by
  obtain ⟨q, _, hq⟩ := exists_rat_btwn (sub_one_lt x)
  exact ⟨q, hq⟩

lemma Real.toSet_Rat_bounded (x:ℝ) : BddAbove x.toSet_Rat := by
  obtain ⟨q, hq, _⟩ := exists_rat_btwn (lt_add_one x)
  refine ⟨q, fun p hp => ?_⟩
  exact Rat.cast_lt.mp (hp.trans hq) |>.le

lemma Real.toSet_Rat_lower (x:ℝ) : IsLowerSet x.toSet_Rat := by
  intro a b h ha
  exact ha.trans_le' (Rat.cast_le (K := Real) |>.mpr h)

lemma Real.toSet_Rat_nomax (x:ℝ) : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  obtain ⟨r, hr⟩ := exists_rat_btwn (show q < x from hq)
  refine ⟨r, hr.2, ?_⟩
  exact Rat.cast_lt.mp hr.1

abbrev Real.toCut (x:ℝ) : Chapter5.DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

namespace Chapter5

abbrev DedekindCut.toSet_R (c: DedekindCut) : Set ℝ := (fun (q:ℚ) ↦ (q:ℝ)) '' c.E

lemma DedekindCut.toSet_R_nonempty (c: DedekindCut) : c.toSet_R.Nonempty := by
  exact Set.Nonempty.image _ c.nonempty

lemma DedekindCut.toSet_R_bounded (c: DedekindCut) : BddAbove c.toSet_R := by
  obtain ⟨q, hq⟩ := c.bounded
  refine ⟨q, fun p hp => ?_⟩
  obtain ⟨r, hr, rfl⟩ := Set.mem_image _ _ _ |>.mp hp
  refine Rat.cast_le.mpr ?_ 
  exact hq hr

noncomputable abbrev DedekindCut.toR (c: DedekindCut) : ℝ := sSup c.toSet_R

lemma DedekindCut.toR_isLUB (c: DedekindCut) : IsLUB c.toSet_R c.toR :=
  isLUB_csSup c.toSet_R_nonempty c.toSet_R_bounded

end Chapter5

noncomputable abbrev Real.equivCut : ℝ ≃ Chapter5.DedekindCut where
  toFun := _root_.Real.toCut
  invFun := Chapter5.DedekindCut.toR
  left_inv x := by
    show sSup ((fun (q:ℚ) ↦ (q:ℝ)) '' x.toSet_Rat) = x
    refine IsLUB.csSup_eq ?_ x.toCut.toSet_R_nonempty
    refine ⟨fun q hq => ?_, ?_⟩
    · obtain ⟨r, hr, rfl⟩ := Set.mem_image _ _ _ |>.mp hq
      exact hr.le
    intro y hy
    rw [mem_upperBounds] at hy
    contrapose! hy with h
    obtain ⟨r, hr⟩ := exists_rat_btwn h
    refine ⟨r, Set.mem_image _ _ _ |>.mpr ⟨r, hr.right, rfl⟩, hr.left⟩
  right_inv c := by
    let x := sSup c.toSet_R
    let hx : IsLUB c.toSet_R x := Chapter5.DedekindCut.toR_isLUB c
    ext q
    show (q: Real) < x ↔ q ∈ c.E
    constructor
    · intro hq
      have : (q: Real) ∉ upperBounds c.toSet_R := (hq.not_ge <| hx.2 ·)
      simp [mem_upperBounds] at this
      obtain ⟨x, hx⟩ := this
      exact c.lower hx.2.le hx.1
    · intro h
      obtain ⟨r, hr⟩ := c.nomax q h
      exact (Rat.cast_lt (K := Real) |>.mpr hr.2).trans_le (hx.1 ⟨r, hr.1, rfl⟩)

namespace Chapter5

/-- The isomorphism between the Chapter 5 reals and the Mathlib reals. -/
noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl

-- In order to use this definition, we need some machinery
-----

-- We start by showing it works for ratCasts
theorem Real.equivR_ratCast {q: ℚ} : equivR q = (q: ℝ) := by
  refine IsLUB.csSup_eq ?_ (Set.Nonempty.image _ <| Real.toSet_Rat_nonempty _)
  constructor
  · intro _ hp
    obtain ⟨p, hp, h⟩ := Set.mem_image _ _ _ |>.mpr hp
    replace hp : (_: Real) < (_: Real) := hp
    refine h ▸ Rat.cast_le.mpr ?_
    refine Rat.cast_lt.mp hp |>.le
  intro M h
  rw [mem_upperBounds] at h
  contrapose! h
  obtain ⟨p, hp⟩ := exists_rat_btwn h
  refine ⟨p, Set.mem_image_of_mem Rat.cast ?_, hp.1⟩
  have := Rat.cast_lt.mp hp.2
  exact Rat.cast_lt (K := Real) |>.mpr this

lemma Real.equivR_nat {n: ℕ} : equivR n = (n: ℝ) := equivR_ratCast
lemma Real.equivR_int {n: ℤ} : equivR n = (n: ℝ) := equivR_ratCast

lemma Real.equivR_ofNat {n: ℕ} : equivR (no_index ofNat(n)) = ((no_index ofNat(n)): ℝ) := by
  rw [Lean.Grind.Semiring.ofNat_eq_natCast]
  exact equivR_nat

-- We then want to set up a way to convert from the Real `LIM` to the ℝ `Real.mk`
-- To do this we need a few things:

-- Convertion between the notions of Cauchy Sequences
theorem Sequence.IsCauchy.to_IsCauSeq {a: ℕ → ℚ} (ha: IsCauchy a) : IsCauSeq _root_.abs a := by
  rw [coe] at ha
  intro ε εpos
  replace ⟨N, ha⟩ := ha (ε / 2) (by positivity)
  refine ⟨N, fun j hj => ?_⟩
  refine ha j hj N (le_refl _) |>.trans_lt ?_
  exact div_two_lt_of_pos εpos

-- Convertion of an `IsCauchy` to a `CauSeq`
abbrev Sequence.IsCauchy.CauSeq {a: ℕ → ℚ} : (ha: IsCauchy a) → CauSeq ℚ _root_.abs := 
  (⟨a, ·.to_IsCauSeq⟩)

lemma Sequence.IsCauchy.CauSeq_val {a: ℕ → ℚ} (ha: IsCauchy a) 
  : ha.CauSeq.val = a := rfl

lemma Sequence.IsCauchy.CauSeq_sub {a b: ℕ → ℚ} (hb: IsCauchy b) (ha: IsCauchy a) 
  : hb.CauSeq - ha.CauSeq = (hb.sub ha).CauSeq := by
    ext n
    rw [CauSeq.sub_apply]
    rfl

theorem Sequence.IsCauchy.iff_IsCauSeq {a: ℕ → ℚ} : IsCauchy a ↔ IsCauSeq _root_.abs a := by
  constructor
  · exact to_IsCauSeq 
  rw [coe]
  intro h ε εpos
  obtain ⟨N, h⟩ := h (ε / 2) (by positivity)
  refine ⟨N, fun i hi j hj => ?_⟩
  calc |a i - a j|
  _ = |(a i - a N) - (a j - a N)| := by ring_nf
  _ ≤ |a i - a N| + |a j - a N| := abs_sub _ _
  _ ≤ ε / 2 + ε / 2 := add_le_add (h i hi).le (h j hj).le
  _ = ε := add_halves ε

-- We then set up the conversion from Sequence.Equiv to CauSeq.LimZero because 
-- it is the equivalence relation
example {a b: CauSeq ℚ abs} : a ≈ b ↔ CauSeq.LimZero (a - b) := by rfl

theorem Sequence.Equiv.LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b) (h:Equiv a b) 
  : CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    rw [equiv_iff] at h
    intro _ εpos
    replace ⟨ε, εpos, hε⟩ := exists_rat_btwn εpos
    replace εpos := Rat.cast_pos.mp εpos
    replace ⟨N, h⟩ := h (ε / 2) (half_pos εpos)
    refine ⟨N, fun j hj => ?_⟩
    rw [CauSeq.sub_apply, ha.CauSeq_val, hb.CauSeq_val]
    refine hε.trans' ?_
    refine div_two_lt_of_pos εpos |>.trans_le' ?_
    simpa using h j hj

-- We can now use it to convert between different functions in Real.mk
theorem Real.mk_eq_mk {a b: ℕ → ℚ} (ha : Sequence.IsCauchy a) (hb : Sequence.IsCauchy b) (hab: Sequence.Equiv a b)
  : Real.mk ha.CauSeq = Real.mk hb.CauSeq := Real.mk_eq.mpr (hab.LimZero ha hb)

-- Both directions of the equivalence
theorem Sequence.Equiv_iff_LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b) 
  : Equiv a b ↔ CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    refine ⟨(·.LimZero ha hb), ?_⟩
    rw [equiv_iff]
    intro h ε εpos
    simp [IsCauchy.CauSeq, CauSeq.LimZero] at h
    replace ⟨N, h⟩ := h ε (Rat.cast_pos.mpr εpos)
    refine ⟨N, fun j hj => ?_⟩
    simpa [← Rat.cast_sub, ← Rat.cast_abs] using h j hj |>.le

----
-- We create some cauchy sequences with useful properties

-- We show that for any sequence, it will eventually be arbitrarily close to its LIM
open Real in
theorem Sequence.difference_approaches_zero {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) :
  ∀ε > 0, ∃N, ∀n ≥ N, |LIM a - a n| ≤ (ε: ℚ) := by
    intro ε εpos
    obtain ⟨N, ha'⟩ := IsCauchy.coe _ |>.mp ha ε εpos
    refine ⟨N, fun n hn => ?_⟩
    have := ha.sub (.const (a n))
    rw [ratCast_def, LIM_sub ha (IsCauchy.const _), LIM_abs this]
    refine LIM_of_le' (IsCauchy.abs this) ⟨N, fun j hj => ?_⟩
    simpa [← Rat.cast_sub, ← Rat.cast_abs] using ha' j hj n hn

-- There exists a Cauchy sequence entirely above the LIM
theorem Real.exists_equiv_above {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) 
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, LIM a ≤ b n := by 
    suffices ∃b, _ ∧ _ by 
      obtain ⟨b, hab, hb⟩ := this
      exact ⟨b, Sequence.isCauchy_of_equiv hab |>.mp ha, hab, hb⟩
    refine ⟨fun n => if h: a n < LIM a then 
        rat_between (show LIM a < 2 * LIM a - a n by linarith) |>.choose
      else a n, ?_, ?_⟩
    · rw [Sequence.equiv_iff]
      intro ε εpos
      obtain ⟨N, ha⟩ := Sequence.difference_approaches_zero ha (ε/2) (half_pos εpos)
      refine ⟨N, fun n hn => ?_⟩
      split_ifs with han
      case neg => simpa using εpos.le
      generalize_proofs h
      rw [← Rat.cast_le (K := Real), Rat.cast_abs, Rat.cast_sub]
      calc
      _ = -(a n - h.choose: Real) := by
        rw [abs_of_nonpos]
        refine sub_nonpos.mpr ?_
        exact han.trans h.choose_spec.1 |>.le
      _ = (h.choose - a n: Real) := by ring
      _ ≤ 2 * LIM a - a n - a n := sub_le_sub_right h.choose_spec.2.le _
      _ = 2 * (LIM a - a n) := by ring
      _ = 2 * |LIM a - a n| := by
        congr; rw [_root_.abs_of_pos]
        exact sub_pos.mpr han
      _ ≤ 2 * (ε/2: ℚ) := mul_le_mul_of_nonneg_left (ha _ hn) zero_le_two
      _ = ε := by
        rw [Rat.cast_div, Rat.cast_ofNat, mul_div_cancel₀ _ zero_lt_two.ne']
    intro n
    dsimp
    split_ifs with han
    · generalize_proofs h 
      exact h.choose_spec.1.le
    exact (not_lt.mp han)

-- There exists a Cauchy sequence entirely below the LIM
theorem Real.exists_equiv_below {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) 
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, b n ≤ LIM a := by 
    suffices ∃b, _ ∧ _ by 
      obtain ⟨b, hab, hb⟩ := this
      exact ⟨b, Sequence.isCauchy_of_equiv hab |>.mp ha, hab, hb⟩
    refine ⟨fun n => if h: LIM a < a n then 
        rat_between (show 2 * LIM a - a n < LIM a by linarith) |>.choose
      else a n, ?_, ?_⟩
    · rw [Sequence.equiv_iff]
      intro ε εpos
      obtain ⟨N, ha⟩ := Sequence.difference_approaches_zero ha (ε/2) (half_pos εpos)
      refine ⟨N, fun n hn => ?_⟩
      split_ifs with han
      case neg => simpa using εpos.le
      generalize_proofs h
      rw [← Rat.cast_le (K := Real), Rat.cast_abs, Rat.cast_sub]
      calc
      _ = (a n - h.choose: Real) := by
        rw [abs_of_nonneg]
        refine sub_nonneg.mpr ?_
        exact han.trans' h.choose_spec.2 |>.le
      _ ≤ a n - (2 * LIM a - a n) := sub_le_sub_left h.choose_spec.1.le _
      _ = 2 * (a n - LIM a) := by ring
      _ = 2 * |LIM a - a n| := by
        congr; rw [_root_.abs_of_neg, neg_sub]
        exact sub_neg.mpr han
      _ ≤ 2 * (ε/2: ℚ) := mul_le_mul_of_nonneg_left (ha _ hn) zero_le_two
      _ = ε := by
        rw [Rat.cast_div, Rat.cast_ofNat, mul_div_cancel₀ _ zero_lt_two.ne']
    intro n
    dsimp
    split_ifs with han
    · generalize_proofs h
      exact h.choose_spec.2.le
    exact (not_lt.mp han)

----

-- useful theorems for the following proof
#check Real.mk_le
#check Real.mk_le_of_forall_le
#check Real.mk_const

-- Transform a `Real` to an `ℝ` by going through Cauchy Sequences
-- we can use the conversion of Real.mk_eq to use different sequences to show different parts
theorem Real.equivR_eq' {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) 
  : (LIM a).equivR = Real.mk ha.CauSeq := by 
    by_cases hq: ∃(q: ℚ), q = LIM a
    · obtain ⟨q, hq⟩ := hq
      rw [← hq]
      rw [Real.ratCast_def, LIM_eq_LIM (.const _) ha] at hq
      rw [← Real.mk_eq_mk (.const _) ha hq]
      exact equivR_ratCast
    show sSup (Rat.cast '' (LIM a).toSet_Rat) = _
    refine IsLUB.csSup_eq ⟨?_, ?_⟩ (Set.Nonempty.image _ <| Real.toSet_Rat_nonempty _)
    · -- show that `Real.mk ha.CauSeq` is an upper bound
      intro _ hy
      obtain ⟨b, hb, hab, hb'⟩ := Real.exists_equiv_above ha
      obtain ⟨y, hy, h⟩ := Set.mem_image _ _ _ |>.mp hy
      rw [← h, ← Real.mk_const, mk_eq_mk ha hb hab, Real.mk_le]
      refine le_of_lt ?_
      show ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ _
      obtain ⟨z, hz⟩ := rat_between hy
      refine ⟨z - y, ?_, 0, fun j _ => ?_⟩
      · exact sub_pos.mpr (Rat.cast_lt.mp hz.1)
      simpa using Rat.cast_le.mp <| hz.2.trans_le (hb' j) |>.le
    -- show that for any other upper bound, `Real.mk ha.CauSeq` is smaller
    intro M hM
    obtain ⟨b, hb, hab, hb'⟩ := exists_equiv_below ha
    rw [mk_eq_mk ha hb hab]
    refine Real.mk_le_of_forall_le ?_
    dsimp
    refine ⟨0, fun j _ => hM ?_⟩
    refine Set.mem_image_of_mem _ ?_
    show (b j: Real) < LIM a
    refine hb' j |>.lt_of_ne ?_
    exact (not_exists.mp hq) _

lemma Real.equivR_eq (x: Real) : ∃(a : ℕ → ℚ) (ha: Sequence.IsCauchy a), 
  x = LIM a ∧ x.equivR = Real.mk ha.CauSeq := by 
    obtain ⟨a, ha, rfl⟩ := x.eq_lim
    exact ⟨a, ha, rfl, equivR_eq' ha⟩

/-- The isomorphism preserves order and ring operations -/
noncomputable abbrev Real.equivR_ordered_ring : Real ≃+*o ℝ where
  toEquiv := equivR
  map_add' := fun x y => by
    obtain ⟨a, ha, ha_eq, haR_eq⟩ := x.equivR_eq
    obtain ⟨b, hb, hb_eq, hbR_eq⟩ := y.equivR_eq
    obtain ⟨c, hc, hc_eq, hcR_eq⟩ := (x + y).equivR_eq
    simp [haR_eq, hbR_eq, hcR_eq, ← Real.mk_add, Real.mk_eq]
    have := Sequence.IsCauchy.add ha hb
    refine Sequence.Equiv_iff_LimZero hc this |>.mp ?_
    rw [← LIM_eq_LIM, ← LIM_add, ← ha_eq, ← hb_eq, ← hc_eq] 
    <;> assumption
  map_mul' := fun x y => by
    obtain ⟨a, ha, ha_eq, haR_eq⟩ := x.equivR_eq
    obtain ⟨b, hb, hb_eq, hbR_eq⟩ := y.equivR_eq
    obtain ⟨c, hc, hc_eq, hcR_eq⟩ := (x * y).equivR_eq
    simp [haR_eq, hbR_eq, hcR_eq, ← Real.mk_mul, Real.mk_eq]
    have := Sequence.IsCauchy.mul ha hb
    refine Sequence.Equiv_iff_LimZero hc this |>.mp ?_
    rw [← LIM_eq_LIM, ← LIM_mul, ← ha_eq, ← hb_eq, ← hc_eq] 
    <;> assumption
  map_le_map_iff' := by 
    intro x y
    obtain ⟨a, ha, ha_eq, haR_eq⟩ := x.equivR_eq
    obtain ⟨b, hb, hb_eq, hbR_eq⟩ := y.equivR_eq
    simp only [Equiv.toFun_as_coe, haR_eq, hbR_eq]
    rw [ha_eq, hb_eq, le_iff_eq_or_lt, le_iff_eq_or_lt]
    refine or_congr ?_ ?_
    · rw [Real.mk_eq, LIM_eq_LIM ha hb]
      exact Sequence.Equiv_iff_LimZero ha hb |>.symm
    show _ ↔ Real.IsNeg _
    rw [neg_iff_pos_of_neg, neg_sub, LIM_sub hb ha]
    constructor
    · rw [Real.mk_lt]
      rintro ⟨K, Kpos, N, h⟩
      let c := fun n => if n < N then K else (b - a) n
      refine ⟨c, ⟨K, Kpos, fun n => if hn: n < N then ?_ else ?_⟩, ?_⟩
      · simp [c, hn]
      · simpa [c, hn] using h n (not_lt.mp hn)
      suffices h1: Sequence.Equiv (b - a) c from
        have h2 := Sequence.isCauchy_of_equiv h1 |>.mp (hb.sub ha)
        ⟨h2, LIM_eq_LIM (hb.sub ha) h2 |>.mpr h1⟩
      rw [Sequence.equiv_iff]
      intro ε εpos
      refine ⟨N, fun n hn => ?_⟩
      simpa [c, hn.not_gt] using εpos.le
    rintro ⟨c, ⟨K, Kpos, hK⟩, hc, heq⟩
    refine sub_pos.mp ?_
    replace heq: Sequence.Equiv (b - a) c := LIM_eq_LIM (hb.sub ha) hc |>.mp heq
    have := Real.mk_eq.mpr <| heq.LimZero (hb.sub ha) hc
    rw [_root_.sub_eq_add_neg, ← Real.mk_neg, ← Real.mk_add, ← _root_.sub_eq_add_neg, 
      hb.CauSeq_sub ha, this, Real.mk_pos]
    exact ⟨K, Kpos, 0, fun n _ => hK n⟩

-- helpers for converting properties between Real and ℝ
lemma Real.equivR_map_mul {x y : Real} : equivR (x * y) = equivR x * equivR y :=
  equivR_ordered_ring.map_mul _ _

lemma Real.equivR_map_inv {x: Real} : equivR (x⁻¹) = (equivR x)⁻¹ :=
  map_inv₀ equivR_ordered_ring _

lemma Real.equivR_map_neg {x: Real} : equivR (-x) = -equivR x :=
  equivR_ordered_ring.map_neg _

theorem Real.equivR_map_pos {x: Real} : 0 < x ↔ 0 < equivR x := by
  rw [show ∀x, equivR x = equivR_ordered_ring x from fun _ => rfl,
    ← equivR_ordered_ring.symm_apply_lt,
    show equivR_ordered_ring.symm 0 = 0 from equivR_ordered_ring.symm.map_zero
  ]

theorem Real.equivR_map_nonneg {x: Real} : 0 ≤ x ↔ 0 ≤ equivR x := by
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt]
  refine or_congr ?_ equivR_map_pos
  conv => congr <;> rw [eq_comm]
  exact equivR_ordered_ring.map_eq_zero_iff.symm

theorem Sequence.IsCauchy.pow {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) (n: ℕ) 
  : Sequence.IsCauchy (a ^ n: ℕ → ℚ) := by
    induction n
    case zero => simpa only [pow_zero] using Sequence.IsCauchy.const _
    case succ n ih =>
      rw [pow_succ]
      exact ih.mul ha

theorem Real.LIM_pow {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) (n: ℕ) : LIM (a ^ n) = (LIM a) ^ n := by
  induction n
  case zero => simp [Pi.ofNat_def, Real.ofNat_def]
  case succ n ih =>
    rw [pow_succ, _root_.pow_succ, ← LIM_mul (ha.pow n) ha, ih]

-- Showing equivalence of the different pows
theorem Real.pow_of_equivR (x:Real) (n:ℕ) : equivR (x^n) = (equivR x)^n := by
  obtain ⟨a, ha, rfl, haR_eq⟩ := x.equivR_eq
  induction n
  case zero => rw [pow_zero, equivR_ofNat, _root_.pow_zero]
  case succ n ih =>
    rw [_root_.pow_succ, equivR_map_mul, ih, _root_.pow_succ]

theorem Real.zpow_of_equivR (x:Real) (n:ℤ) : equivR (x^n) = (equivR x)^n := by
  by_cases hn: 0 ≤ n
  · lift n to ℕ using hn
    exact pow_of_equivR _ _
  obtain ⟨n, hn⟩ := CanLift.prf (β := ℕ) (-n) (by omega)
  rw [← neg_eq_iff_eq_neg.mpr hn, neg_eq_neg_one_mul, ← zpow_mul, zpow_neg_one,
    _root_.zpow_mul, zpow_neg_one, ← equivR_map_inv
  ]
  exact pow_of_equivR _ _

theorem Real.ratPow_of_equivR (x:Real) (hx: 0 ≤ x) (q:ℚ) : equivR (x^q) = (equivR x)^(q:ℝ) := by
  refine pow_left_inj₀ ?_ ?_ q.den_pos.ne' |>.mp ?_
  · refine equivR_map_nonneg.mp ?_
    exact ratPow_nonneg hx _
  · refine Real.rpow_nonneg ?_ ↑q
    exact equivR_map_nonneg.mp hx
  rw [← pow_of_equivR, ratPow_iff, ← zpow_root_comm hx q.den_pos,
    pow_of_root (zpow_nonneg _ hx) q.den_pos, zpow_of_equivR,
    ← Real.rpow_intCast, Real.rpow_pow_comm, ← Real.rpow_natCast_mul,
    ← Rat.cast_natCast, ← Rat.cast_mul, ← Rat.cast_intCast,
    Rat.den_mul_eq_num
  ]
  all_goals exact equivR_map_nonneg.mp hx

end Chapter5
