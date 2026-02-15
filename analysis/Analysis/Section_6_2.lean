import Mathlib.Tactic
import Analysis.Section_5_5
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.2: The extended real number system

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals `EReal`, particularly with regard to the supremum
  operation `sSup` and infimum operation `sInf`.

-/

open EReal

/-- Definition 6.2.1 -/
theorem EReal.def (x:EReal) : (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ := by
  revert x
  simp [EReal.forall]

theorem EReal.real_neq_infty (x:ℝ) : (x:EReal) ≠ ⊤ := coe_ne_top _

theorem EReal.real_neq_neg_infty (x:ℝ) : (x:EReal) ≠ ⊥ := coe_ne_bot _

theorem EReal.infty_neq_neg_infty : (⊤:EReal) ≠ (⊥:EReal) := add_top_iff_ne_bot.mp rfl

abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

theorem EReal.infinite_iff_not_finite (x:EReal): x.IsInfinite ↔ ¬ x.IsFinite := by
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def x <;> simp [IsFinite, IsInfinite]

/-- Definition 6.2.2 (Negation of extended reals) -/
theorem EReal.neg_of_real (x:Real) : -(x:EReal) = (-x:ℝ) := rfl

#check EReal.neg_top
#check EReal.neg_bot

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.le_iff (x y:EReal) :
    x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y <;> simp

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.lt_iff (x y:EReal) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

#check EReal.coe_lt_coe_iff

/-- Examples 6.2.4 -/
example : (3:EReal) ≤ (5:EReal) := by rw [le_iff]; left; use (3:ℝ), (5:ℝ); norm_cast


/-- Examples 6.2.4 -/
example : (3:EReal) < ⊤ := by simp [lt_iff]; exact real_neq_infty 3


/-- Examples 6.2.4 -/
example : (⊥:EReal) < ⊤ := by simp


/-- Examples 6.2.4 -/
example : ¬ (3:EReal) ≤ ⊥ := by
  by_contra h
  simp at h
  exact real_neq_neg_infty 3 h

#check instCompleteLinearOrderEReal

/-- Proposition 6.2.5(a) / Exercise 6.2.1 -/
theorem EReal.refl (x:EReal) : x ≤ x := by
  rw [le_iff]
  obtain ⟨x, rfl⟩ | rfl | rfl := x.def
  · exact Or.inl ⟨x, x, rfl, rfl, le_refl (α := ℝ) _⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.trichotomy (x y:EReal) : x < y ∨ x = y ∨ x > y := by
  obtain ⟨x, rfl⟩ | rfl | rfl := x.def
  <;> obtain ⟨y, rfl⟩ | rfl | rfl := y.def
  · convert trichotomous (α := ℝ) (r := LT.lt) x y 
    exact EReal.coe_lt_coe_iff
    exact EReal.coe_eq_coe_iff
    exact EReal.coe_lt_coe_iff
  · exact Or.inl <| coe_lt_top _
  · exact Or.inr <| Or.inr <| bot_lt_coe _
  · exact Or.inr <| Or.inr <| coe_lt_top _
  · exact Or.inr <| Or.inl rfl
  · exact Or.inr <| Or.inr <| bot_lt_top
  · exact Or.inl <| bot_lt_coe _
  · exact Or.inl <| bot_lt_top
  · exact Or.inr <| Or.inl rfl

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_eq (x y:EReal) : ¬ (x < y ∧ x = y) := by
  refine not_and.mpr fun h => ?_
  exact lt_iff _ _ |>.mp h |>.2

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_gt_and_eq (x y:EReal) : ¬ (x > y ∧ x = y) := by
  convert not_lt_and_eq y x using 2
  exact eq_comm

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_gt (x y:EReal) : ¬ (x < y ∧ x > y) := by
  obtain ⟨x, rfl⟩ | rfl | rfl := x.def
  <;> obtain ⟨y, rfl⟩ | rfl | rfl := y.def
  · simpa only [EReal.coe_lt_coe_iff, not_and] using lt_asymm (α := ℝ)
  · exact not_and.mpr fun _ => not_top_lt
  · exact not_and'.mpr fun _ => not_lt_bot
  · exact not_and'.mpr fun _ => not_top_lt
  · exact not_and.mpr fun _ => not_top_lt
  · exact not_and'.mpr fun _ => not_top_lt
  · exact not_and.mpr fun _ => not_lt_bot
  · exact not_and.mpr fun _ => not_lt_bot
  · exact not_and.mpr fun _ => not_lt_bot

/-- Proposition 6.2.5(c) / Exercise 6.2.1 -/
theorem EReal.trans {x y z:EReal} (hxy : x ≤ y) (hyz: y ≤ z) : x ≤ z := by
  rw [le_iff] at *
  obtain ⟨x, y, hx, hy, hxy⟩ | hy | hx := hxy
  <;> obtain ⟨y', z, hy', hz, hyz⟩ | hz | hy' := hyz
  · refine Or.inl ⟨x, z, hx, hz, ?_⟩
    refine hxy.trans_eq ?_ |>.trans hyz
    refine EReal.coe_eq_coe_iff.mp ?_
    exact hy.symm.trans hy'
  · exact Or.inr (Or.inl hz)
  · refine (bot_lt_coe y).ne' ?_ |>.elim
    exact hy.symm.trans hy'
  · refine (coe_lt_top y').ne ?_ |>.elim
    exact hy'.symm.trans hy
  · exact Or.inr (Or.inl hz)
  · refine bot_ne_top (hy'.symm.trans hy) |>.elim
  · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inr hx)

/-- Proposition 6.2.5(d) / Exercise 6.2.1 -/
theorem EReal.neg_of_lt {x y:EReal} (hxy : x ≤ y): -y ≤ -x := by
  rw [le_iff] at *
  obtain ⟨x, y, hx, hy, hxy⟩ | hx | hy := hxy
  · refine Or.inl ⟨-y, -x, ?_, ?_, ?_⟩
    <;> try rwa [EReal.coe_neg, neg_inj]
    exact _root_.neg_le_neg_iff.mpr hxy
  · refine Or.inr (Or.inr ?_)
    rw [hx, neg_top]
  · refine Or.inr (Or.inl ?_)
    rw [hy, neg_bot]

/-- Definition 6.2.6 -/
theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
    sSup (Real.toEReal '' E) = sSup E := calc
  _ = sSup
      ((fun (x:WithTop ℝ) ↦ (x:WithBot (WithTop ℝ))) '' ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E)) := by
    rw [←Set.image_comp]; congr
  _ = sSup ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E) := by
    symm; apply WithBot.coe_sSup'
    . simp [hnon]
    exact WithTop.coe_mono.map_bddAbove hbound
  _ = ((sSup E : ℝ) : WithTop ℝ) := by congr; symm; exact WithTop.coe_sSup' hbound
  _ = _ := rfl

/-- Definition 6.2.6 -/
theorem EReal.sup_of_unbounded_nonempty {E: Set ℝ} (hunbound: ¬ BddAbove E) (hnon: E.Nonempty) :
    sSup (Real.toEReal '' E) = ⊤ := by
  rw [sSup_eq_top]
  intro b hb
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
  . simp; contrapose! hunbound; exact ⟨ y, hunbound ⟩
  . simp at hb
  simpa

/-- Definition 6.2.6 -/
theorem EReal.sup_of_empty : sSup (∅:Set EReal) = ⊥ := sSup_empty

/-- Definition 6.2.6 -/
theorem EReal.sup_of_infty_mem {E: Set EReal} (hE: ⊤ ∈ E) : sSup E = ⊤ := csSup_eq_top_of_top_mem hE

/-- Definition 6.2.6 -/
theorem EReal.sup_of_neg_infty_mem {E: Set EReal} : sSup E = sSup (E \ {⊥}) := 
  (sSup_diff_singleton_bot _).symm

theorem EReal.inf_eq_neg_sup (E: Set EReal) : sInf E = - sSup (-E) := by
  simp_rw [←isGLB_iff_sInf_eq, isGLB_iff_le_iff, EReal.le_neg]
  intro b
  simp [lowerBounds]

section example_6_2_7

/-- Example 6.2.7 -/
abbrev Example_6_2_7 : Set EReal := { x | ∃ n:ℕ, x = -((n+1):EReal)} ∪ {⊥}

example : sSup Example_6_2_7 = -1 := by
  rw [EReal.sup_of_neg_infty_mem, Example_6_2_7, Set.union_diff_right, ← sup_of_neg_infty_mem]
  refine IsLUB.sSup_eq ?_
  constructor 
  · rintro _ ⟨n, rfl⟩ 
    rw [← Nat.cast_add_one, neg_le_neg_iff, ← Nat.cast_one, Nat.cast_le]
    exact Nat.le_add_left 1 n
  rintro M hM
  refine hM ?_
  exact ⟨0, by rw [Nat.cast_zero, zero_add]⟩

example : sInf Example_6_2_7 = ⊥ := by
  rw [EReal.inf_eq_neg_sup, neg_eq_iff_eq_neg, neg_bot, Example_6_2_7, 
    Set.union_singleton, Set.neg_insert, neg_bot]
  refine sup_of_infty_mem ?_
  exact Set.mem_insert _ _

end example_6_2_7

theorem rpow_log_div_log_self {a b: ℝ} (ha: 0 < a) (ha': a ≠ 1) (hb: 0 < b) 
  : a ^ (Real.log b / Real.log a) = b := by
    refine (Real.mul_log_eq_log_iff ha hb).mp ?_
    refine div_mul_cancel₀ _ ?_
    exact Real.log_ne_zero_of_pos_of_ne_one ha ha'

section example_6_2_8

/-- Example 6.2.8 -/
abbrev Example_6_2_8 : Set EReal := { x | ∃ n:ℕ, x = (1 - (10:ℝ)^(-(n:ℤ)-1):Real)}

example : sInf Example_6_2_8 = (0.9:ℝ) := by 
  rw [EReal.inf_eq_neg_sup, neg_eq_iff_eq_neg, Example_6_2_8]
  refine IsLUB.sSup_eq ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_neg.mp hx
    rw [← neg_neg x]
    refine neg_of_lt ?_
    rw [hn, EReal.coe_le_coe_iff, le_sub_comm, 
      show (1 - 0.9: ℝ) = 10⁻¹ by norm_num,
      sub_eq_add_neg, ← _root_.neg_add,
      ← Nat.cast_add_one, zpow_neg, zpow_natCast,
      inv_le_inv₀ ?_ ?_
    ]
    refine le_self_pow₀ ?_ ?_
    all_goals norm_num
  intro M hM
  exact hM ⟨0, by norm_num⟩

example : sSup Example_6_2_8 = 1 := by
  refine IsLUB.sSup_eq ⟨?_, ?_⟩
  . intro x hx
    obtain ⟨n, rfl⟩ := hx
    rw [← EReal.coe_one, EReal.coe_le_coe_iff, sub_le_self_iff]
    positivity
  rw [← EReal.coe_one, Example_6_2_8]
  intro M hM
  by_contra! h
  obtain ⟨x, hMx, hx1⟩ := lt_iff_exists_real_btwn.mp h
  suffices ∃y ∈ Example_6_2_8, x ≤ y by
    obtain ⟨y, hy, hxy⟩ := this
    exact hMx.not_ge <| hxy.trans (hM hy)
  simp only [Example_6_2_8, Set.mem_setOf_eq, ↓existsAndEq, EReal.coe_le_coe_iff, true_and, EReal.coe_lt_coe_iff] at ⊢ hx1
  let y := 1 - x
  have hy: 0 < y := _root_.sub_pos.mpr hx1
  simp_rw [show x = 1 - y from (sub_sub_self 1 x).symm, sub_le_sub_iff_left, 
    sub_eq_add_neg, ← _root_.neg_add]
  by_cases hy': y ≤ 1
  · obtain ⟨n, hn⟩ := CanLift.prf (-FloorRing.floor (y.log / Real.log 10)) (β := ℕ) (by
      refine neg_nonneg_of_nonpos ?_
      refine Int.floor_nonpos ?_
      refine div_nonpos_of_nonpos_of_nonneg ?_ ?_
      exact Real.log_nonpos hy.le hy'
      exact Real.log_nonneg (by norm_num)
    )
    refine ⟨n, ?_⟩
    simp [hn, zpow_add₀, inv_mul_eq_div]
    refine div_le_self hy.le (show 1 ≤ 10 by norm_num) |>.trans' ?_
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine (Real.zpow_le_iff_le_log (by positivity) hy).mpr ?_
    refine le_div_iff₀ (by positivity) |>.mp ?_
    exact Int.floor_le _
  obtain ⟨n, hn⟩ := CanLift.prf (FloorRing.floor (y.log / Real.log 10)) (β := ℕ) (by
    refine Int.floor_nonneg.mpr ?_
    refine div_nonneg ?_ ?_ <;> refine Real.log_nonneg ?_
    exact le_of_not_ge hy'
    norm_num
  )
  refine ⟨n, ?_⟩
  simp [← Real.rpow_intCast, hn]
  refine le_of_le_of_eq (b := (10: ℝ) ^ (Real.log y / Real.log 10)) ?_ ?_
  pick_goal 2; refine rpow_log_div_log_self ?_ ?_ hy <;> norm_num
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  refine (Int.floor_le _).trans' ?_
  simp [← two_mul]
  refine neg_one_lt_zero.le.trans ?_
  refine mul_nonneg (by positivity) ?_
  refine Int.cast_nonneg_iff.mpr ?_
  refine Int.floor_nonneg.mpr ?_
  refine div_nonneg ?_ ?_ <;> refine Real.log_nonneg ?_
  · exact le_of_not_ge hy'
  norm_num

end example_6_2_8

/-- Example 6.2.9 -/
abbrev Example_6_2_9 : Set EReal := { x | ∃ n:ℕ, x = n+1}

example : sInf Example_6_2_9 = 1 := by
  rw [Example_6_2_9, inf_eq_neg_sup]
  refine le_antisymm ?_ ?_
  · simp [Set.neg_setOf, ← EReal.coe_one, ← EReal.coe_natCast, ← EReal.coe_add, 
      neg_eq_iff_eq_neg, ← EReal.coe_neg, EReal.neg_le]
    refine le_sSup ⟨0, by simp⟩
  · simp [Set.neg_setOf, ← EReal.coe_one, ← EReal.coe_natCast, ← EReal.coe_add, 
      neg_eq_iff_eq_neg, ← EReal.coe_neg, EReal.le_neg]

example : sSup Example_6_2_9 = ⊤ := by 
  simp [Example_6_2_9, ← EReal.coe_one, ← EReal.coe_natCast, ← EReal.coe_add]
  refine sSup_eq_top.mpr fun b hb => ?_
  obtain ⟨b, rfl⟩ | hb := b.def.elim Or.inl (·.resolve_left hb.ne |> Or.inr)
  · obtain ⟨a, ha⟩ := exists_nat_gt b
    refine ⟨(a + 1: ℕ), ⟨a, ?_⟩, ?_⟩
    · simp
    rw [← EReal.coe_natCast, EReal.coe_lt_coe_iff, Nat.cast_add_one]
    exact ha.trans (lt_add_one _)
  refine ⟨1, ⟨0, ?_⟩, ?_⟩ <;> simp [hb, ← EReal.coe_one]

example : sInf (∅ : Set EReal) = ⊤ := by
  rw [inf_eq_neg_sup, Set.neg_empty, sup_of_empty, neg_bot]

example (E: Set EReal) : sSup E < sInf E ↔ E = ∅ := by
  constructor
  case mpr =>
    rintro rfl
    simp
  contrapose! 
  intro ⟨x, hx⟩
  exact sInf_le hx |>.trans <| le_sSup hx

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_le_sup (E: Set EReal) {x:EReal} (hx: x ∈ E) 
  : x ≤ sSup E := (isLUB_sSup E).1 hx

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_ge_inf (E: Set EReal) {x:EReal} (hx: x ∈ E) 
  : sInf E ≤ x := by
    rw [inf_eq_neg_sup, EReal.neg_le]
    refine mem_le_sup _ ?_
    exact Set.neg_mem_neg.mpr hx

/-- Theorem 6.2.11 (b) / Exercise 6.2.2 -/
theorem EReal.sup_le_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) 
  : sSup E ≤ M := by
    have : IsLUB E (sSup E) := isLUB_sSup E
    exact (isLUB_le_iff this).mpr hM

example (a b: EReal) : -a = b ↔ a = -b := by exact neg_eq_iff_eq_neg

/-- Theorem 6.2.11 (c) / Exercise 6.2.2 -/
theorem EReal.inf_ge_upper (E: Set EReal) {M:EReal} (hM: M ∈ lowerBounds E) 
  : sInf E ≥ M := by
    rw [ge_iff_le, ← neg_le_neg_iff, inf_eq_neg_sup, neg_neg]
    refine sup_le_upper _ ?_
    intro x hx
    rw [Set.mem_neg] at hx
    rw [EReal.le_neg]
    exact hM hx

#check isLUB_iff_sSup_eq
#check isGLB_iff_sInf_eq

/-- Not in textbook: identify the Chapter 5 extended reals with the Mathlib extended reals.
-/
noncomputable abbrev Chapter5.ExtendedReal.toEReal (x:ExtendedReal) : EReal := match x with
  | real r => ((Real.equivR r):EReal)
  | infty => ⊤
  | neg_infty => ⊥

theorem Chapter5.ExtendedReal.coe_inj : Function.Injective toEReal := by
  rintro (x|x|x) (y|y|y) hxy <;> try rfl
  case real.real =>
    rw [coe_injective.eq_iff, Real.equivR.injective.eq_iff] at hxy
    rw [hxy]
  all_goals simp at hxy

theorem Chapter5.ExtendedReal.coe_surj : Function.Surjective toEReal := by 
  rintro (x|x|x)
  · exact ⟨neg_infty, rfl⟩
  · exact ⟨infty, rfl⟩
  refine ⟨Real.equivR.symm x, ?_⟩
  dsimp only [toEReal]
  rw [Real.equivR.apply_symm_apply]
  rfl

lemma EReal.coe_eq (x: ℝ) : (x: EReal) = some (some x) := rfl

noncomputable abbrev Chapter5.ExtendedReal.equivEReal : Chapter5.ExtendedReal ≃ EReal where
  toFun := toEReal
  invFun : EReal → ExtendedReal
    | none => .neg_infty
    | some none => .infty
    | some (some r) => .real (Real.equivR.symm r)
  left_inv := by
    rintro (x|x|x)
    case neg_infty => simp
    case infty => simp
    dsimp only [toEReal, EReal.coe_eq]
    exact real.injEq _ _ ▸ Real.equivR.symm_apply_apply x
  right_inv := by
    rintro (x|x|x)
    case none => rfl
    case some.none => rfl
    dsimp only [toEReal, EReal.coe_eq]
    rw [Option.some_inj, Option.some_inj, Real.equivR.apply_symm_apply]

