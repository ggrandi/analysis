import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  refine ⟨fun x => ⟨((2 * (x:ℕ)): ℕ), ?_⟩, ?_, ?_⟩
  · rw [specification_axiom'']
    use nat_equiv (2 * nat_equiv.symm x) |>.prop
    simp
  · intro x y h
    simp at h
    exact h
  · intro ⟨x, hx⟩
    simp [specification_axiom''] at hx
    obtain ⟨h, ⟨y, hy⟩⟩ := hx
    use y
    simp at ⊢
    rw [← Nat.two_mul] at hy
    rw [← hy, Object.ofnat_eq'']


@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X :=
  ⟨id, Function.bijective_id⟩

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg, hg'⟩ := Function.bijective_iff_has_inverse.mp hf
  exact ⟨g, Function.bijective_iff_has_inverse.mpr ⟨f, hg', hg⟩⟩

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  obtain ⟨f1, hf1⟩ := h1
  obtain ⟨f2, hf2⟩ := h2
  exact ⟨f2 ∘ f1, Function.Bijective.comp hf2 hf1⟩
  

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, EqualCard]

abbrev SetTheory.Set.singleton_has_card (x: Object) : ({x}: Set).has_card 1 := by
  rw [has_card_iff]
  refine ⟨fun _ => Fin_mk 1 0 Nat.one_pos, ?_, ?_⟩
  · intro a b h; clear h
    rw [← coe_inj, mem_singleton _ _ |>.mp a.prop, mem_singleton _ _ |>.mp b.prop]
  · intro n
    obtain ⟨m, hm, hnm⟩ := mem_Fin _ _ |>.mp n.prop
    replace hnm : (n: ℕ) = m := (Fin.coe_eq_iff n).mp hnm
    obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
    refine ⟨⟨x, mem_singleton _ _ |>.mpr rfl⟩, ?_⟩ 
    simp [hnm]

abbrev SetTheory.Set.pair_has_card {x y: Object} (hxy : x ≠ y) : ({x, y}: Set).has_card 2 := by
  rw [has_card_iff]
  refine ⟨fun z => by
    if z.val = x then exact Fin_mk 2 0 Nat.zero_lt_two
    else exact Fin_mk 2 1 Nat.one_lt_two, ?_, ?_
  ⟩
  · intro a b h
    simp at h
    by_cases ha : a.val = x
    <;> by_cases hb : b.val = x
    · simpa [←hb, coe_inj] using ha
    · simp [if_pos ha, if_neg hb] at h
    · simp [if_neg ha, if_pos hb] at h
    replace ha : a.val = y := mem_pair _ _ _ |>.mp a.prop |>.elim (ha · |>.elim) id
    replace hb : b.val = y := mem_pair _ _ _ |>.mp b.prop |>.elim (hb · |>.elim) id
    · simpa [←hb, coe_inj] using ha
  · intro ⟨m, hm'⟩
    obtain ⟨m, hm, rfl⟩ := mem_Fin _ _ |>.mp hm'
    obtain (rfl|rfl) : m = 0 ∨ m = 1 := 
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hm)
    · exact ⟨⟨x, mem_pair _ _ _ |>.mpr (Or.inl rfl)⟩, by simp⟩
    refine ⟨⟨y, mem_pair _ _ _ |>.mpr (Or.inr rfl)⟩, ?_⟩
    simp [hxy.symm]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
  (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
    apply has_card_iff _ _ |>.mpr
    refine ⟨fun x => ⟨((⟨x.val, specification_axiom x.prop⟩: Nat): ℕ).pred, ?_⟩, ?_, ?_⟩
    · rw [mem_Fin]
      refine ⟨(nat_equiv.symm ⟨x, specification_axiom x.prop⟩).pred, ?_, rfl⟩
      obtain ⟨_, hx', hx⟩  := specification_axiom'' _ _ |>.mp x.prop
      set x := ((⟨x.val, specification_axiom x.prop⟩: Nat): ℕ)
      have : x.pred < x := Nat.pred_lt (Nat.ne_zero_of_lt hx')
      exact Nat.lt_of_lt_of_le this hx
    · intro x y h
      simp only [Subtype.mk.injEq, Object.natCast_inj] at h
      obtain ⟨_, hx, _⟩  := specification_axiom'' _ _ |>.mp x.prop
      obtain ⟨_, hy, _⟩  := specification_axiom'' _ _ |>.mp y.prop
      replace h := _root_.Nat.pred_inj hx hy h
      simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, Subtype.coe_inj] at h
      exact h
    · intro x
      refine ⟨⟨(x: ℕ).succ, ?_⟩, by simp⟩
      have := specification_axiom x.prop
      have ⟨x, hx⟩ : ∃n: ℕ, ↑x = n := by use ↑x
      simp_rw [hx]
      refine specification_axiom'' _ _ |>.mpr ⟨?_, ?_, ?_⟩ 
      · have ⟨x, hx'⟩ : ∃n: Nat, x.succ = ↑n :=
          ⟨x.succ, Equiv.apply_eq_iff_eq_symm_apply _ |>.mp rfl⟩
        simp_rw [hx', Object.ofnat_eq'']
        exact x.prop
      · exact Object.ofnat_eq''' ▸ NeZero.one_le
      · subst x
        rw [Object.ofnat_eq''']
        have ⟨x', hx, h⟩ := mem_Fin _ _ |>.mp x.prop
        simp_all

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hX_empty
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.
  obtain ⟨⟨y, hy⟩, _⟩ := hf.surjective (nonempty_choose hnon)
  exact (not_mem_empty _) (hX_empty ▸ hy)

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  rw [has_card_iff]
  have hFin_0 : Fin 0 = ∅ := by ext x; simp
  refine ⟨?_, ?_⟩ 
  · intro ⟨f, _⟩ 
    by_contra! hX
    have ⟨_, h⟩ := f (nonempty_choose hX)
    exact (not_mem_empty _) (hFin_0 ▸ h)
  · intro h
    refine ⟨fun ⟨_,hx⟩ => (not_mem_empty _) (h ▸ hx) |>.elim, ?_, ?_⟩
    · intro ⟨_, hx⟩ _ _
      exact (not_mem_empty _) (h ▸ hx) |>.elim
    · intro ⟨_, hx⟩
      exact (not_mem_empty _) (hFin_0 ▸ hx) |>.elim

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (hn: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX
  choose f hf using hX
  set X' : Set := X \ {x.val}
  have mem_X' {v} : v ∈ X' ↔ v ∈ X ∧ v ≠ x.val := by rw [mem_sdiff, mem_singleton]
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by simp_all only [ge_iff_le, mem_sdiff, mem_singleton, ne_eq,
    implies_true, X'] ⟩
  have hι : ∀ x:X', ι x = ⟨x, mem_X'.mp x.prop |>.left⟩ := fun _ => rfl
  have ι_inj {x y} : ι x = ι y ↔ x = y := by
    refine ⟨fun h => ?_, congrArg _⟩ 
    simp_rw [hι, Subtype.mk.injEq, coe_inj] at h
    exact h
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  have hfι (x': X') : (f (ι x'):ℕ) ≠ m₀ := by
      by_contra!
      simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property
      rename_i this_2
      subst this_2
      simp_all only [ge_iff_le, implies_true, mem_sdiff, mem_singleton, not_true_eq_false, and_false, X', ι]
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let := hfι x'
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg_def' (x':X') : if (g x':ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g]
    <;> split_ifs with h''
    · exact Fin.toNat_mk _ _
    · have hgx' := hg_def x'
      rw [if_neg h''] at hgx'
      rw [hgx'] at h'
      replace h': (f (ι x'): ℕ) ≤ m₀ := Nat.le_of_pred_lt h'
      replace h'' := Nat.le_of_not_lt h''
      exact (hfι x') (Nat.le_antisymm h' h'') |>.elim
    · have hgx' := hg_def x'
      rw [if_pos h''] at hgx'
      rw [hgx'] at h'
      exact h' h'' |>.elim
    · exact Fin.toNat_mk _ _
  refine Exists.intro g ⟨?_, ?_⟩
  · intro a b h
    apply ι_inj.mp
    apply hf.injective
    have hfιa := hfι a
    have hfιb := hfι b
    have hga := hg_def a
    have hgb := hg_def' b
    split_ifs at hga with hga'
    · rwa [if_pos (h ▸ hga ▸ hga'), ← h, hga, ← Fin.coe_inj] at hgb
    · have hfam : (f (ι a): ℕ) > m₀ := 
        Nat.lt_of_le_of_ne (Nat.le_of_not_lt hga') (hfιa).symm
      rw [
        if_neg (by 
          rw [← h, hga, not_lt]
          exact Nat.le_sub_one_of_lt hfam
        ), ← h, hga] at hgb
      have hfbm : (f (ι a): ℕ) - 1 ≥ m₀ := Nat.le_sub_one_of_lt hfam
      rw [hgb] at hfbm
      replace hfbm : (f (ι b): ℕ) ≥ m₀ := hfbm.trans (Nat.sub_le _ _)
      replace hfbm : (f (ι b): ℕ) > m₀ := Nat.lt_of_le_of_ne hfbm (id (Ne.symm hfιb))
      replace hgb := Nat.pred_inj (Nat.zero_lt_of_lt hfam) (Nat.zero_lt_of_lt hfbm) hgb
      exact Fin.coe_inj.mpr hgb
  intro m
  by_cases h : m < m₀
  · obtain ⟨a, ha⟩ := hf.surjective (Fin_embed n.pred n (Nat.pred_le n) m)
    have : a ≠ x := by
      by_contra! h'
      replace h' := congrArg Subtype.val <| congrArg f h'
      rw [ha, hm₀f] at h'
      simp only [Fin.coe_eq_iff] at h'
      exact Nat.ne_of_lt h h'
    let a': X' := ⟨a, mem_X'.mpr ⟨a.prop, Subtype.coe_ne_coe.mpr this⟩⟩
    have hιa: ι a' = a := rfl
    have : ↑(f (ι a')) < m₀ := by rwa [hιa, ha, Fin.coe_eq_iff']
    use a'
    simp [g, dif_pos this, hιa, ha]
  rw [not_lt] at h
  let m' := Fin_mk n (m: ℕ).succ (by
    obtain ⟨m, hm, hm'⟩  := mem_Fin _ _ |>.mp m.prop
    rw [Fin.coe_eq_iff _ |>.mp hm']
    exact Nat.lt_of_le_pred hn hm
  )
  have hm' : (m': ℕ)  = (m: ℕ).succ := (Fin.coe_eq_iff m').mp rfl
  obtain ⟨a, ha⟩ := hf.surjective m'
  have : a ≠ x := by 
    by_contra! h'
    replace h' := congrArg Subtype.val <| congrArg f h'
    rw [ha, hm₀f] at h'
    simp only [Fin.coe_eq_iff] at h'
    refine (?_: ¬ _) h'
    have := _root_.Nat.lt_succ_of_le h
    replace := _root_.Nat.ne_of_lt this |>.symm
    exact hm' ▸ this
  let a': X' := ⟨a, mem_X'.mpr ⟨a.prop, Subtype.coe_ne_coe.mpr this⟩⟩
  have hιa: ι a' = a := rfl
  have : ¬↑(f (ι a')) < m₀ := by 
    rw [hιa, ha, hm']
    apply not_lt.mpr
    exact h.trans (Nat.le_succ _)
  use a'
  simp [g, dif_neg this, hιa, ha, hm']

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  induction' n with n hn generalizing X m
  . rw [has_card_zero] at h1
    contrapose! h1
    apply pos_card_nonempty _ h2
    exact Nat.one_le_iff_ne_zero.mpr h1.symm
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  induction' n with n ih
  · refine ⟨0, fun ⟨i, hi⟩ => ?_⟩ 
    obtain ⟨_, hm, _⟩ := mem_Fin _ _ |>.mp hi
    apply (Nat.not_lt_zero _) hm |>.elim
  · obtain ⟨M, hm⟩ := ih (fun i => f (Fin_embed n n.succ (Nat.le_succ n) i))
    let n': Fin (n + 1) := Fin_mk n.succ n (Nat.lt_add_one n)
    let M' := Nat.max M (f n')
    refine ⟨M', fun i => ?_⟩
    rw [Std.le_max]
    by_cases h : i = n'
    · exact Or.inr (h ▸ le_refl _)
    replace h : (i: ℕ) ≠ n := by
      contrapose! h
      refine Fin.coe_inj.mpr ?_
      rw [h]
      exact (Fin.toNat_mk _ _).symm
    replace hm := hm <| Fin_mk n (i: ℕ) (by
      have ⟨m, hm, him⟩ := mem_Fin _ _ |>.mp i.prop
      replace him : (i: ℕ) = m := (Fin.coe_eq_iff _).mp him
      rw [him]
      replace hm : m ≤ n := Nat.le_of_lt_succ hm
      replace him : m ≠ n := him ▸ h
      exact Nat.lt_of_le_of_ne hm him
    )
    left
    simpa [Fin.embed_mk] using hm

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv, Setoid.r, EqualCard] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_to_has_card' {X:Set} {n: ℕ} (hX: X.finite) (hX_card: X.card = n) : X.has_card n := by
  unfold card at hX_card
  rw [← hX_card, dif_pos hX]
  exact hX.choose_spec

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  rw [card]
  constructor
  · rintro rfl
    have hempty : empty.finite := ⟨0, has_card_zero.mpr rfl⟩
    refine ⟨hempty, ?_⟩ 
    rw [dif_pos hempty]
    apply card_uniq hempty.choose_spec (has_card_zero.mpr rfl)
  · rintro ⟨h_finite, h⟩ 
    exact has_card_zero.mp ((dif_pos h_finite ▸ h) ▸ h_finite.choose_spec)

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

example {a b : Prop} {ha: ¬a} : (a ∨ b) ↔ b := by exact or_iff_right ha

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
(X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  let n := X.card
  have : X.has_card n := has_card_card hX
  have X_x_has_card : (X ∪ {x}).has_card n.succ := by
    rw [has_card_iff]
    choose f hf using has_card_iff _ _ |>.mp this
    let f' (x': (X ∪ {x}).toSubtype) : Fin n.succ := by
      if h : x'.val ∈ X then 
        exact Fin_embed n n.succ (Nat.le_succ _) (f ⟨x'.val, h⟩)
      else exact Fin_mk n.succ n (Nat.lt_add_one n)
    refine ⟨f', ?_, ?_⟩
    · intro a b h
      unfold f' at h
      by_cases ha: a.val ∈ X
      <;> by_cases hb: b.val ∈ X
      · simp [dif_pos ha, dif_pos hb] at h
        replace h := hf.injective <| (coe_inj _ _ _).mp h
        replace h : a.val = b.val := Subtype.mk.injEq _ _ _ _ |>.to_iff.mp h
        exact (coe_inj _ _ _).mp h
      · simp [dif_pos ha, dif_neg hb] at h
        have : f ⟨↑a, ha⟩ ≠ n := ne_of_lt <| Fin.toNat_lt _
        exact this h |>.elim
      · simp [dif_neg ha, dif_pos hb] at h
        have : f ⟨↑b, hb⟩ ≠ n := ne_of_lt <| Fin.toNat_lt _
        replace h : f ⟨↑b, hb⟩ = n := (Fin.coe_eq_iff _).mp h.symm
        exact this h |>.elim
      · replace ha : a.val ∈ ({x}: Set) := or_iff_right ha |>.mp <| mem_union _ _ _ |>.mp a.prop
        replace ha := (mem_singleton _ _).mp ha
        replace hb : b.val ∈ ({x}: Set) := or_iff_right hb |>.mp <| mem_union _ _ _ |>.mp b.prop
        replace hb := (mem_singleton _ _).mp hb
        exact (coe_inj _ _ _).mp (ha.trans hb.symm)
    intro m
    by_cases hm : n = m
    · use ⟨x, mem_union _ _ _ |>.mpr (Or.inr <| mem_singleton _ _ |>.mpr rfl)⟩
      simpa [f', dif_neg hx]
    · obtain ⟨x', hx'⟩ := hf.surjective (Fin_mk n m (by
        obtain ⟨m', hm', h⟩  := mem_Fin _ _ |>.mp m.prop
        obtain rfl : (m: ℕ) = m' := (Fin.coe_eq_iff m).mp h 
        exact lt_of_le_of_ne (Nat.le_of_lt_succ hm') (fun h ↦ hm h.symm)
      ))
      use ⟨x', mem_union _ _ _ |>.mpr (Or.inl <| x'.prop)⟩
      simp [f', dif_pos x'.prop, hx']
  refine ⟨Exists.intro n.succ X_x_has_card, has_card_to_card X_x_has_card⟩ 

theorem SetTheory.Set.induction_insert {p : Set → Prop} {X: Set} (hX: X.finite) (hempty: p empty)
  (hind: ∀x X, X.finite → x ∉ X → p X → p (X ∪ {x})) : p X := by
    obtain ⟨n, hn⟩ := hX
    induction' n with n ih generalizing X
    · exact has_card_zero.mp hn ▸ hempty
    have X_nonempty : X ≠ ∅ := by
      apply has_card_zero.not.mp
      by_contra h
      exact Nat.zero_lt_succ n |>.ne (card_uniq h hn)
    let x := nonempty_choose X_nonempty
    let X' := X \ {x.val}
    have hx : x.val ∉ X' := by
      rw [mem_sdiff, not_and, not_not]
      exact fun _ => mem_singleton _ _ |>.mpr rfl
    have X'_card : X'.has_card n := SetTheory.Set.card_erase (Nat.le_add_left _ _) hn x
    obtain hX : X = X' ∪ {x.val} := by
      ext x'
      unfold X'
      simp [mem_union, mem_singleton, mem_sdiff]
      constructor
      · intro h
        by_cases hx' : x' = x.val
        · exact Or.inr hx'
        exact Or.inl ⟨h, hx'⟩ 
      · rintro (h|h)
        · exact h.left
        exact h ▸ x.prop
    exact hX ▸ hind x.val X' ⟨n, X'_card⟩ hx (ih X'_card)

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
  (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
    have ⟨m, hm⟩ := hY
    apply induction_insert hX
    · simp [hY]
    intro x X hX hx ih
    rw [card_insert hX hx |>.2]
    by_cases hy : x ∈ Y
    · have hXY : X ∪ {x} ∪ Y = X ∪ Y := by
        rw [union_assoc, subset_union (show {x} ⊆ Y by
          intro x' hx'
          obtain rfl := mem_singleton _ _ |>.mp hx'
          exact hy
        )]
      refine ⟨hXY ▸ ih.1, hXY ▸ Nat.le_trans ih.2 ?_⟩ 
      refine Nat.add_le_add_right ?_ _
      exact Nat.le_add_right _ _
    have hxy : x ∉ X ∪ Y := by
      rw [mem_union, not_or]
      exact ⟨hx, hy⟩ 
    have := card_insert ih.1 hxy
    rw [union_right_comm]
    refine ⟨this.1, ?_⟩ 
    rw [this.2, add_right_comm]
    exact Nat.add_le_add_right ih.2 _

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  : (hdisj: Disjoint X Y) → (X ∪ Y).card = X.card + Y.card := by
    have ⟨m, hm⟩ := hY
    apply induction_insert hX
    · simp
    intro x X hX hx ih hdisj
    replace hdisj := by simp [Set.disjoint_iff, Set.ext_iff, mem_inter] at hdisj; exact hdisj
    have X_subset : X ⊆ X ∪ {x} := subset_union_left _ _
    have : Disjoint X Y := by
      simp [Set.disjoint_iff, Set.ext_iff, mem_inter]
      intro x' hx
      by_contra hy
      have := not_imp_not.mpr (hdisj x') (fun h ↦ h hy) |> not_or.mp
      exact this.1 hx
    specialize ih this
    have hxy : x ∉ X ∪ Y := by
      rw [mem_union, not_or]
      exact ⟨hx, hdisj x (Or.inr rfl)⟩ 
    rw [
      union_right_comm, 
      card_insert (card_union hX hY).left hxy |>.2, 
      card_insert hX hx |>.2,
      ih,
      add_right_comm
    ]

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
  Y.finite ∧ Y.card ≤ X.card := by
    have ⟨n, hn⟩ := hX
    induction' n with n ih generalizing X Y
    · obtain rfl : X = ∅ := has_card_zero.mp hn
      obtain rfl : Y = ∅ := subset_antisymm _ _ hY (empty_subset _)
      exact ⟨finite_of_empty rfl, Nat.le_refl empty.card⟩ 
    by_cases hXY : X \ Y = ∅
    · have : X = Y := by
        ext x
        obtain h : X = X ∪ Y := union_subset hY |>.symm
        rw [union_eq_partition, hXY, empty_union] at h
        rw [Set.ext_iff.mp h x, mem_union, mem_inter, mem_sdiff, and_comm, ← and_or_left, and_iff_left_iff_imp]
        exact fun _ => Classical.em _
      exact this ▸ ⟨hX, Nat.le_refl _⟩ 
    have X_nonempty := pos_card_nonempty (Nat.le_add_left _ _) hn
    let x := nonempty_choose hXY
    have hx := mem_sdiff _ _ _ |>.mp x.prop
    let X' := X \ {x.val}
    have X'_card : X'.has_card n := 
      card_erase (Nat.le_add_left _ _) hn ⟨x.val, hx.left⟩
    have Y_subset : Y ⊆ X' := by
      intro y hy
      rw [mem_sdiff, mem_singleton]
      refine ⟨hY _ hy, ?_⟩ 
      by_contra! rfl
      exact hx.right hy
    specialize ih ⟨n, X'_card⟩ Y_subset X'_card 
    refine ⟨ih.left, ih.right.trans ?_⟩ 
    rw [has_card_to_card X'_card, has_card_to_card hn]
    exact Nat.le_add_right _ _

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY_ssubset: Y ⊂ X) :
  Y.card < X.card := by
    have ⟨hY_subset, hXY⟩  : Y ⊆ X ∧ Y ≠ X := hY_ssubset
    replace ⟨hY, card_le⟩ := card_subset hX hY_subset
    refine Nat.lt_of_le_of_ne card_le ?_
    let Z := X \ Y
    have hZY_eq : Z ∪ Y = X := by 
      rw [union_comm]
      exact union_compl hY_subset
    have hZ_subset : Z ⊆ X := fun _ h => mem_sdiff _ _ _ |>.mp h |>.left
    have hZ : Z.finite := (card_subset hX hZ_subset).left
    have hZY_disj : Disjoint Z Y := by simp [disjoint_iff, Z, Set.ext_iff]
    have Z_card : Z.card ≠ 0 := by
      by_contra! h
      have : Z = ∅ := empty_iff_card_eq_zero.mpr ⟨hZ, h⟩ 
      rw [this, empty_union] at hZY_eq
      exact hXY hZY_eq
    replace := hZY_eq ▸ card_union_disjoint hZ hY hZY_disj
    contrapose! Z_card
    rwa [Z_card, Nat.right_eq_add] at this

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) : (f: X → Y) →
  (image f X).finite ∧ (image f X).card ≤ X.card := by
    apply induction_insert hX
    · intro f; simp
    intro x X hX hx ih f
    let f' (x: X): Y := f ⟨x.val, mem_union _ _ _ |>.mpr (Or.inl x.prop)⟩ 
    specialize ih f'
    let fx := f ⟨x, mem_union _ _ _ |>.mpr (Or.inr (mem_singleton _ _ |>.mpr rfl))⟩
    have hF : (image f' X) ∪ {fx.val} = image f (X ∪ {x}) := by
        ext x'; simp [f', fx]
        constructor
        · rintro (⟨a, ha, hfa⟩|h)
          exact ⟨a, Or.inl ha, hfa⟩ 
          exact ⟨x, Or.inr rfl, h.symm⟩ 
        · rintro ⟨a, ha|rfl, hfa⟩
          exact Or.inl ⟨a, Exists.intro ha hfa⟩ 
          exact Or.inr hfa.symm
    by_cases hfx : fx.val ∈ (image f' X)
    · replace hF : (image f' X) = image f (X ∪ {x}) := by
        rwa [union_subset] at hF
        exact fun a ha => (mem_singleton _ _ |>.mp ha) ▸ hfx
      refine hF ▸ ⟨ih.left, ih.right.trans ?_⟩ 
      rw [card_insert hX hx |>.right]
      exact Nat.le_add_right _ _
    replace := card_insert ih.left hfx
    rw [← hF]
    refine ⟨this.left, this.right ▸ ?_⟩ 
    rw [card_insert hX hx |>.right]
    exact Nat.add_le_add_right ih.right _


/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) : {f: X → Y} →
  (hf: Function.Injective f) → (image f X).card = X.card := by
    apply induction_insert hX
    · intro f hf; simp
    intro x X hX hx ih f hf
    let f' (x: X): Y := f ⟨x.val, mem_union _ _ _ |>.mpr (Or.inl x.prop)⟩ 
    have f'_injective : Function.Injective f' := by
      intro a b h
      replace h := hf h
      simpa [coe_inj] using h
    specialize ih f'_injective
    let fx := f ⟨x, mem_union _ _ _ |>.mpr (Or.inr (mem_singleton _ _ |>.mpr rfl))⟩
    have f'_image_card := card_image hX f' 
    have hF : (image f' X) ∪ {fx.val} = image f (X ∪ {x}) := by
      ext x'; simp [f', fx]
      constructor
      · rintro (⟨a, ha, hfa⟩|h)
        exact ⟨a, Or.inl ha, hfa⟩ 
        exact ⟨x, Or.inr rfl, h.symm⟩ 
      · rintro ⟨a, ha|rfl, hfa⟩
        exact Or.inl ⟨a, Exists.intro ha hfa⟩ 
        exact Or.inr hfa.symm
    have hfx : fx.val ∉ (image f' X) := by
      by_contra hfx
      replace ⟨x', hx', hfx⟩ := mem_image _ _ _ |>.mp hfx
      simp [coe_inj, fx] at hfx
      replace hfx := hf hfx |> Subtype.mk.inj
      exact (hfx ▸ hx) hx'
    rw [← hF, 
      card_insert f'_image_card.left hfx |>.right,
      card_insert hX hx |>.right,
      ih
    ]

@[simp]
theorem SetTheory.Set.empty_prod (X: Set) : empty ×ˢ X = empty := by
  ext x
  simp

@[simp]
theorem SetTheory.Set.prod_empty (X: Set) : X ×ˢ empty = empty := by
  ext x
  simp

@[simp]
theorem SetTheory.Set.disjoint_prod {X Y Z: Set} (hZ: Z ≠ ∅) : Disjoint X Y ↔ Disjoint (X ×ˢ Z) (Y ×ˢ Z) := by
  simp_rw [disjoint_iff, eq_empty_iff_forall_notMem, mem_inter, mem_cartesian, ← not_exists, not_iff_not]
  constructor
  · intro ⟨x, hX, hY⟩
    have z := nonempty_choose hZ
    exact ⟨OrderedPair.mk x z.val, ⟨⟨x, hX⟩, z, rfl⟩, ⟨⟨x, hY⟩, z, rfl⟩⟩
  · rintro ⟨x, ⟨a, z1, ha⟩, ⟨b, z2, hb⟩⟩ 
    rw [hb, OrderedPair.toObject.injective.eq_iff, OrderedPair.eq] at ha
    exact ⟨a.val, a.prop, ha.left ▸ b.prop⟩ 

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
  (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
    by_cases hY_nonempty : Y = ∅
    · subst Y; simp
    apply induction_insert hX
    · simp
    intro x X hX hx ih
    rw [union_prod]
    have card_singleton_prod : ∀x {X: Set}, X.finite → (({x}: Set) ×ˢ X).has_card X.card := by
      intro x X hX
      obtain ⟨f, hf⟩ := has_card_card hX |> (has_card_iff _ _).mp
      refine has_card_iff _ _ |>.mpr ⟨(f <| snd ·), ?_, ?_⟩
      · intro ⟨a, ha⟩ ⟨b, hb⟩ h
        obtain ⟨a1, a2, rfl⟩ := mem_cartesian _ _ _ |>.mp ha
        obtain ⟨b1, b2, rfl⟩ := mem_cartesian _ _ _ |>.mp hb
        replace h := hf.injective h
        simp only [snd_of_mk_cartesian] at h
        have : a1 = b1 := by
          have ha := a1.prop |> (mem_singleton _ _ |>.mp)
          have hb := b1.prop |> (mem_singleton _ _ |>.mp)
          simpa only [← hb, coe_inj] using ha
        simp [h, this]
      · intro m
        obtain ⟨y, hy⟩ := hf.surjective m
        use (mk_cartesian ⟨x, mem_singleton _ _ |>.mpr rfl⟩ y)
        simp [snd_of_mk_cartesian, hy]
    have x_xs_Y_card := card_singleton_prod x hY
    refine ⟨card_union ih.left ⟨_, x_xs_Y_card⟩ |>.left, ?_⟩ 
    have := disjoint_iff X {x} |>.mpr (eq_empty_iff_forall_notMem.mpr (by 
      intro x'
      simp
      exact fun h h' => hx (h' ▸ h)
    ))
    replace := disjoint_prod hY_nonempty |>.mp this
    replace := card_union_disjoint ih.left ⟨_, x_xs_Y_card⟩  this
    rw [this, has_card_to_card x_xs_Y_card, 
      ih.right, card_insert hX hx |>.right, 
      Nat.succ_mul]

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun := fun x => powerset_axiom _ |>.mp x.prop |>.choose
  invFun := fun x => ⟨coe_of_fun x, powerset_axiom _ |>.mpr ⟨x, rfl⟩⟩
  left_inv x := by
    generalize_proofs _ h
    simp [h x |>.choose_spec]
  right_inv x := by simp

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

theorem SetTheory.Set.empty_pow (hX : X ≠ empty) : empty ^ X = empty := by
  ext x
  simp
  intro f
  exact (not_mem_empty _) (f (nonempty_choose hX)).prop |>.elim

@[simp]
theorem SetTheory.Set.pow_empty {Y : Set} : 
  Y ^ empty = {coe_of_fun (X := empty) (Y := Y) fun x => (not_mem_empty _) x.prop |>.elim} := by
  simp [Set.ext_iff]
  refine fun f => ⟨?_, ?_⟩ 
  · rintro ⟨f, rfl⟩ 
    rw [coe_of_fun_inj]
    ext x
    exact (not_mem_empty _) x.prop |>.elim
  · exact fun h => by simp [h]

example {a b: Prop} (h: ¬a) : a ∨ b ↔ b := or_iff_right h
example {f g: α → β} (h: (fun x => f x) = fun x => g x) : f y = g y  := by exact congrFun h y

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
    suffices (Y ^ X).has_card (Y.card ^ X.card) from ⟨⟨_, this⟩, has_card_to_card this⟩
    apply induction_insert hX
    · rw [pow_empty, empty_card_eq_zero, pow_zero]; exact singleton_has_card _
    intro x X hX hx ih
    rw [card_insert hX hx |>.right, pow_succ]
    have : ((Y ^ X) ×ˢ Y).has_card (Y.card ^ X.card * Y.card) := by
      have := card_prod ⟨_, ih⟩ hY
      apply card_to_has_card' this.left
      rw [this.right, has_card_to_card ih]
    apply Setoid.trans ?_ this
    let x': (X ∪ {x}).toSubtype := ⟨x, mem_union _ _ _ |>.mpr (Or.inr <| mem_singleton _ _ |>.mpr rfl)⟩
    refine ⟨fun z =>
      mk_cartesian (pow_fun_equiv.symm fun x => 
        (pow_fun_equiv z ⟨x, mem_union _ _ _ |>.mpr (Or.inl x.prop)⟩)
      ) (pow_fun_equiv z x')
    , ?_, ?_⟩
    · intro a b h
      simp [mk_cartesian, coe_inj] at h
      apply Equiv.injective pow_fun_equiv
      ext y
      by_cases hy : y.val ∈ X 
      · replace h := congrFun h.left ⟨y, hy⟩
        exact congrArg Subtype.val h
      · have : y.val = x := mem_union _ _ _ |>.mp y.prop |> (or_iff_right hy).mp |> (mem_singleton _ _).mp
        exact (coe_inj _ y x').mp this ▸ h.right ▸ rfl
    · intro ⟨_, h⟩
      obtain ⟨yx, y, rfl⟩ := mem_cartesian _ _ _ |>.mp h
      use pow_fun_equiv.symm fun x' => by
        if h : x'.val ∈ X then exact pow_fun_equiv yx ⟨x', h⟩ 
        else exact y
      simp [mk_cartesian, coe_inj]
      constructor
      · apply pow_fun_equiv.injective
        ext x
        rw [Equiv.apply_symm_apply, if_pos x.prop]
      · exact fun h ↦ (hx h).elim

/-- Exercise 3.6.5. You might find `SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
  EqualCard (A ×ˢ B) (B ×ˢ A) := by
    use prod_commutator A B
    exact Equiv.bijective (A.prod_commutator B)

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

def EquivReturn {A B C: Sort*} (b_equiv_c: B ≃ C) : (A → B) ≃ (A → C) where
  toFun f a := b_equiv_c (f a)
  invFun f a := b_equiv_c.symm (f a)
  left_inv f := by simp
  right_inv f := by simp

def EquivSwapArgs {A B C: Sort*} : (A → B → C) ≃ (B → A → C) where
  toFun f b a := f a b
  invFun f a b := f b a
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exercise 3.6.6. You may find `SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
  EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
    use pow_fun_equiv' (A ^ B) C 
      |>.trans (EquivReturn (pow_fun_equiv' A B))
      |>.trans EquivSwapArgs 
      |>.trans curry_equiv
      |>.trans pow_fun_equiv.symm
    exact Equiv.bijective _


theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by
  have hA_B := card_pow (Fin_finite a) (Fin_finite b)
  have hA_B_C := card_pow hA_B.left (Fin_finite c)
  have hBC := card_prod (Fin_finite b) (Fin_finite c)
  have hA_BC := card_pow (Fin_finite a) hBC.left
  rw [
    ← Fin_card a, ← Fin_card b, ← Fin_card c, 
    ← hA_B.right, ← hA_B_C.right, 
    ← hBC.right, ← hA_BC.right, 
    EquivCard_to_card_eq]
  exact pow_pow_EqualCard_pow_prod _ _ _

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
  EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by
    replace hd: ∀x, x ∈ C → x ∉ B := by 
      rw [disjoint_comm] at hd
      simpa [disjoint_iff, eq_empty_iff_forall_notMem] using hd
    refine ⟨fun a => by
      have fb := pow_fun_equiv (fst a)
      have fc := pow_fun_equiv (snd a)
      exact pow_fun_equiv.symm fun bc => by
        if hbc: bc.val ∈ B then 
          exact fb ⟨bc, hbc⟩
        else 
          replace hbc := mem_union _ _ _ |>.mp bc.prop |>.elim
            (fun h => hbc h |>.elim)
            (fun h => h)
          exact fc ⟨bc, hbc⟩
      , ?_, ?_⟩
    · intro ⟨a,ha⟩ ⟨b,hb⟩ h
      obtain ⟨a1, a2, rfl⟩ := mem_cartesian _ _ _ |>.mp ha
      obtain ⟨b1, b2, rfl⟩ := mem_cartesian _ _ _ |>.mp hb
      simp [coe_inj] at ⊢ h
      have h1 : pow_fun_equiv a1 = pow_fun_equiv b1 := by
        ext b
        have : b.val ∈ (B ∪ C) := mem_union _ _ _ |>.mpr (Or.inl b.prop)
        replace h := congrArg (· ⟨b, this⟩) h
        simp [dif_pos b.prop] at h
        rw [h]
      have h2 : pow_fun_equiv a2 = pow_fun_equiv b2 := by
        ext c
        have : c.val ∈ (B ∪ C) := mem_union _ _ _ |>.mpr (Or.inr c.prop)
        replace h := congrArg (· ⟨c, this⟩) h
        simp [dif_neg <| hd _ c.prop] at h
        rw [h]
      simp [h1, h2, pow_fun_eq_iff]
    · intro ⟨f, hf⟩
      obtain ⟨f, rfl⟩ := powerset_axiom _ |>.mp hf
      let fb (b: B): A := f ⟨b, mem_union _ _ _ |>.mpr (Or.inl b.prop)⟩
      let fc (c: C): A := f ⟨c, mem_union _ _ _ |>.mpr (Or.inr c.prop)⟩
      use mk_cartesian (pow_fun_equiv.symm fb) (pow_fun_equiv.symm fc)
      simp [pow_fun_equiv]
      funext bc
      generalize_proofs hfb hfc
      split_ifs with h'
      · rw [coe_of_fun_inj _ _ |>.mp hfb.choose_spec]
      · rw [coe_of_fun_inj _ _ |>.mp hfc.choose_spec]

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by
  let B := (Fin b).replace (P := fun b y => ((b: ℕ) + c: Object) = y) (by simp)
  have mem_B (b': Fin b) : ((b': ℕ) + c: Object) ∈ B := replacement_axiom _ _ |>.mpr ⟨b', rfl⟩
  have disj_B_C : Disjoint B (Fin c) := by
    rw [disjoint_iff, inter_comm, eq_empty_iff_forall_notMem]
    intro x
    rw [mem_inter, not_and, mem_Fin]
    rintro ⟨x, hx, rfl⟩
    simp [B]
    intro y hy h
    obtain ⟨y, rfl⟩ : ∃n: ℕ, y = ↑n := ⟨(Subtype.mk y hy : ℕ), Object.ofnat_eq'' ▸ rfl⟩
    simp at h
    omega
  have B_card : B.has_card b := by
    apply Setoid.symm
    refine ⟨fun b => ⟨_, mem_B b⟩, ?_, ?_⟩
    · intro x y h
      simpa [coe_inj] using h
    · intro x
      obtain ⟨b', hb'⟩ := replacement_axiom _ _ |>.mp x.prop
      have : x = ⟨↑(↑b' + c), hb' ▸ x.prop⟩ := coe_inj _ _ _ |>.mp hb'.symm
      simp [this]
  have hA_B := card_pow (Fin_finite a) ⟨_, B_card⟩
  have hA_C := card_pow (Fin_finite a) (Fin_finite c)
  have hA_B_C := card_pow hA_B.left (Fin_finite c)
  rw [
    ← Fin_card a, ← has_card_to_card B_card, ← Fin_card c, 
    ← hA_B.right, ← hA_C.right, ← (card_prod hA_B.left hA_C.left).right,
    ← card_union_disjoint ⟨_, B_card⟩ (Fin_finite c) disj_B_C,
    ← card_pow (Fin_finite a) (card_union ⟨_, B_card⟩ (Fin_finite c)).left |>.right,
    EquivCard_to_card_eq]
  exact pow_prod_pow_EqualCard_pow_union _ _ _ disj_B_C

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
  (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := by
    constructor
    · intro ⟨f, hf⟩
      rw [← card_image_inj hA hf]
      apply card_subset hB (image_in_codomain _ _) |>.right
    intro h
    obtain ⟨n, hn⟩ := hA
    obtain rfl := has_card_to_card hn
    obtain ⟨f, hf⟩ := hn
    obtain ⟨m, hm⟩ := hB
    obtain rfl := has_card_to_card hm
    obtain ⟨g, hg⟩ := hm
    refine ⟨fun a => Fin_embed A.card B.card h (f a) |> hg.surjective |>.choose, ?_⟩
    intro x y h
    simp at h
    generalize_proofs hx hy at h
    have := hy.choose_spec
    rw [← h, hx.choose_spec, ← Fin.coe_inj] at this
    exact hf.injective this

theorem SetTheory.Set.empty_inter (A: Set) : ∅ ∩ A = ∅ := by simp [Set.ext_iff]

theorem SetTheory.Set.empty_sdiff (A: Set) : ∅ \ A = ∅ := by simp [Set.ext_iff]

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
    have : Nonempty A := ⟨nonempty_choose hA⟩
    refine ⟨Function.invFun f, fun a => ⟨f a, ?_⟩⟩
    exact hf Function.apply_invFun_apply

theorem SetTheory.Set.inter_finite {A B:Set} (hA: A.finite)
  : (A ∩ B).finite := by
    apply induction_insert hA
    · simp [empty_inter]
    intro x X hX hx ih
    rw [show ((X ∪ {x}) ∩ B) = X ∩ B ∪ {x} ∩ B by simp [Set.ext_iff]; tauto]
    refine card_union ih ?_ |>.left
    by_cases h: x ∈ B
    · rw [show {x} ∩ B = {x} by simp [Set.ext_iff]; tauto]
      exact ⟨_, singleton_has_card _⟩
    · rw [show {x} ∩ B = ∅ by simp [Set.ext_iff]; tauto]
      exact finite_of_empty rfl

theorem SetTheory.Set.sdiff_finite {A B:Set} (hA: A.finite)
  : (A \ B).finite := by
    apply induction_insert hA
    · simp [empty_sdiff]
    intro x X hX hx ih
    rw [show ((X ∪ {x}) \ B) = X \ B ∪ {x} \ B by simp [Set.ext_iff]; tauto]
    refine card_union ih ?_ |>.left
    by_cases h: x ∈ B
    · rw [show {x} \ B = ∅ by simp [Set.ext_iff]; tauto]
      exact finite_of_empty rfl
    · rw [show {x} \ B = {x} by simp [Set.ext_iff]; tauto]
      exact ⟨_, singleton_has_card _⟩

theorem SetTheory.Set.partition_sdiff_inter (A B: Set) : A = A \ B ∪ A ∩ B := by 
    simp [Set.ext_iff, ← and_or_left]
    exact fun _ _ => or_comm.eq ▸ Classical.em _

theorem SetTheory.Set.disjoint_union {A B C: Set} 
  (hAC: Disjoint A C) (hBC: Disjoint B C) : Disjoint (A ∪ B) C := by
    rw [disjoint_iff] at *
    rw [show (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) by simp [Set.ext_iff]; tauto, hAC, hBC, empty_union]

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by 
    nth_rw 1 [union_eq_partition, partition_sdiff_inter B A, partition_sdiff_inter A B]
    rw [
      card_union_disjoint (sdiff_finite hB) (inter_finite hB) disjoint_sdiff_inter,
      inter_comm B A,
      card_union_disjoint (card_union (sdiff_finite hA) (inter_finite hA)).left (sdiff_finite hB),
      add_assoc
    ]
    refine disjoint_union disjoint_sdiff_sdiff ?_
    rw [disjoint_comm, inter_comm]
    exact disjoint_sdiff_inter

theorem SetTheory.Set.iUnion_union {I I' J: Set} {A} (hJ: J = I ∪ I'):
  J.iUnion A = I.iUnion (fun i => A ⟨i.val, hJ ▸ mem_union _ _ _ |>.mpr (Or.inl i.prop)⟩) ∪
    I'.iUnion (fun i => A ⟨i.val, hJ ▸ mem_union _ _ _ |>.mpr (Or.inr i.prop)⟩) := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨⟨i, hi⟩, hx⟩
      by_cases hj : i ∈ I
      · refine Or.inl ⟨⟨i, hj⟩, ?_⟩
        simpa
      replace hj : i ∈ I' := mem_union _ _ _ |>.mp (hJ ▸ hi) |>.elim (hj · |>.elim) id
      refine Or.inr ⟨⟨i, hj⟩, ?_⟩
      simpa
    rintro (⟨⟨j, hj⟩, hx⟩|⟨⟨j, hj⟩, hx⟩)
    · exact ⟨⟨j, hJ ▸ mem_union _ _ _ |>.mpr (Or.inl hj)⟩, hx⟩
    · exact ⟨⟨j, hJ ▸ mem_union _ _ _ |>.mpr (Or.inr hj)⟩, hx⟩

theorem SetTheory.Set.iUnion_singleton {x: Object} {A} :
    iUnion {x} A = A ⟨x, mem_singleton _ _ |>.mpr rfl⟩ := by
      ext y
      rw [mem_iUnion]
      constructor
      · rintro ⟨⟨x, hx⟩, ha⟩
        exact (mem_singleton _ _ |>.mp hx) ▸ ha
      exact fun ha => ⟨⟨x, mem_singleton _ _ |>.mpr rfl⟩, ha⟩

theorem SetTheory.Set.iUnion_finite {I: Set} (hI: I.finite) {A : I → Set}  (hA: ∀ i, (A i).finite) :
  (I.iUnion A).finite := by
    revert A; apply induction_insert hI
    · intro A; simp [iUnion_of_empty]
    intro x X hX hx ih A hA
    simp [iUnion_union rfl]
    apply card_union (ih ?_) ?_ |>.left
    · intro ⟨i, hi⟩
      simp [hA ⟨i, mem_union _ _ _ |>.mpr (Or.inl hi)⟩]
    simp [iUnion_singleton, hA ⟨x, mem_union _ _ _ |>.mpr (Or.inr <| mem_singleton _ _ |>.mpr rfl)⟩]

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
    induction' n with n ih
    · have : Fin 0 = ∅ := has_card_zero.mp (Setoid.refl _)
      simp [this ▸ iUnion_of_empty, this] at hAcard
    let n' := (Fin_mk n.succ n (lt_add_one _))
    by_cases hn_card : (A n').card ≥ 2
    · exact ⟨n', hn_card⟩
    replace hn_card : (A n').card = 0 ∨ (A n').card = 1  := by
      have : (A n').card < 2 := by exact Nat.lt_of_not_le hn_card
      replace : (A n').card ≤ 1 := by exact Nat.le_of_lt_succ this
      exact Nat.le_one_iff_eq_zero_or_eq_one.mp this
    let A' (n': Fin n): Set := A (Fin_embed n n.succ (Nat.le_succ n) n')
    have hA' : ∀ i, (A' i).finite := by simp [A', hA]
    have : Fin n.succ = (Fin n) ∪ {(n: Object)} := by
      simp only [Nat.succ_eq_add_one, Set.ext_iff, mem_union, mem_singleton, mem_Fin]
      have (x y: ℕ) : (x: Object) = (y: Object) → x = y := by 
        exact fun a ↦ (fun [SetTheory] n m ↦ (ofNat_inj' n m).mp) x y a
      intro x
      constructor
      · rintro ⟨m, hm, rfl⟩
        by_cases hm_eq : m = n
        · simp [hm_eq]
        refine Or.inl ⟨m, ?_, rfl⟩
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hm) hm_eq
      · rintro (⟨m, hm, rfl⟩|rfl) <;> simp
        exact hm.le
    have hA'card := hAcard
    rw [iUnion_union this] at hA'card
    replace hA'card := lt_of_lt_of_le hA'card (card_union 
      (iUnion_finite (Fin_finite n) fun i => hA (Fin_embed n n.succ (Nat.le_succ _) i))
      (iUnion_finite ⟨_, singleton_has_card _⟩ fun ⟨x, hx⟩ => 
        have := mem_singleton _ _ |>.mp hx
        hA ⟨x, mem_Fin _ _ |>.mpr ⟨n, lt_add_one n, this⟩⟩)
      ).right
    replace hA'card : n  < ((Fin n).iUnion fun i ↦ A (Fin_embed n n.succ (Nat.le_succ _) i)).card := by
      rcases hn_card with hn|hn
      · rw [iUnion_singleton, hn] at hA'card
        exact lt_of_le_of_lt (Nat.le_succ _) hA'card
      · rw [iUnion_singleton, hn] at hA'card
        exact Nat.succ_lt_succ_iff.mp hA'card
    obtain ⟨i, hi⟩ := ih hA' hA'card
    exact ⟨Fin_embed n n.succ (Nat.le_succ _) i, hi⟩

theorem SetTheory.Set.sdiff_of_singleton_mem {X Y: Set} {x: X} (hX: X \ {x.val} = Y) : Y ∪ {x.val} = X := by
  simp [← hX, Set.ext_iff]
  refine fun y => ⟨?_, ?_⟩
  · rintro (hy|hy)
    exact hy.left
    exact hy ▸ x.prop
  · rintro hy
    by_cases hx : y = x.val
    exact Or.inr hx
    exact Or.inl ⟨hy, hx⟩

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
      constructor
      · intro hf S hS hS_card
        replace hS_card: S.has_card 2 := card_to_has_card (Nat.zero_ne_add_one _).symm hS_card
        obtain ⟨x, y, hS_pair, hxy⟩ : ∃(x y: S), S = {x.val, y.val} ∧ x ≠ y := by
          let x := nonempty_choose fun h => by
            have := card_uniq hS_card (has_card_zero.mpr h)
            contradiction
          replace : (S \ {↑x}).has_card 1 := card_erase (Nat.le_succ _) hS_card x
          let y := nonempty_choose fun h => by
            have := card_uniq this (has_card_zero.mpr h)
            contradiction
          replace : ((S \ {↑x}) \ {↑y}) = ∅ := has_card_zero.mp <| card_erase (Nat.le_refl _) this y
          replace := empty_union _ ▸ sdiff_of_singleton_mem this 
            |>.symm |> sdiff_of_singleton_mem
            |>.symm
          replace : S = {↑x, ↑y} := by simp [Set.ext_iff, this, or_comm]
          refine ⟨x, ⟨y.val, mem_sdiff _ _ _ |>.mp y.prop |>.left⟩, this, ?_⟩
          replace := mem_singleton _ _ |>.eq ▸ (mem_sdiff _ _ _ |>.mp y.prop |>.right)
          exact Subtype.coe_ne_coe.mp fun a ↦ this a.symm
        rw [hS_pair,  image_pair (hS _ x.prop) (hS _ y.prop)]
        refine has_card_to_card <| pair_has_card ?_
        by_contra h
        simp [coe_inj, hf.eq_iff, hxy] at h
      intro hS x y h
      by_cases hxy : x = y
      · exact hxy
      have : {x.val, y.val} ⊆ X := by
        intro x' hx'
        obtain rfl|rfl := mem_pair _ _ _ |>.mp hx'
        exact x.prop
        exact y.prop
      specialize hS _ this (has_card_to_card <| pair_has_card <| Subtype.coe_ne_coe.mpr hxy)
      rw [image_pair x.prop y.prop, h, pair_self] at hS
      replace hS : ({↑(f y)}: Set).has_card 2 := card_to_has_card (Nat.zero_ne_add_one _).symm hS
      replace hS := card_uniq (hS) (singleton_has_card _)
      contradiction


          



/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by sorry

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by sorry

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by sorry

/-- This connects our concept of a permutation with Mathlib's `Equiv` between `Fin n` and `Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any `Fin n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by sorry

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by sorry

/-- Any `Fin (n + 1)` except `n` can be cast to `Fin n`. Compare to Mathlib `Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by sorry

/-- Any natural `n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by sorry

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some `x : Fin (n+1)` is never equal to `i`, we can shrink it into `Fin n` by shifting all `x > i` down by one.
  Compare to Mathlib `Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by sorry)
  else
    Fin_mk _ ((x:ℕ) - 1) (by sorry)

/--
  We can expand `x : Fin n` into `Fin (n + 1)` by shifting all `x ≥ i` up by one.
  The output is never `i`, so it forms an inverse to the shrinking done by `predAbove`.
  Compare to Mathlib `Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by sorry) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by sorry)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by sorry

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by sorry

/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    -- Hint: you might find `perm_equiv_equiv`, `Fin.succAbove`, and `Fin.predAbove` useful.
    have equiv : S i ≃ Permutations n := sorry
    use equiv, equiv.injective, equiv.surjective

  -- Hint: you might find `card_iUnion_card_disjoint` and `Permutations_finite` useful.
  sorry

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by sorry

/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
