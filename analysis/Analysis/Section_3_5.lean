import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as `Set.pi` and `Set.prod`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used `Object × Object` to
define `OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
  a = c ∧ b = c := by
    constructor
    · intro h
      replace h := Set.ext_iff.mp h
      exact ⟨
        h a |>.mp (mem_pair _ _ _ |>.mpr (Or.inl rfl)) |> (mem_singleton _ _ |>.mp),
        h b |>.mp (mem_pair _ _ _ |>.mpr (Or.inr rfl)) |> (mem_singleton _ _ |>.mp)
      ⟩
    rintro ⟨rfl, rfl⟩ 
    exact pair_self _


open SetTheory in
/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    simp_all
    obtain ⟨h1,h2⟩|⟨h1,h2⟩ := pair_eq_iff.mp h
    all_goals
      clear h
      apply Function.Embedding.injective set_to_object at h1
      apply Function.Embedding.injective set_to_object at h2
    · obtain rfl := singleton_eq_iff.mp h1
      obtain rfl := pair_eq_iff'.mp h2
      exact ⟨rfl, rfl⟩ 
    · replace h1 := pair_eq_singleton_iff.mp h1.symm
      replace h2 := pair_eq_singleton_iff.mp h2
      refine ⟨h1.left.symm, h2.right.trans h1.left |>.trans h1.right.symm⟩ 

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = 
    Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)
  ) (by grind))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  . intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ x, hx ⟩ := hS
    use x; simp_all
  rintro ⟨ x, y, rfl ⟩
  use Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)
  refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

@[simp]
theorem SetTheory.Set.cartesian_empty_iff { X Y:Set } :
  X ×ˢ Y = ∅ ↔ X = ∅ ∨ Y = ∅ := by
    simp_rw [eq_empty_iff_forall_notMem, mem_cartesian, not_exists]
    constructor
    · intro h
      by_contra! h'
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h'
      apply h (OrderedPair.mk x y) ⟨x, hx⟩ ⟨y, hy⟩  
      rfl
    rintro (h|h) x f s
    exact absurd f.prop (h f.val) 
    exact absurd s.prop (h s.val) 

@[simp]
theorem SetTheory.Set.cartesian_nonempty_iff { X Y:Set } :
  X ×ˢ Y ≠ ∅ ↔ X ≠ ∅ ∧ Y ≠ ∅ := by
    apply not_iff_not.mp
    rw [Classical.not_and_iff_not_or_not]
    push_neg
    exact cartesian_empty_iff

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ fst z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, snd z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

/-- This equips an `OrderedPair` with proofs that `x ∈ X` and `y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ fst z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', snd z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

/--
  Connections with the Mathlib set product, which consists of Lean pairs like `(x, y)`
  equipped with a proof that `x` is in the left set, and `y` is in the right set.
  Lean pairs like `(x, y)` are similar to our `OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between `X ×ˢ Y` and `Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun z := mk_cartesian (snd z) (fst z)
  invFun z := mk_cartesian (snd z) (fst z)
  left_inv z := by simp
  right_inv z := by simp

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f (mk_cartesian x y)
  left_inv _ := by simp
  right_inv _ := by simp

/-- Definition 3.5.6.  The indexing set `I` plays the role of `{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections betweeen this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)

/-- Definition 3.5.6 -/
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  . intro ⟨ ht, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
  tuple x = tuple y ↔ x = y := by
    refine ⟨?_, fun h => h ▸ rfl⟩ 
    intro h
    funext i
    rw [coe_of_fun_inj, funext_iff] at h
    replace h := Subtype.mk.injEq _ _ _ _ ▸ h i
    exact (coe_inj _ _ _).mp h


/-- Example 3.5.8. There is a bijection between `(X ×ˢ Y) ×ˢ Z` and `X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun z := mem_iProd z.val |>.mp z.prop |>.choose ⟨i, mem_singleton _ _ |>.mpr rfl⟩ 
  invFun z := by
    refine ⟨tuple (fun _:({i}:Set) => z), ?_⟩ 
    rw [mem_iProd]
    use fun _ => z
  left_inv z := by
    let h := (mem_iProd _).mp z.property
    obtain ht := h.choose_spec
    ext
    rw [ht, tuple_inj]
    funext i'
    have : i' = ⟨i, mem_singleton _ _ |>.mpr rfl⟩ := by
      have : i = ↑i' := mem_singleton _ _ |>.mp i'.prop |>.symm
      simp [this]
    simp [this]
  right_inv  := fun ⟨x, hx⟩ => by
    dsimp only
    generalize_proofs h
    rw [← tuple_inj _ _ |>.mp h.choose_spec]

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨tuple (absurd ·.prop (not_mem_empty _)), tuple_mem_iProd _⟩ 
  left_inv x := by
    dsimp only
    ext
    obtain ⟨t, ht⟩ := mem_iProd _ |>.mp x.prop
    rw [ht, tuple_inj]
    funext x
    apply absurd x.prop (not_mem_empty _)
  right_inv x := rfl


/- open Classical in -/
/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun t :=
    let x := ((mem_iProd _).mp t.property).choose
    mk_cartesian (x ⟨0, by simp⟩) (x ⟨1, by simp⟩)
  invFun := fun z ↦ ⟨tuple (X:=X) (fun i ↦ by
    if h0 : i = ⟨0, by simp⟩ then rw [h0]; exact (fst z)
    else if h1 : i = ⟨1, by simp⟩ then rw [h1]; exact (snd z)
    else exact absurd (subtype_pair i |>.resolve_left h0) h1
  ), by apply tuple_mem_iProd⟩
  left_inv t := by
    have h := (mem_iProd _).mp t.property
    have ht := h.choose_spec
    ext
    rw [ht, tuple_inj]
    ext i
    if h0 : i = ⟨0, by simp⟩ then
      rw [dif_pos h0, fst_of_mk_cartesian]
      subst h0
      rw [eq_mpr_eq_cast, cast_eq]
    else if h1 : i = ⟨1, by simp⟩ then
      rw [dif_neg h0, dif_pos h1, snd_of_mk_cartesian]
      subst h1
      rw [eq_mpr_eq_cast, cast_eq]
    else exact absurd (subtype_pair i |>.resolve_left h0) h1
  right_inv x := by
    dsimp only []
    generalize_proofs _ _ _ _ _ h
    simp [← tuple_inj _ _ |>.mp h.choose_spec]

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun t :=
    let x := ((mem_iProd _).mp t.property).choose
    mk_cartesian (x ⟨0, by simp⟩) <| mk_cartesian (x ⟨1, by simp⟩) (x ⟨2, by simp⟩)
  invFun := fun z ↦ ⟨tuple (X:=X) (fun i ↦ by
    if h0 : i = ⟨0, by simp⟩ then rw [h0]; exact (fst z)
    else if h1 : i = ⟨1, by simp⟩ then rw [h1]; exact fst (snd z)
    else if h2 : i = ⟨2, by simp⟩ then rw [h2]; exact snd (snd z)
    else exact absurd (subtype_triple i |>.resolve_left h0 |>.resolve_left h1) h2
  ), by apply tuple_mem_iProd⟩
  left_inv t := by
    have h := (mem_iProd _).mp t.property
    have ht := h.choose_spec
    ext
    rw [ht, tuple_inj]
    ext i
    if h0 : i = ⟨0, by simp⟩ then
      rw [dif_pos h0, fst_of_mk_cartesian]
      subst h0
      rw [eq_mpr_eq_cast, cast_eq]
    else if h1 : i = ⟨1, by simp⟩ then
      rw [dif_neg h0, dif_pos h1, snd_of_mk_cartesian, fst_of_mk_cartesian]
      subst h1
      rw [eq_mpr_eq_cast, cast_eq]
    else if h2 : i = ⟨2, by simp⟩ then
      rw [dif_neg h0, dif_neg h1, dif_pos h2, snd_of_mk_cartesian, snd_of_mk_cartesian]
      subst h2
      rw [eq_mpr_eq_cast, cast_eq]
    else exact absurd (subtype_triple i |>.resolve_left h0 |>.resolve_left h1) h2
  right_inv x := by
    dsimp only []
    generalize_proofs _ _ _ _ _ _ _ h
    simp [← tuple_inj _ _ |>.mp h.choose_spec]

/-- Connections with Mathlib's `Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [←(tuple_inj _ _).mp h.choose_spec]


/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib `Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  . intro ⟨ h1, h2 ⟩; use ↑(⟨ x, h1 ⟩:nat); simp [h2]
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m:nat).property)
  grind [Object.ofnat_eq''']

theorem SetTheory.Set.Fin_mem_exists (h: n ≠ 0) : ∃m, m ∈ Fin n := by
  use n.pred
  rw [mem_Fin]
  use n.pred
  simp [Nat.zero_lt_of_ne_zero h]

lemma SetTheory.Set.not_mem_Fin_0 {x : Object} : x ∉ Fin 0 := by
  intro h
  have ⟨m, hm, _⟩ := mem_Fin _ _ |>.mp h
  exact Nat.not_succ_le_zero m hm

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n:ℕ} {i j: Fin n} : i = j ↔ (i:ℕ) = (j:ℕ) := by
  constructor
  · simp_all
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n:ℕ} (i: Fin n) {j:ℕ} : (i:Object) = (j:Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [←Object.natCast_inj]
  aesop

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m:ℕ} (i: Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m):ℕ) = (i:ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose: Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at *; grind
⟩

/-- Connections with Mathlib's `Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/-- Lemma 3.5.11 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [←Fin.coe_toNat, last]
      ⟨a, by grind⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by 
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    replace h := Function.Embedding.injective _ h
    simp [pair_eq_iff] at h
    rw [OrderedPair.eq]
    rcases h with (⟨rfl, h|h⟩|⟨ha, hb⟩)
    · exact h
    · exact ⟨rfl, h.right.trans h.left⟩ 
    obtain ⟨a1, rfl⟩ : ∃(a: Set), a1 = ↑a := Exists.intro _ ha
    obtain ⟨b1, rfl⟩ : ∃(a: Set), b1 = ↑a := Exists.intro _ hb.symm
    replace ha := Function.Embedding.injective _ ha
    replace hb := Function.Embedding.injective _ hb
    simp at ha hb
    exact not_mem_mem a1 b1 |>.elim
      (fun h => h (hb ▸ mem_pair _ _ _ |>.mpr (Or.inl rfl)))
      (fun h => h (ha ▸ mem_pair _ _ _ |>.mpr (Or.inl rfl)))
      |>.elim

/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing `@[ext]` on the structure would generate a lemma requiring proof of `t.x = t'.x`,
  but these functions have different types when `t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; grind

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
  t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
    constructor
    · rintro rfl n
      rfl
    rintro h
    ext i
    constructor
    · intro hi
      have ⟨m, hm⟩ := t.surj ⟨i, hi⟩ 
      replace h := hm ▸ h m
      rw [show i = t'.x m from h]
      exact (t'.x m).prop
    · intro hi
      have ⟨m, hm⟩ := t'.surj ⟨i, hi⟩ 
      replace h := hm ▸ h m |>.symm
      rw [show i = t.x m from h]
      exact (t.x m).prop
    exact h i

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  toFun := fun ⟨x, hx⟩ => by
    have x := mem_iProd _ |>.mp hx |>.choose
    let X' := iUnion (Fin n) fun i => {(x i: Object)}
    refine ⟨Tuple.mk X' (fun i => ⟨x i, ?_⟩) ?_, ?_⟩ 
    · rw [mem_iUnion]
      use i
      simp
    · intro ⟨y, hy⟩ 
      obtain ⟨z, hz⟩ := mem_iUnion _ _ |>.mp hy
      use z
      rw [Subtype.mk.injEq]
      exact mem_singleton _ _ |>.mp hz |>.symm
    · intro i
      simp [x i |>.prop]
  invFun := fun ⟨t, ht⟩ => by
    let x (i: Fin n): X i := ⟨t.x i |>.val, ht i⟩ 
    refine ⟨tuple x, ?_⟩ 
    rw [mem_iProd]
    use x
  left_inv := by
    intro ⟨t, ht⟩  
    obtain ht := mem_iProd _ |>.mp ht
    simp only [Subtype.coe_eta, ← ht.choose_spec]
  right_inv := by
    intro ⟨t, ht⟩ 
    ext i
    dsimp only
    generalize_proofs h'
    have := tuple_inj _ _ |>.mp h'.choose_spec
    simp only [← this, mem_iUnion, mem_singleton]
    constructor
    · intro ⟨a,ha⟩ 
      exact ha ▸ (t.x a).prop
    · intro hi
      obtain ⟨a, ha⟩ := t.surj ⟨i, hi⟩ 
      use a, ha ▸ rfl
    simp
    generalize_proofs h'
    simp [← tuple_inj _ _ |>.mp h'.choose_spec]

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use `OrderedPair.eq` or `SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by
  rw [OrderedPair.eq]
  grind

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  rw [OrderedPair.eq, OrderedPair.eq]
  constructor; repeat
    intro ⟨h1, h2⟩ 
    exact And.intro h1.symm h2.symm

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p = q) (hqr: q = r) : p = r := by
  rw [OrderedPair.eq] at hpq hqr ⊢
  exact ⟨hpq.left.trans hqr.left, hpq.right.trans hqr.right⟩ 

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
  tuple a = tuple a := tuple_inj _ _ |>.mpr rfl

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
  tuple a = tuple b ↔ tuple b = tuple a := by
    rw [tuple_inj, tuple_inj, eq_comm]


theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by
      rw [tuple_inj] at hab hbc ⊢
      exact hab.trans hbc

/-- Exercise 3.5.4 -/
@[simp]
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  ext x
  simp_rw [mem_union, mem_cartesian]
  constructor
  · rintro ⟨x, ⟨y, hy⟩, rfl⟩ 
    rcases mem_union _ _ _ |>.mp hy with hy|hy
    exact Or.inl ⟨x, ⟨y, hy⟩, rfl⟩ 
    exact Or.inr ⟨x, ⟨y, hy⟩, rfl⟩ 
  · rintro (⟨x, y, rfl⟩|⟨x, y, rfl⟩ )
    exact ⟨x, ⟨y, (mem_union _ _ _).mpr (Or.inl y.prop)⟩, rfl⟩ 
    exact ⟨x, ⟨y, (mem_union _ _ _).mpr (Or.inr y.prop)⟩, rfl⟩ 


/-- Exercise 3.5.4 -/
@[simp]
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  ext x
  simp_rw [mem_inter, mem_cartesian]
  constructor
  · rintro ⟨x, ⟨y, hy⟩, rfl⟩ 
    exact ⟨
      ⟨x, ⟨y, mem_inter _ _ _  |>.mp hy |>.1⟩, rfl⟩,
      ⟨x, ⟨y, mem_inter _ _ _  |>.mp hy |>.2⟩, rfl⟩,
     ⟩ 
  rintro ⟨⟨x, ⟨y, hyB⟩, rfl⟩, ⟨x', ⟨y', hyC⟩, h⟩⟩
  replace h := OrderedPair.eq _ _ _ _ |>.mp (Function.Embedding.injective _ h)
  obtain rfl := Subtype.coe_inj.mp h.left
  obtain rfl: y = y' := h.right
  use x, ⟨y, mem_inter _ _ _ |>.mpr ⟨hyB, hyC⟩⟩ 

/-- Exercise 3.5.4 -/
@[simp]
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  ext x
  simp_rw [mem_sdiff, mem_cartesian, not_exists]
  constructor
  · rintro ⟨x, ⟨y, hy⟩, rfl⟩
    rw [mem_sdiff] at hy
    refine ⟨⟨x, ⟨y, hy.left⟩, rfl⟩, ?_⟩ 
    rintro x' y'
    by_contra h
    replace h : y = y' := OrderedPair.eq _ _ _ _ |>.mp (Function.Embedding.injective _ h) |>.right
    replace h := h ▸ y'.prop
    exact hy.right h
  rintro ⟨⟨x, ⟨y, hyB⟩, rfl⟩, h⟩ 
  by_cases hyC : y ∈ C
  · have := h x ⟨y, hyC⟩ 
    contradiction
  use x, ⟨y, mem_sdiff _ _ _ |>.mpr ⟨hyB, hyC⟩⟩ 

/-- Exercise 3.5.4 -/
@[simp]
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by aesop

/-- Exercise 3.5.4 -/
@[simp]
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by aesop

/-- Exercise 3.5.4 -/
@[simp]
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by aesop

/-- Exercise 3.5.5 -/
@[simp]
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
  (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by aesop
    


/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use {0}, {}, {}, {3}
  apply not_eq_iff.mpr
  use OrderedPair.mk 0 3
  simp

/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use {0}, {0, 1}, {0}, {}
  apply not_eq_iff.mpr
  use OrderedPair.mk 0 1
  simp

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) :
  A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
    constructor
    · intro h 
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩ 
      · have ⟨b, hb⟩ := nonempty_def hB
        replace h := h (OrderedPair.mk x b) (by simp [hx, hb])
        replace ⟨x', _, h⟩  := mem_cartesian _ _ _ |>.mp h
        have : x = x'.val := 
          Function.Embedding.injective OrderedPair.toObject h 
          |> (OrderedPair.eq _ _ _ _ |>.mp)
          |>.left
        exact this ▸ x'.prop
      · have ⟨a, ha⟩ := nonempty_def hA
        replace h := h (OrderedPair.mk a x) (by simp [hx, ha])
        replace ⟨_, x', h⟩  := mem_cartesian _ _ _ |>.mp h
        have : x = x'.val := 
          Function.Embedding.injective OrderedPair.toObject h 
          |> (OrderedPair.eq _ _ _ _ |>.mp)
          |>.right
        exact this ▸ x'.prop
    intro ⟨hAC, hBD⟩ x hx
    rw [mem_cartesian] at hx ⊢
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩ := hx
    use ⟨a, hAC _ ha⟩, ⟨b, hBD _ hb⟩ 

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use {0}, {}, {}, {}
  simp [subset_def]


/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
  ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by
    apply existsUnique_of_exists_of_unique
    · refine ⟨fun z => mk_cartesian (f z) (g z), ?_, ?_⟩ <;> funext z <;> simp
    rintro x1 x2 hx1 hx2 
    have {x: Z.toSubtype → (X ×ˢ Y).toSubtype} {z} (hx: fst ∘ x = f ∧ snd ∘ x = g) : 
      x z = mk_cartesian (f z) (g z) := by
        rw [← mk_cartesian_fst_snd_eq (x z)]
        simp only [mk_cartesian, Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq]
        rw [← Function.comp_apply (f := fst), hx.left, ← Function.comp_apply (f := snd), hx.right]
        exact And.intro rfl rfl
    funext z
    rw [this hx1, this hx2]

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
  iProd X = ∅ ↔ ∃ i, X i = ∅ := by
    constructor
    · intro h
      simp [eq_empty_iff_forall_notMem] at h
      by_contra! h'
      exact h (nonempty_choose <| h' ·)
    rintro ⟨i, hi⟩ 
    refine eq_empty_iff_forall_notMem.mpr fun x => ?_
    rw [mem_iProd]
    push_neg
    intro xi
    exact absurd (hi ▸ xi i |>.prop) (not_mem_empty _)

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
  (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by
    ext x
    simp only [mem_inter, mem_iUnion]
    constructor
    · rintro ⟨⟨i, ha⟩, ⟨j, hb⟩⟩ 
      use mk_cartesian i j
      simp [ha, hb]
    · rintro ⟨i, ⟨ha, hb⟩⟩ 
      exact And.intro ⟨fst i, ha⟩ ⟨snd i, hb⟩

theorem SetTheory.Set.iInter_union_iInter {I J: Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: I → Set) (B: J → Set) :
  (I.iInter hI A) ∪ (J.iInter hJ B) = 
  iInter (I ×ˢ J) (cartesian_nonempty_iff.mpr ⟨hI, hJ⟩) (fun p ↦ (A (fst p)) ∪ (B (snd p))) := by
    ext x
    simp only [mem_union, mem_iInter]
    constructor
    · rintro (ha|hb) ⟨i, hi⟩
      <;> obtain ⟨i, j, rfl⟩ := mem_cartesian _ _ _ |>.mp hi
      exact Or.inl (fst_of_mk_cartesian _ _ ▸ ha i)
      exact Or.inr (snd_of_mk_cartesian _ _ ▸ hb j)
    intro h
    contrapose! h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    use mk_cartesian i j
    refine And.intro (fst_of_mk_cartesian _ _ ▸ hi) (snd_of_mk_cartesian _ _ ▸ hj)

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
  graph f = graph f' ↔ f = f' := by
    refine ⟨?_, fun h => h ▸ rfl⟩ 
    intro h
    ext x
    let p := (mk_cartesian x (f x))
    replace h := Set.ext_iff.mp h p
    simp_rw [specification_axiom''] at h
    replace ⟨_, h⟩  := h.mp ⟨p.prop, by simp⟩ 
    simp at h
    rw [h]

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
  ∃! f: X → Y, G = graph f := by 
    apply existsUnique_of_exists_of_unique
    · let g (x: X): Y := hvert x |>.choose
      use g
      ext xy
      rw [specification_axiom'']
      constructor
      · intro hxy
        use hG _ hxy
        simp [g]
        generalize_proofs hXY h
        obtain ⟨x, y, rfl⟩  : ∃x y, xy = mk_cartesian (X := X) (Y := Y) x y := by
          use fst ⟨_, hXY⟩, snd ⟨_, hXY⟩ 
          simp
        replace h := h.choose_spec.right y y.prop (fst_of_mk_cartesian _ _ ▸ hxy)
        rw [← h, snd_of_mk_cartesian]
      rintro ⟨hXY, h⟩ 
      obtain ⟨x, y, rfl⟩  : ∃x y, xy = ↑(mk_cartesian x y) := by
        use fst ⟨xy, hXY⟩, snd ⟨xy, hXY⟩ 
        simp
      simp [g] at h
      generalize_proofs h' at h
      exact h ▸ h'.choose_spec.left
    rintro f1 f2 h rfl
    exact graph_inj _ _ |>.mp h.symm

/--
  Exercise 3.5.11. This trivially follows from `SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from `SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
  ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := by
    apply existsUnique_of_exists_of_unique
    · let ⟨Z, hZ⟩ := exists_powerset (Y ×ˢ X)
      let Z' := Z.specify (fun z =>
        have := hZ z |>.mp z.prop
        have G := this.choose
        ∀ y:Y, ∃! x:X, ((⟨y,x⟩:OrderedPair):Object) ∈ G
      )
      let Z'' := Z'.replace (P := fun G' f' => 
        ∃! f: Y → X, f = f' ∧ (G': Object) = (graph f)
      ) (by rintro G _ _ ⟨⟨f1, ⟨_, h1⟩⟩, ⟨f2, ⟨_, h2⟩⟩⟩; simp_all [graph_inj])
      use Z''
      intro F
      simp [Z'']
      constructor
      · rintro ⟨w, _, ⟨f, ⟨hf, _⟩, _⟩⟩ 
        use f
      rintro ⟨f, rfl⟩ 
      use graph f
      constructor
      · simp only [Z', specification_axiom'']
        constructor
        · rintro y
          generalize_proofs h
          obtain hG := Function.Embedding.injective _ h.choose_spec.left |>.symm
          rw [hG] at *
          apply existsUnique_of_exists_of_unique
          · use f y
            simp
          intro x1 x2 hx1 hx2
          simp_all
        apply hZ _ |>.mpr
        refine ⟨graph f, rfl, ?_⟩
        intro xy hxy
        obtain ⟨h, _⟩ := specification_axiom'' _ _ |>.mp hxy
        exact h
      refine existsUnique_of_exists_of_unique ⟨f, rfl, rfl⟩  ?_
      intro f1 f2 ⟨hf1, _⟩ ⟨hf2, _⟩
      exact coe_of_fun_inj _ _ |>.mp <| hf1.trans hf2.symm
    intro Z1 Z2 h1 h2
    ext F
    rw [h1 F, h2 F]

/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
  ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by
    apply existsUnique_of_exists_of_unique
    · let a: ℕ → X := _root_.Nat.rec c (fun n a_n => f n a_n)
      refine ⟨fun n => a n, ?_, ?_⟩ <;> simp [a]
    intro a1 a2 ha1 ha2
    ext n
    obtain ⟨n, rfl⟩: ∃n': ℕ, n = n' := by use (n: ℕ); rw [nat_equiv_coe_of_coe']
    induction' n with n ih
    · rw [show ↑(0: ℕ) = (0: nat) by rfl, ha1.left, ha2.left]
    rw [ha1.right, ha2.right, Subtype.coe_inj.mp ih]

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, hf⟩ := recursion nat' (fun n n' => succ n') zero
  have succ_inj {x y} : succ x = succ y ↔ x = y := by
    refine ⟨fun h => ?_, fun h => h ▸ rfl⟩ 
    contrapose! h
    exact succ_of_ne x y h
  /- have nonzero_iff {x} : x ≠ zero ↔ ∃y, x = succ y := by -/
  /-   refine ⟨fun h => ?_, fun h => ?_⟩  -/
  /-   · revert x -/
  /-     apply ind -/
  /-     · exact fun h => absurd rfl h -/
  /-     intro n _ _ -/
  /-     use n -/
  /-   by_contra! h' -/
  /-   obtain ⟨y, hy⟩ := h' ▸ h -/
  /-   exact succ_ne y hy.symm -/
  apply existsUnique_of_exists_of_unique
  · use f
    refine ⟨⟨?_, ?_⟩, hf.left.left, ?_⟩ 
    · intro x1 x2 heq
      induction' hx1: (x1:ℕ) with i ih generalizing x1 x2
      · have : x1 = 0 :=  nat_coe_eq hx1
        subst x1
        simp [hf.left.left] at heq
        by_cases h: x2 = 0
        · exact h.symm
        obtain ⟨x2', hx2'⟩ := _root_.Nat.exists_eq_succ_of_ne_zero fun a ↦ h (nat_coe_eq a)
        obtain rfl : x2 = ↑x2'.succ := nat_coe_eq hx2'
        rw [hf.left.right x2'] at heq
        exact (succ_ne _ heq.symm).elim
      obtain rfl := nat_coe_eq hx1; clear hx1
      rw [hf.left.right i] at heq
      have : x2 ≠ 0 := by
        by_contra! h
        simp [h, hf.left.left] at heq
        exact succ_ne _ heq
      have : (x2 : ℕ) ≠ 0 := fun a ↦ this (nat_coe_eq a)
      obtain ⟨x2, hx2'⟩ := _root_.Nat.exists_eq_succ_of_ne_zero this; clear this
      obtain rfl := nat_coe_eq hx2'; clear hx2'
      refine (nat_equiv_inj (i + 1) x2.succ).mpr ?_
      replace heq: f ↑i = f ↑x2 := by
        simp [hf.left.right x2, succ_inj] at heq
        exact heq
      exact (ih heq (nat_equiv_coe_of_coe _) |> (nat_equiv_inj _ _ |>.mp)) ▸ rfl
    · apply ind
      · exact ⟨0, hf.left.left⟩
      intro y ⟨x, hx⟩ 
      use (x: ℕ).succ
      rw [← hx, hf.left.right, nat_equiv_coe_of_coe']
    · intro x y
      constructor
      · rintro rfl
        rw [hf.left.right, nat_equiv_coe_of_coe']
      · rintro h
        rwa [hf.left.right, succ_inj, nat_equiv_coe_of_coe'] at h
  intro f1 f2 hf1 hf2
  ext x
  induction' hx: (x:ℕ) with i ih generalizing x
  · simp_rw [show x = 0 from nat_coe_eq hx, hf1.right.left, hf2.right.left]
  simp_rw [show x = ↑(i + 1) from nat_coe_eq hx,
    nat_equiv_coe_of_coe i ▸ hf1.right.right i (f1 i) |>.mp rfl,
    nat_equiv_coe_of_coe i ▸ hf2.right.right i (f2 i) |>.mp rfl,
    ih i (nat_equiv_coe_of_coe i) |> (coe_inj _ _ _ |>.mp)
  ]

end Chapter3
