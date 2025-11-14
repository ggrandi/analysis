import Mathlib.Tactic

/- set_option profiler true -/
/- set_option profiler.threshold 50 -/

/-!
# Analysis I, Section 3.1: Fundamentals (of set theory)

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be
as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to
the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A type `Chapter3.SetTheory.Set` of sets
- A type `Chapter3.SetTheory.Object` of objects
- An axiom that every set is (or can be coerced into) an object
- The empty set `∅`, singletons `{y}`, and pairs `{y,z}` (and more general finite tuples), with
  their attendant axioms
- Pairwise union `X ∪ Y`, and their attendant axioms
- Coercion of a set `A` to its associated type `A.toSubtype`, which is a subtype of `Object`, and
  basic API.  (This is a technical construction needed to make the Zermelo-Frankel set theory
  compatible with the dependent type theory of Lean.)
- The specification `A.specify P` of a set `A` and a predicate `P: A.toSubtype → Prop` to the
  subset of elements of `A` obeying `P`, and the axiom of specification.
  TODO: somehow implement set builder elaboration for this.
- The replacement `A.replace hP` of a set `A` via a predicate
  `P: A.toSubtype → Object → Prop` obeying a uniqueness condition
  `∀ x y y', P x y ∧ P x y' → y = y'`, and the axiom of replacement.
- A bijective correspondence between the Mathlib natural numbers `ℕ` and a set
  `Chapter3.Nat : Chapter3.Set` (the axiom of infinity).
- Axioms of regularity, power set, and union (used in later sections of this chapter, but not
  required here)
- Connections with Mathlib's notion of a set

The other axioms of Zermelo-Frankel set theory are discussed in later sections.

Some technical notes:
- Mathlib of course has its own notion of a `Set` (or more precisely, a type `Set X` associated to
  each type `X`), which is not compatible with the notion `Chapter3.Set` defined here,
  though we will try to make the notations match as much as possible.  This causes some notational
  conflict: for instance, one may need to explicitly specify `(∅:Chapter3.Set)` instead of just `∅`
  to indicate that one is using the `Chapter3.Set` version of the empty set, rather than the
  Mathlib version of the empty set, and similarly for other notation defined here.
- In Analysis I, we chose to work with an "impure" set theory, in which there could be more
  `Object`s than just `Set`s.  In the type theory of Lean, this requires treating `Chapter3.Set`
  and `Chapter3.Object` as distinct types. Occasionally this means we have to use a coercion
  `(X: Chapter3.Object)` of a `Chapter3.Set` `X` to make into a `Chapter3.Object`: this is
  mostly needed when manipulating sets of sets.
- Strictly speaking, a set `X:Set` is not a type; however, we will coerce sets to types, and
  specifically to a subtype of `Object`.  A similar coercion is in place for Mathlib's
  formalization of sets.
- After this chapter is concluded, the notion of a `Chapter3.SetTheory.Set` will be deprecated in
  favor of the standard Mathlib notion of a `Set` (or more precisely of the type `Set X` of a set
  in a given type `X`).  However, due to various technical incompatibilities between set theory
  and type theory, we will not attempt to create a full equivalence between these two
  notions of sets. (As such, this makes this entire chapter optional from the point of view of
  the rest of the book, though we retain it for pedagogical purposes.)

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)
-/

namespace Chapter3

/- The ability to work in multiple universe is not relevant immediately, but
becomes relevant when constructing models of set theory in the Chapter 3 epilogue. -/
universe u v

/-- The axioms of Zermelo-Frankel theory with atoms.  -/
class SetTheory where
  Set : Type u -- Axiom 3.1
  Object : Type v -- Axiom 3.1
  set_to_object : Set ↪ Object -- Axiom 3.1
  mem : Object → Set → Prop -- Axiom 3.1
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y -- Axiom 3.2
  emptyset: Set -- Axiom 3.3
  emptyset_mem x : ¬ mem x emptyset -- Axiom 3.3
  singleton : Object → Set -- Axiom 3.4
  singleton_axiom x y : mem x (singleton y) ↔ x = y -- Axiom 3.4
  union_pair : Set → Set → Set -- Axiom 3.5
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y) -- Axiom 3.5
  specify A (P: Subtype (mem . A) → Prop) : Set -- Axiom 3.6
  specification_axiom A (P: Subtype (mem . A) → Prop) :
    (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x -- Axiom 3.6
  replace A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : Set -- Axiom 3.7
  replacement_axiom A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y -- Axiom 3.7
  nat : Set -- Axiom 3.8
  nat_equiv : ℕ ≃ Subtype (mem . nat) -- Axiom 3.8
  regularity_axiom A (hA : ∃ x, mem x A) :
    ∃ x, mem x A ∧ ∀ S, x = set_to_object S → ¬ ∃ y, mem y A ∧ mem y S -- Axiom 3.9
  pow : Set → Set → Set -- Axiom 3.11
  function_to_object (X: Set) (Y: Set) :
    (Subtype (mem . X) → Subtype (mem . Y)) ↪ Object -- Axiom 3.11
  powerset_axiom (X: Set) (Y: Set) (F:Object) :
    mem F (pow X Y) ↔ ∃ f: Subtype (mem . Y) → Subtype (mem . X),
    function_to_object Y X f = F -- Axiom 3.11
  union : Set → Set -- Axiom 3.12
  union_axiom A x : mem x (union A) ↔ ∃ S, mem x S ∧ mem (set_to_object S) A -- Axiom 3.12

-- This enables one to use `Set` and `Object` instead of `SetTheory.Set` and `SetTheory.Object`.
export SetTheory (Set Object)

-- This instance implicitly imposes the axioms of Zermelo-Frankel set theory with atoms.
variable [SetTheory]

/-- Definition 3.1.1 (objects can be elements of sets) -/
instance SetTheory.objects_mem_sets : Membership Object Set where
  mem X x := mem x X

-- Now we can use the `∈` notation between our `Object` and `Set`.
example (X: Set) (x: Object) : x ∈ X ↔ SetTheory.mem x X := by rfl

/-- Axiom 3.1 (Sets are objects)-/
instance SetTheory.sets_are_objects : Coe Set Object where
  coe X := set_to_object X

-- Now we can treat a `Set` as an `Object` when needed.
example (X: Set) : (X: Object) = SetTheory.set_to_object X := rfl

/-- Axiom 3.1 (Sets are objects)-/
theorem SetTheory.Set.coe_eq {X Y:Set} (h: (X: Object) = (Y: Object)) : X = Y :=
  set_to_object.inj' h

/-- Axiom 3.1 (Sets are objects)-/
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y:Set) : (X: Object) = (Y: Object) ↔  X = Y :=
  ⟨ coe_eq, by rintro rfl; rfl ⟩

/-- Axiom 3.2 (Equality of sets).  The `[ext]` tag allows the `ext` tactic to work for sets. -/
@[ext]
theorem SetTheory.Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := extensionality _ _ h

/- Axiom 3.2 (Equality of sets)-/
#check SetTheory.Set.ext_iff

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := emptyset

-- Now we can use the `∅` notation to refer to `SetTheory.emptyset`.
example : ∅ = SetTheory.emptyset := rfl

-- Make everything we define in `SetTheory.Set.*` accessible directly.
open SetTheory.Set

/--
  Axiom 3.3 (empty set).
  Note: in some applications one may have to explicitly cast ∅ to Set due to
  Mathlib's existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅:Set) := emptyset_mem

/-- Empty set has no elements -/
theorem SetTheory.Set.eq_empty_iff_forall_notMem {X:Set} : X = ∅ ↔ (∀ x, x ∉ X) := by
  refine ⟨
    fun h => h ▸ emptyset_mem, 
    fun h => extensionality _ _ <| fun x => ⟨fun hxX => ?_, fun hx => ?_⟩⟩ 
  · have := h x
    contradiction
  · have := emptyset_mem x
    contradiction

/-- Empty set is unique -/
theorem SetTheory.Set.empty_unique : ∃! (X:Set), ∀ x, x ∉ X := by
  apply existsUnique_of_exists_of_unique ⟨∅, emptyset_mem⟩ ?_
  · intro X Y hX hY
    ext x
    exact (iff_false_right (hY x)).mpr (hX x)

/-- Lemma 3.1.5 (Single choice) -/
lemma SetTheory.Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have claim (x:Object) : x ∈ X ↔ x ∈ (∅:Set) := by simp [this, not_mem_empty]
  apply ext at claim
  contradiction

theorem SetTheory.Set.nonempty_of_inhabited {X:Set} {x:Object} (h:x ∈ X) : X ≠ ∅ := by
  contrapose! h
  rw [eq_empty_iff_forall_notMem] at h
  exact h x

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := singleton

-- Now we can use the `{x}` notation for a single element `Set`.
example (x: Object) : {x} = SetTheory.singleton x := rfl

/--
  Axiom 3.3(a) (singleton).
  Note: in some applications one may have to explicitly cast {a} to Set due to Mathlib's
  existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a := singleton_axiom x a


instance SetTheory.Set.instUnion : Union Set where
  union := union_pair

-- Now we can use the `X ∪ Y` notation for a union of two `Set`s.
example (X Y: Set) : X ∪ Y = SetTheory.union_pair X Y := rfl

/-- Axiom 3.4 (Pairwise union)-/
@[simp]
theorem SetTheory.Set.mem_union (x:Object) (X Y:Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
  union_pair_axiom X Y x

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

@[simp]
theorem SetTheory.Set.mem_insert (a b: Object) (X: Set) : a ∈ insert b X ↔ a = b ∨ a ∈ X := by
  simp [instInsert]

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
theorem SetTheory.Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b} := by rfl

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
@[simp]
theorem SetTheory.Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  simp [pair_eq, mem_union, mem_singleton]

@[simp]
theorem SetTheory.Set.mem_triple (x a b c:Object) : x ∈ ({a,b,c}:Set) ↔ (x = a ∨ x = b ∨ x = c) := by
  simp [Insert.insert, mem_union, mem_singleton]

/-- Remark 3.1.9 -/
theorem SetTheory.Set.singleton_uniq (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by
  refine existsUnique_of_exists_of_unique ⟨{a}, (mem_singleton · a)⟩ ?_
  · intro X Y hX hY
    ext x
    exact Iff.trans (hX x) (hY x).symm

/-- Remark 3.1.9 -/
theorem SetTheory.Set.pair_uniq (a b:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by
  apply existsUnique_of_exists_of_unique  ⟨{a, b}, fun x => Set.mem_pair ..⟩ ?_
  · intro X Y hX hY
    ext x
    exact Iff.trans (hX x) (hY x).symm

/-- Remark 3.1.9 -/
theorem SetTheory.Set.pair_comm (a b:Object) : ({a,b}:Set) = {b,a} := by
  ext x
  rw [Set.mem_pair, Set.mem_pair, Or.comm]

/-- Remark 3.1.9 -/
@[simp]
theorem SetTheory.Set.pair_self (a:Object) : ({a,a}:Set) = {a} := by
  ext x
  rw [Set.mem_pair, Set.mem_singleton, or_self]

/-- Exercise 3.1.1 -/
theorem SetTheory.Set.pair_eq_pair {a b c d:Object} (h: ({a,b}:Set) = {c,d}) :
    a = c ∧ b = d ∨ a = d ∧ b = c := by sorry
  /- This is a proof but it makes the code take an extra second to run -/
  /- have h: ∀ x, x ∈ ({a,b}: Set) ↔ x ∈ ({c,d}: Set) := Set.ext_iff.mp h -/
  /- have ha: a = c ∨ a = d := h a |>.mp ((mem_pair ..).mpr (Or.inl rfl)) |> (mem_pair ..).mp -/
  /- have hb: b = c ∨ b = d := h b |>.mp ((mem_pair ..).mpr (Or.inr rfl)) |> (mem_pair ..).mp -/
  /- have hc: c = a ∨ c = b := h c |>.mpr ((mem_pair ..).mpr (Or.inl rfl)) |> (mem_pair ..).mp -/
  /- have hd: d = a ∨ d = b := h d |>.mpr ((mem_pair ..).mpr (Or.inr rfl)) |> (mem_pair ..).mp -/
  /- tauto -/

abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {(empty: Object)}
abbrev SetTheory.Set.pair_empty : Set := {(empty: Object), (singleton_empty: Object)}

/-- Exercise 3.1.2 -/
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  by_contra! h
  have hmem : (empty: Object) ∈ singleton_empty := (mem_singleton ..).mpr rfl
  have hnmem : ¬(empty: Object) ∈ singleton_empty := h ▸ emptyset_mem _
  exact hnmem hmem


/-- Exercise 3.1.2 -/
theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by
  by_contra! h
  have hmem : (empty: Object) ∈ pair_empty := mem_pair .. |>.mpr <| Or.inl rfl
  have hnmem : ¬(empty: Object) ∈ pair_empty := h ▸ emptyset_mem _
  exact hnmem hmem


/-- Exercise 3.1.2 -/
theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  by_contra h
  have hmem : (singleton_empty : Object) ∈ singleton_empty := by
    nth_rw 1 [h]
    apply mem_pair _ _ _ |>.mpr
    apply Or.inr rfl
  apply mem_singleton _ _ |>.mp at hmem
  have : singleton_empty = empty := coe_eq_iff _ _ |>.mp hmem
  exact emptyset_neq_singleton this.symm

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_left (A A' B:Set) (h: A = A') : A ∪ B = A' ∪ B := h ▸ rfl

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_right (A B B':Set) (h: B = B') : A ∪ B = A ∪ B' := h ▸ rfl

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.singleton_union_singleton (a b:Object) :
    ({a}:Set) ∪ ({b}:Set) = {a,b} := rfl


/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_comm (A B:Set) : A ∪ B = B ∪ A := by
  ext x
  rw [mem_union, mem_union, Or.comm]

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_assoc (A B C:Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  -- this proof is written to follow the structure of the original text.
  ext x
  simp only [mem_union, or_assoc]

/-- Proposition 3.1.27(c) -/
@[simp]
theorem SetTheory.Set.union_self (A:Set) : A ∪ A = A := by
  ext x
  rw [mem_union, or_self]
  

/-- Proposition 3.1.27(a) -/
@[simp]
theorem SetTheory.Set.union_empty (A:Set) : A ∪ ∅ = A := by
  ext x
  rw [mem_union, or_iff_left <| not_mem_empty x]

/-- Proposition 3.1.27(a) -/
@[simp]
theorem SetTheory.Set.empty_union (A:Set) : ∅ ∪ A = A := by
  rw [union_comm, union_empty]

theorem SetTheory.Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c} := by
  rfl

/-- Example 3.1.10 -/
theorem SetTheory.Set.pair_union_pair (a b c:Object) :
    ({a,b}:Set) ∪ {b,c} = {a,b,c} := by
  ext; simp only [mem_union, mem_pair, mem_triple]; tauto

/-- Definition 3.1.14.   -/
instance SetTheory.Set.instSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

-- Now we can use `⊆` for a subset relationship between two `Set`s.
example (X Y: Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

-- Now we can use `⊂` for a strict subset relationship between two `Set`s.
example (X Y: Set) : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y := by rfl

/-- Definition 3.1.14. -/
theorem SetTheory.Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
theorem SetTheory.Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/-- Remark 3.1.15 -/
theorem SetTheory.Set.subset_congr_left {A A' B:Set} (hAA':A = A') (hAB: A ⊆ B) : A' ⊆ B := 
  hAA'.symm ▸ hAB

/-- Examples 3.1.16 -/
@[simp, refl]
theorem SetTheory.Set.subset_self (A:Set) : A ⊆ A := fun _ => id 

@[simp]
theorem SetTheory.Set.not_ssubset_self (A:Set) : ¬ A ⊂ A := fun h => h.right rfl

theorem SetTheory.Set.subset_of_ssubset (X Y:Set) : X ⊆ Y ↔ X ⊂ Y ∨ X = Y := by
  refine ⟨fun hXY => ?_, ?_⟩
  · by_cases h : X = Y
    · exact Or.inr h
    · exact Or.inl ⟨hXY, h⟩
  · rintro (⟨h, _⟩|rfl)
    assumption
    exact subset_self _

/-- Examples 3.1.16 -/
@[simp]
theorem SetTheory.Set.empty_subset (A:Set) : ∅ ⊆ A := 
  fun _ h => absurd h (not_mem_empty _)

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C := by
  -- This proof is written to follow the structure of the original text.
  rw [subset_def]
  intro x hx
  rw [subset_def] at hAB
  apply hAB x at hx
  apply hBC x at hx
  assumption

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_antisymm (A B:Set) (hAB:A ⊆ B) (hBA:B ⊆ A) : A = B := by
  ext x
  exact ⟨fun h => hAB _ h, fun h => hBA _ h⟩

theorem SetTheory.Set.subset_antisymm_iff { A B:Set } : A = B ↔ A ⊆ B ∧ B ⊆ A :=
  ⟨fun h => h ▸ ⟨subset_self _, subset_self _⟩, fun ⟨hAB, hBA⟩ => subset_antisymm _ _ hAB hBA⟩

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.ssubset_trans (A B C:Set) (hAB:A ⊂ B) (hBC:B ⊂ C) : A ⊂ C := by
  refine ⟨subset_trans hAB.left hBC.left, ?_⟩
  by_contra! h
  rw [h.symm] at hBC
  have : A = B := subset_antisymm _ _ hAB.left hBC.left
  exact hAB.right this

/--
  This defines the subtype `A.toSubtype` for any `A:Set`.
  Note that `A.toSubtype` gives you a type, similar to how `Object` or `Set` are types.
  A value `x'` of type `A.toSubtype` combines some `x: Object` with a proof that `hx: x ∈ A`.

  To produce an element `x'` of this subtype, use `⟨ x, hx ⟩`, where `x: Object` and `hx: x ∈ A`.
  The object `x` associated to a subtype element `x'` is recovered as `x'.val`, and
  the property `hx` that `x` belongs to `A` is recovered as `x'.property`.
-/
abbrev SetTheory.Set.toSubtype (A:Set) := Subtype (fun x ↦ x ∈ A)

example (A: Set) (x: Object) (hx: x ∈ A) : A.toSubtype := ⟨x, hx⟩
example (A: Set) (x': A.toSubtype) : Object := x'.val
example (A: Set) (x': A.toSubtype) : x'.val ∈ A := x'.property

-- In practice, a subtype lets us carry an object with a membership proof as a single value.
-- Compare these two proofs. They are equivalent, but the latter packs `x` and `hx` into `x'`.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

instance : CoeSort (Set) (Type v) where
  coe A := A.toSubtype

-- Now instead of writing `x': A.toSubtype`, we can just write `x': A`.
-- Compare these three proofs. They are equivalent, but the last one reads most concisely.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property
example (A B: Set) (x': A) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

/--
  Elements of a set (implicitly coerced to a subtype) are also elements of the set
  (with respect to the membership operation of the set theory).
-/
lemma SetTheory.Set.subtype_property (A:Set) (x:A) : x.val ∈ A := x.property

lemma SetTheory.Set.subtype_coe (A:Set) (x:A) : x.val = x := rfl

lemma SetTheory.Set.coe_inj (A:Set) (x y:A) : x.val = y.val ↔ x = y := Subtype.coe_inj

/--
  If one has a proof `hx` of `x ∈ A`, then `A.subtype_mk hx` will then make the element of `A`
  (viewed as a subtype) corresponding to `x`.
-/
def SetTheory.Set.subtype_mk (A:Set) {x:Object} (hx:x ∈ A) : A := ⟨ x, hx ⟩

@[simp]
lemma SetTheory.Set.subtype_mk_coe {A:Set} {x:Object} (hx:x ∈ A) : A.subtype_mk hx = x := by rfl


abbrev SetTheory.Set.specify (A:Set) (P: A → Prop) : Set := SetTheory.specify A P

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom {A:Set} {P: A → Prop} {x:Object} (h: x ∈ A.specify P) :
    x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom' {A:Set} (P: A → Prop) (x:A) :
    x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

/-- Axiom 3.6 (axiom of specification) -/
@[simp]
theorem SetTheory.Set.specification_axiom'' {A:Set} (P: A → Prop) (x:Object) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩ := by
  constructor
  . intro h; use specification_axiom h
    simp [←specification_axiom' P, h]
  intro ⟨ h, hP ⟩
  simpa [←specification_axiom' P] using hP

theorem SetTheory.Set.specify_subset {A:Set} (P: A → Prop) : A.specify P ⊆ A := by
  intro x
  rw [specification_axiom'']
  rintro ⟨hxA, _⟩
  exact hxA

/-- This exercise may require some understanding of how subtypes are implemented in Lean. -/
theorem SetTheory.Set.specify_congr {A A':Set} (hAA':A = A') {P: A → Prop} {P': A' → Prop}
  (hPP': (x:Object) → (h:x ∈ A) → (h':x ∈ A') → P ⟨ x, h⟩ ↔ P' ⟨ x, h'⟩ ) :
    A.specify P = A'.specify P' := by
    refine Set.ext_iff.mpr (fun x => ⟨?_, ?_⟩)
    · intro h
      have hxA : x ∈ A := specification_axiom h
      have hxA' : x ∈ A' := hAA'.symm ▸ hxA
      obtain ⟨_, h⟩ := specification_axiom'' _ _ |>.mp h
      refine specification_axiom'' _ _ |>.mpr ⟨hxA', ?_⟩
      apply hPP' x hxA hxA' |>.mp h
    · intro h
      have hxA' : x ∈ A' := specification_axiom h
      have hxA : x ∈ A := hAA'.symm ▸ hxA'
      obtain ⟨_, h⟩ := specification_axiom'' _ _ |>.mp h
      refine specification_axiom'' _ _ |>.mpr ⟨hxA, ?_⟩
      apply hPP' x hxA hxA' |>.mpr h


instance SetTheory.Set.instIntersection : Inter Set where
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

-- Now we can use the `X ∩ Y` notation for an intersection of two `Set`s.
example (X Y: Set) : X ∩ Y = X.specify (fun x ↦ x.val ∈ Y) := rfl

/-- Definition 3.1.22 (Intersections) -/
@[simp]
theorem SetTheory.Set.mem_inter (x:Object) (X Y:Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  . intro h; have h' := specification_axiom h; simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩).mp h
  intro ⟨ hX, hY ⟩; exact (specification_axiom' (fun x ↦ x.val ∈ Y) ⟨ x,hX⟩).mpr hY

instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

-- Now we can use the `X \ Y` notation for a difference of two `Set`s.
example (X Y: Set) : X \ Y = X.specify (fun x ↦ x.val ∉ Y) := rfl

/-- Definition 3.1.26 (Difference sets) -/
@[simp]
theorem SetTheory.Set.mem_sdiff (x:Object) (X Y:Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  . intro h; have h' := specification_axiom h; simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩ ).mp h
  intro ⟨ hX, hY ⟩; exact (specification_axiom' (fun x ↦ x.val ∉ Y) ⟨ x, hX⟩ ).mpr hY

/-- Proposition 3.1.27(d) / Exercise 3.1.6 -/
theorem SetTheory.Set.inter_comm (A B:Set) : A ∩ B = B ∩ A := by
  ext x
  rw [mem_inter, mem_inter, and_comm]

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.subset_union {A X: Set} (hAX: A ⊆ X) : A ∪ X = X := by
  ext x
  rw [mem_union]
  exact or_iff_right_iff_imp.mpr (hAX _)

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.union_subset {A X: Set} (hAX: A ⊆ X) : X ∪ A = X := by
  rw [union_comm, subset_union hAX]

/-- Proposition 3.1.27(c) -/
@[simp]
theorem SetTheory.Set.inter_self (A:Set) : A ∩ A = A := by
  ext x
  rw [mem_inter, and_self]

/-- Proposition 3.1.27(e) -/
theorem SetTheory.Set.inter_assoc (A B C:Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  rw [mem_inter, mem_inter, mem_inter, mem_inter, and_assoc]

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.inter_union_distrib_left (A B C:Set) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter, and_or_left]

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.union_inter_distrib_left (A B C:Set) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_union, or_and_left]

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.union_compl {A X:Set} (hAX: A ⊆ X) : A ∪ (X \ A) = X := by
  ext x
  rw [mem_union, mem_sdiff]
  refine ⟨?_, fun hX => ?_⟩
  · rintro (hA|⟨hX, _⟩)
    · exact hAX _ hA
    · exact hX
  · by_cases hA : x ∈ A
    · exact Or.inl hA
    · exact Or.inr ⟨hX, hA⟩


/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.inter_compl {A X:Set} : A ∩ (X \ A) = ∅ := by
  ext x
  simp
  exact fun h _ => h

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_union {A B X:Set} : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  ext x
  simp
  exact and_and_left

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_inter {A B X:Set} : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  ext x
  simp
  refine ⟨fun ⟨hX, hAnB⟩ => ?_, ?_⟩
  · by_cases hA : x ∈ A    
    · exact Or.inr ⟨hX, hAnB hA⟩
    · exact Or.inl ⟨hX, hA⟩
  · rintro (⟨hX,hnA⟩|⟨hX,hnB⟩) 
    · exact ⟨hX, fun hA _ => hnA hA⟩
    · exact ⟨hX, fun _ => hnB⟩

/-- Not from textbook: sets form a distributive lattice. -/
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := fun _ _ _ ↦ subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left A B x hA := by
    rw [mem_union]
    exact (Or.inl hA)
  le_sup_right A B x hB := by
    rw [mem_union]
    exact (Or.inr hB)
  sup_le A B C hAC hBC x h := by
    obtain hA|hB := mem_union _ _ _ |>.mp h
    · exact hAC _ hA
    · exact hBC _ hB
  inf_le_left A B x h := mem_inter _ _ _ |>.mp h |>.left
  inf_le_right A B x h := mem_inter _ _ _ |>.mp h |>.right
  le_inf A B C hAB hAC x hA := mem_inter _ _ _ |>.mpr ⟨hAB _ hA, hAC _ hA⟩ 
  le_sup_inf := by
    intro X Y Z; change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [←union_inter_distrib_left]


/-- Sets have a minimal element.  -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

-- Now we've defined `A ≤ B` to mean `A ⊆ B`, and set `⊥` to `∅`.
-- This makes the `Disjoint` definition from Mathlib work with our `Set`.
example (A B: Set) : (A ≤ B) ↔ (A ⊆ B) := by rfl
example : ⊥ = (∅: Set) := by rfl
example (A B: Set) : Prop := Disjoint A B

/-- Definition of disjointness (using the previous instances) -/
theorem SetTheory.Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

abbrev SetTheory.Set.replace (A:Set) {P: A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/-- Axiom 3.7 (Axiom of replacement) -/
@[simp]
theorem SetTheory.Set.replacement_axiom {A:Set} {P: A → Object → Prop}
  (hP: ∀ x y y', P x y ∧ P x y' → y = y') (y:Object) :
    y ∈ A.replace hP ↔ ∃ x, P x y := SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

-- Going forward, we'll use `Nat` as a type.
-- However, notice we've set `Nat` to `SetTheory.nat` which is a `Set` and not a type.
-- The only reason we can write `x: Nat` is because we've previously defined a `CoeSort`
-- coercion that lets us write `x: A` (when `A` is a `Set`) as a shortcut for `x: A.toSubtype`.
-- This is why, whenever you see `x: Nat`, you're really looking at `x: Nat.toSubtype`.
example (x: Nat) : Nat.toSubtype := x
example (x: Nat) : Object := x.val
example (x: Nat) : (x.val ∈ Nat) := x.property
example (o: Object) (ho: o ∈ Nat) : Nat := ⟨o, ho⟩

/-- Axiom 3.8 (Axiom of infinity) -/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

-- Below are some API for handling coercions. This may not be the optimal way to set things up.
instance SetTheory.Set.instOfNat {n:ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

-- Now we can define `Nat` with a natural literal.
example : Nat := 5
example : (5 : Nat).val ∈ Nat := (5 : Nat).property

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

-- Now we can turn `ℕ` into `Nat`.
example (n : ℕ) : Nat := n
example (n : ℕ) : (n : Nat).val ∈ Nat := (n : Nat).property

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

-- Now we can turn `Nat` into `ℕ`.
example (n : Nat) : ℕ := n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n:Nat).val

-- Now we can turn `ℕ` into an `Object`.
example (n: ℕ) : Object := n
example (n: ℕ) : Set := {(n: Object)}

instance SetTheory.Object.instOfNat {n:ℕ} : OfNat Object n where
  ofNat := ((n:Nat):Object)

-- Now we can define `Object` with a natural literal.
example : Object := 1
example : Set := {1, 2, 3}

@[simp]
lemma SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object) := rfl

@[simp]
lemma SetTheory.Object.ofnat_eq'' {n:Nat} : ((n:ℕ):Object) = (n: Object) := by
  simp [instNatCast, Nat.cast, Set.instNatCast]

@[simp]
lemma SetTheory.Object.ofnat_eq''' {n:ℕ} {hn} : ((⟨(n:Object), hn⟩: nat): ℕ) = n := by
  simp [instNatCast, Nat.cast, Set.instNatCast]

lemma SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m  :=
  Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

example : (5:Nat) ≠ (3:Nat) := by
  simp

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

example : (5:Object) ≠ (3:Object) := by
  simp

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff {m n : ℕ} : (m:Object) = ofNat(n) ↔ m = n := by exact ofNat_inj' m n

example (n: ℕ) : (n: Object) = 2 ↔ n = 2 := by
  simp

@[simp]
theorem SetTheory.Object.natCast_inj (n m:ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
      simp [←ofnat_eq, Subtype.val_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe'' (n:ℕ) : ((ofNat(n):Nat):ℕ) = n :=
  nat_equiv_coe_of_coe n

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff' {m: Nat} {n : ℕ} : (m:Object) = (ofNat(n):Object) ↔ (m:ℕ) = ofNat(n) := by
  constructor <;> intro h <;> rw [show m = n by aesop]
  apply nat_equiv_coe_of_coe; rfl


/-- Example 3.1.16 (simplified).  -/
example : ({3, 5}:Set) ⊆ {1, 3, 5} := by
  simp only [subset_def, mem_pair, mem_triple]; tauto


/-- Example 3.1.17 (simplified). -/
example : ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3) = ({5}:Set) := by
  ext
  simp only [mem_singleton, specification_axiom'']
  constructor
  · rintro ⟨h1, h2⟩; simp only [mem_pair] at h1; tauto
  rintro ⟨rfl⟩; norm_num

/-- Example 3.1.24 -/
example : ({1, 2, 4}:Set) ∩ {2,3,4} = {2, 4} := by
  ext x
  -- Instead of unfolding repetitive branches by hand like earlier,
  -- you can use the `aesop` tactic which does this automatically.
  aesop

/-- Example 3.1.24 -/

example : ({1, 2}:Set) ∩ {3,4} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  aesop

example : ¬ Disjoint ({1, 2, 3}:Set) {2,3,4} := by
  rw [disjoint_iff]
  intro h
  change {1, 2, 3} ∩ {2, 3, 4} = ∅ at h
  rw [eq_empty_iff_forall_notMem] at h
  aesop

example : Disjoint (∅:Set) ∅ := by
  exact fun X _ hX => hX

/-- Definition 3.1.26 example -/

example : ({1, 2, 3, 4}:Set) \ {2,4,6} = {1, 3} := by
  apply ext; aesop

/-- Example 3.1.30 -/
example : ({3,5,9}:Set).replace (P := fun x y ↦ ∃ (n:ℕ), x.val = n ∧ y = (n+1:ℕ)) (by aesop)
  = {4,6,10} := by
    ext x
    rw [replacement_axiom]
    refine ⟨?_, ?_⟩ 
    · rintro ⟨⟨x, hx⟩, n, rfl, rfl⟩
      simp_all only [mem_insert, nat_coe_eq_iff, mem_singleton, Nat.reduceEqDiff]
    · aesop


/-- Example 3.1.31 -/
example : ({3,5,9}:Set).replace (P := fun _ y ↦ y=1) (by aesop) = {1} := by
  ext; simp only [replacement_axiom]; aesop

/-- Exercise 3.1.5.  One can use the `tfae_have` and `tfae_finish` tactics here. -/
theorem SetTheory.Set.subset_tfae (A B:Set) : [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by
  apply List.tfae_of_forall (A ⊆ B)
  intro a ha
  replace ha: (a = (A ⊆ B)) ∨ (a = (A ∪ B = B)) ∨ (a = (A ∩ B = A)) := 
    by simp_all only [List.mem_cons, eq_iff_iff, List.not_mem_nil, or_false]
  rcases ha with rfl|rfl|rfl
  · rfl
  · refine ⟨fun h x hA => ?_, fun h => subset_union h⟩
    exact (mem_union _ _ _ |>.eq) ▸ Set.ext_iff.mp h x |>.mp (Or.inl hA)
  · refine ⟨fun h x hA => ?_, fun hAB => Set.ext_iff.mpr (fun x => ?_)⟩
    · exact (mem_inter _ _ _ |>.eq) ▸ Set.ext_iff.mp h x |>.mpr hA |>.right
    · rw [mem_inter, and_iff_left_iff_imp]
      exact hAB x

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_left (A B:Set) : A ∩ B ⊆ A :=
  fun _ hAB => mem_inter _ _ _ |>.mp hAB |>.left


/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_right (A B:Set) : A ∩ B ⊆ B :=
  fun _ hAB => mem_inter _ _ _ |>.mp hAB |>.right

/-- Exercise 3.1.7 -/
@[simp]
theorem SetTheory.Set.subset_inter_iff (A B C:Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  refine ⟨fun h => ⟨fun x hC => ?_, fun x hC => ?_⟩, fun ⟨hCA, hCB⟩ x hC => ?_⟩
  · exact (mem_inter _ _ _ |>.eq) ▸ h _ hC |>.left
  · exact (mem_inter _ _ _ |>.eq) ▸ h _ hC |>.right
  · exact (mem_inter _ _ _ |>.eq) ▸ ⟨hCA _ hC, hCB _ hC⟩ 

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_left (A B:Set) : A ⊆ A ∪ B :=
  fun _ hA => mem_union _ _ _ |>.mpr (Or.inl hA)
  

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_right (A B:Set) : B ⊆ A ∪ B :=
  fun _ hA => mem_union _ _ _ |>.mpr (Or.inr hA)

/-- Exercise 3.1.7 -/
@[simp]
theorem SetTheory.Set.union_subset_iff (A B C:Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  refine ⟨fun h => ⟨fun x hA => ?_, fun x hB => ?_⟩, fun ⟨hCA, hCB⟩ x hC => ?_⟩
  · refine h x <| (mem_union _ _ _).mpr (Or.inl hA)
  · refine h x <| (mem_union _ _ _).mpr (Or.inr hB)
  · rcases mem_union _ _ _ |>.mp hC with hA|hB
    exact hCA _ hA
    exact hCB _ hB


/-- Exercise 3.1.8 -/
@[simp]
theorem SetTheory.Set.inter_union_cancel (A B:Set) : A ∩ (A ∪ B) = A := by
  ext x
  simp
  exact fun h => (Or.inl h)

/-- Exercise 3.1.8 -/
@[simp]
theorem SetTheory.Set.union_inter_cancel (A B:Set) : A ∪ (A ∩ B) = A := by
  ext x
  simp
  exact fun h _ => h

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_left {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
  A = X \ B := by
    ext x
    simp
    replace h_union (x) := (mem_union x _ _ |>.eq) ▸ Set.ext_iff.mp h_union x
    replace h_inter (x) := (mem_inter x _ _ |>.eq) ▸ Set.ext_iff.mp h_inter x
    replace h_inter (x): x ∈ A → x ∉ B := by 
      simp only [not_mem_empty, iff_false, not_and] at h_inter
      exact h_inter x
    refine ⟨fun hA => ?_, fun ⟨hX, hnB⟩ => ?_⟩
    · exact ⟨h_union x |>.mp (Or.inl hA), h_inter _ hA⟩
    · rcases h_union _ |>.mpr hX with hA|hB
      · assumption
      · contradiction

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_right {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
    B = X \ A := partition_left (union_comm _ _ ▸ h_union) (inter_comm _ _ ▸ h_inter)

theorem SetTheory.Set.disjoint_sdiff_inter {A B: Set} : Disjoint (A \ B) (A ∩ B)  := fun _ h1 h2 _ hX =>
      have hnB := mem_sdiff _ _ _ |>.mp (h1 _ hX) |>.right
      have hB := mem_inter _ _ _ |>.mp (h2 _ hX) |>.right
      absurd hB hnB

theorem SetTheory.Set.disjoint_sdiff_sdiff {A B: Set} : Disjoint (A \ B) (B \ A)  := fun _ h1 h2 _ hX =>
      have hnB := mem_sdiff _ _ _ |>.mp (h1 _ hX) |>.right
      have hB := mem_sdiff _ _ _ |>.mp (h2 _ hX) |>.left
      absurd hB hnB

/--
  Exercise 3.1.10.
  You may find `Function.onFun_apply` and the `fin_cases` tactic useful.
-/
theorem SetTheory.Set.pairwise_disjoint (A B:Set) :
  Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A]) := by
    have h1 := disjoint_sdiff_inter (A := A) (B := B)
    have h1' := disjoint_comm.mp h1
    have h2 := disjoint_sdiff_sdiff (A := A) (B := B)
    have h2' := disjoint_comm.mp h2
    have h3 := inter_comm _ _ ▸ disjoint_sdiff_inter (A := B) (B := A)
    have h3' := disjoint_comm.mp h3
    rintro i j hij
    rw [Function.onFun_apply]
    fin_cases i <;> fin_cases j <;> aesop

/-- Exercise 3.1.10 -/
theorem SetTheory.Set.union_eq_partition (A B:Set) : A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by
  ext x
  simp
  constructor
  · rintro (hA|hB)
    · by_cases hB : x ∈ B
      · exact Or.inl <| Or.inr ⟨hA, hB⟩
      · exact Or.inl <| Or.inl ⟨hA, hB⟩
    · by_cases hA : x ∈ A
      · exact Or.inl <| Or.inr ⟨hA, hB⟩
      · exact Or.inr <|⟨hB, hA⟩
  · rintro ((⟨hA, _⟩|⟨hA, _⟩)|⟨hB, _⟩)
    · exact Or.inl hA
    · exact Or.inl hA
    · exact Or.inr hB

/--
  Exercise 3.1.11.
  The challenge is to prove this without using `Set.specify`, `Set.specification_axiom`,
  `Set.specification_axiom'`, or anything built from them (like differences and intersections).
-/
theorem SetTheory.Set.specification_from_replacement {A:Set} {P: A → Prop} :
  ∃ B, B ⊆ A ∧ ∀ x, x.val ∈ B ↔ P x := by
    let P' : A.toSubtype → Object → Prop := fun x y => P x ∧ x.val = y
    have hPP' : ∀ (x : A.toSubtype) (y y' : Object), P' x y ∧ P' x y' → y = y' := by
      rintro x y y' h
      unfold P' at h
      exact Eq.trans h.left.right.symm h.right.right
    refine ⟨A.replace hPP', fun x hx => ?_, ?_⟩
    · simp only [replacement_axiom, Subtype.exists, exists_and_right, exists_eq_right, P'] at hx
      obtain ⟨w, h⟩ := hx
      exact w
    · intro x
      rw [replacement_axiom]
      unfold P'
      refine ⟨fun ⟨x', hx'⟩ => ?_, fun hx => ⟨x, hx, rfl⟩⟩
      obtain ⟨rfl⟩ := Subtype.eq hx'.right
      exact hx'.left

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_union_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
  A' ∪ B' ⊆ A ∪ B := by
    intro x hx
    simp at hx ⊢
    exact Or.imp (hA'A _) (hB'B _) hx

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_inter_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
    A' ∩ B' ⊆ A ∩ B := by
    intro x hx
    simp at hx ⊢
    exact And.imp (hA'A _) (hB'B _) hx

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_diff_subset_counter :
  ∃ (A B A' B':Set), (A' ⊆ A) ∧ (B' ⊆ B) ∧ ¬ (A' \ B') ⊆ (A \ B) := by
    refine ⟨singleton_empty, singleton_empty, singleton_empty, empty, ?_, ?_, ?_⟩
    · exact fun _ h ↦ h
    · exact empty_subset singleton_empty
    · have h1 : singleton_empty \ empty = singleton_empty := by ext x; simp
      have h2 : singleton_empty \ singleton_empty = empty := by ext x; simp
      rw [h1, h2]
      intro h
      have hmem := h empty <| (mem_singleton _ _).mpr rfl
      apply absurd hmem <| not_mem_empty _

/-
  Final part of Exercise 3.1.12: state and prove a reasonable substitute positive result for the
  above theorem that involves set differences.
-/

/-- Exercise 3.1.13 -/
theorem SetTheory.Set.singleton_iff (A:Set) (hA: A ≠ ∅) : (¬∃ B ⊂ A, B ≠ ∅) ↔ ∃ x, A = {x} := by
  refine ⟨?_, ?_⟩ 
  · intro h
    obtain ⟨x, hx⟩ := nonempty_def hA
    refine ⟨x, ?_⟩
    ext y
    rw [mem_singleton]
    refine ⟨fun hy => ?_, fun h => h ▸ hx⟩ 
    contrapose! h
    refine ⟨{x}, ?_, ?_⟩ 
    · refine ⟨fun z hz => (mem_singleton _ _ |>.mp hz) ▸ hx, ?_⟩
      contrapose! h
      apply mem_singleton _ _ |>.mp
      apply h.symm ▸ hy
    · by_contra h
      have : x ∈ {x} := mem_singleton _ _ |>.mpr rfl
      have : ¬x ∈ {x} := h ▸ not_mem_empty x
      contradiction
  · rintro ⟨x, hAx⟩
    push_neg
    intro B ⟨hBA, hnBA⟩
    by_contra! hB'
    obtain ⟨y, hy⟩ := nonempty_def hB'
    obtain h := hAx ▸ mem_singleton _ _ |>.mp <| hBA _ hy
    have : B = A := by 
      refine subset_antisymm _ _ hBA (fun z hz => ?_) 
      rw [hAx, mem_singleton, h.symm] at hz
      exact hz ▸ hy
    contradiction

/-
  Now we introduce connections between this notion of a set, and Mathlib's notion.
  The exercise below will acquiant you with the API for Mathlib's sets.
-/

instance SetTheory.Set.inst_coe_set : Coe Set (_root_.Set Object) where
  coe X := { x | x ∈ X }

-- Now we can convert our `Set` into a Mathlib `_root_.Set`.
-- Notice that Mathlib sets are parameterized by the element type, in our case `Object`.
example (X: Set) : _root_.Set Object := X

/--
  Injectivity of the coercion. Note however that we do NOT assert that the coercion is surjective
  (and indeed Russell's paradox prevents this)
-/
@[simp]
theorem SetTheory.Set.coe_inj' (X Y:Set) :
    (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y := by
  constructor
  . intro h
    apply ext
    intro x
    replace h := congr(x ∈ $h)
    simpa using h
  rintro rfl
  rfl

/-- Compatibility of the membership operation ∈ -/
theorem SetTheory.Set.mem_coe (X:Set) (x:Object) : x ∈ (X : _root_.Set Object) ↔ x ∈ X := by
  simp

/-- Compatibility of the emptyset -/
theorem SetTheory.Set.coe_empty : ((∅:Set) : _root_.Set Object) = ∅ := by sorry

/-- Compatibility of subset -/
theorem SetTheory.Set.coe_subset (X Y:Set) :
    (X : _root_.Set Object) ⊆ (Y : _root_.Set Object) ↔ X ⊆ Y := by sorry

theorem SetTheory.Set.coe_ssubset (X Y:Set) :
    (X : _root_.Set Object) ⊂ (Y : _root_.Set Object) ↔ X ⊂ Y := by sorry

/-- Compatibility of singleton -/
theorem SetTheory.Set.coe_singleton (x: Object) : (({x}:Set) : _root_.Set Object) = {x} := by sorry

/-- Compatibility of union -/
theorem SetTheory.Set.coe_union (X Y: Set) :
    ((X ∪ Y:Set) : _root_.Set Object) = (X : _root_.Set Object) ∪ (Y : _root_.Set Object) := by sorry

/-- Compatibility of pair -/
theorem SetTheory.Set.coe_pair (x y: Object) : (({x, y}:Set) : _root_.Set Object) = {x, y} := by sorry

/-- Compatibility of subtype -/
theorem SetTheory.Set.coe_subtype (X: Set) :  (X : _root_.Set Object) = X.toSubtype := by sorry

/-- Compatibility of intersection -/
theorem SetTheory.Set.coe_intersection (X Y: Set) :
    ((X ∩ Y:Set) : _root_.Set Object) = (X : _root_.Set Object) ∩ (Y : _root_.Set Object) := by sorry

/-- Compatibility of set difference-/
theorem SetTheory.Set.coe_diff (X Y: Set) :
    ((X \ Y:Set) : _root_.Set Object) = (X : _root_.Set Object) \ (Y : _root_.Set Object) := by sorry

/-- Compatibility of disjointness -/
theorem SetTheory.Set.coe_Disjoint (X Y: Set) :
    Disjoint (X : _root_.Set Object) (Y : _root_.Set Object) ↔ Disjoint X Y := by sorry

end Chapter3
