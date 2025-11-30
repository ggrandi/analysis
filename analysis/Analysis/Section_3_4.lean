import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image `f '' S` and preimage `f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require S to be a subset of X. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
    y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  grind [replacement_axiom]

@[simp]
theorem SetTheory.Set.image_singleton {X Y:Set} {f:X → Y} {x: Object} (h: x ∈ X) :
  image f {x} = {↑(f ⟨x, h⟩)} := by
    ext y
    rw [mem_singleton, mem_image]
    refine ⟨?_, fun hy => ⟨⟨x, h⟩, mem_singleton _ _ |>.mpr rfl, hy.symm⟩⟩ 
    rintro ⟨x', hx, hfx⟩ 
    exact (mem_singleton _ _ |>.mp hx) ▸  hfx.symm

@[simp]
theorem SetTheory.Set.image_singleton' {X Y:Set} (f:X → Y) (x: X) :
  image f {x.val} = {↑(f x)} := image_singleton x.property

@[simp]
theorem SetTheory.Set.image_pair {X Y:Set} {f:X → Y} {x1 x2: Object} (h1: x1 ∈ X) (h2: x2 ∈ X):
  image f {x1, x2} = {↑(f ⟨x1, h1⟩), ↑(f ⟨x2, h2⟩) } := by
    ext y
    rw [mem_pair, mem_image]
    constructor
    · rintro ⟨x, hx, hfx⟩ 
      obtain (hx|hx) := mem_pair _ _ _ |>.mp hx
      exact Or.inl <| hx ▸ hfx.symm
      exact Or.inr <| hx ▸ hfx.symm
    · rintro (hx|hx) 
      exact ⟨⟨x1, h1⟩, mem_pair _ _ _ |>.mpr (Or.inl rfl), hx.symm⟩ 
      exact ⟨⟨x2, h2⟩, mem_pair _ _ _ |>.mpr (Or.inr rfl), hx.symm⟩ 

@[simp]
theorem SetTheory.Set.image_pair' {X Y:Set} (f:X → Y) (x1 x2: X) :
  image f {x1.val, x2.val} = {↑(f x1), ↑(f x2)} := image_pair x1.property x2.property

/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) :
  image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by
    refine Set.ext_iff.mpr fun y => ?_
    rw [mem_image, specification_axiom'']
    constructor
    · refine fun ⟨x, hx, hfx⟩ => ⟨?_, x, hx, ?_⟩ 
      exact hfx ▸ subtype_property _ _
      exact (coe_inj _ _ _).mp hfx
    · exact fun ⟨hy, x, hx, hfx⟩ => ⟨x, hx, hfx ▸ rfl⟩ 
/--
  Connection with Mathlib's notion of image.  Note the need to utilize the `Subtype.val` coercion
  to make everything type consistent.
-/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set):
    (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
  ext; simp; grind

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by intro _ h; rw [mem_image] at h; grind only [cases eager Subtype]

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals simp_all

/-- Example 3.4.3 is written using Mathlib's notion of image. -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) :
  x.val ∈ S → (f x).val ∈ image f S :=
    fun hx => mem_image _ _ _ |>.mpr ⟨x, hx, rfl⟩ 


theorem SetTheory.Set.mem_image_of_eval_counter :
  ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬((f x).val ∈ image f S → x.val ∈ S) := by
    use {0, 1}, {0}, Function.const _ ⟨0, mem_singleton _ _ |>.mpr rfl⟩
    use {1}, ⟨0, mem_pair _ _ _ |>.mpr (Or.inl rfl)⟩ 
    simp

/--
  Definition 3.4.4 (inverse images).
  Again, it is not required that U be a subset of Y.
-/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := 
  X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

/--
  A version of mem_preimage that does not require x to be of type X.
-/
theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h; by_cases hx: x ∈ X
    . use ⟨ x, hx ⟩; have := mem_preimage f U ⟨ _, hx ⟩; simp_all
    . grind [specification_axiom]
  . rintro ⟨ x', rfl, hfx' ⟩; rwa [mem_preimage]

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext; simp

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by intro _ _; aesop

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  rintro (rfl | rfl | rfl); map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
  image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
    rw [show preimage f_3_4_2 {1,2,3} = {1} by
      ext x
      simp only [mem_preimage', mem_triple, mem_singleton, f_3_4_2]
      constructor
      · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all; omega
      rintro (rfl | rfl | rfl)
      all_goals simp
      refine ⟨(1: Nat), (1: Nat).prop, by simp⟩,
    show image f_3_4_2 {1} = {2} by
      ext x
      simp
    ]
    by_contra! h
    rw [Set.ext_iff] at h
    have := h (1: ℕ) |>.mpr (mem_triple _ _ _ _ |>.mpr (Or.inl rfl)) |> (mem_singleton _ _).mp
    rw [show (2: Object) = ↑(2 : ℕ) by rfl] at this
    replace : (1 : ℕ) = (2: ℕ) := (ofNat_inj' 1 2).mp this
    contradiction

/-- Example 3.4.7 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext; refine ⟨ ?_, by aesop ⟩; rintro (_ | _ | h)
  on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  rw [show (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0, 1, 4} by aesop,
    show (fun n ↦ n ^ 2) ⁻¹' {0, 1, 4} = {-2, -1, 0, 1, 2} by
      ext x
      rw [_root_.Set.mem_preimage]
      simp only [Set.mem_insert_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        sq_eq_one_iff, Int.reduceNeg, Set.mem_singleton_iff]
      rw [show (4: ℤ) = 2 ^ 2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg]
      tauto
  ]
  by_contra h
  have : (-2 : ℤ) ∉ ({-1, 0, 1, 2}: _root_.Set ℤ) := of_decide_eq_false rfl
  exact (h ▸ this) (Set.mem_insert _ _)


instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

/-- This coercion has to be a `CoeOut` rather than a
`Coe` because the input type `X → Y` contains
parameters not present in the output type `Output` -/
instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun]

/-- Axiom 3.11 (Power set axiom) --/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp only [mem_insert, mem_singleton, coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩; simp at hx; grind

/-- Exercise 3.4.6 (i). One needs to provide a suitable definition of the power set here. -/
def SetTheory.Set.powerset (X:Set) : Set :=
  (({0,1} ^ X): Set).replace (P := fun F Y =>
    ∃(f : X.toSubtype → ({0,1} : Set).toSubtype), F = (f: Object) ∧ Y = preimage f {1}
  ) (by aesop)

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
  x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
    simp [powerset, replacement_axiom]
    constructor
    · rintro ⟨Y, rfl⟩ 
      exact ⟨preimage Y {1}, rfl, preimage_in_domain _ _⟩
    rintro ⟨Y, rfl, hY⟩ 
    use fun x => if x.val ∈ Y 
      then ⟨1, mem_pair _ _ _ |>.mpr (Or.inr rfl)⟩ 
      else ⟨0, mem_pair _ _ _ |>.mpr (Or.inl rfl)⟩
    refine (coe_eq_iff _ _).mpr ?_
    ext y
    refine ⟨fun hy => ?_, ?_⟩ 
    · have : y = ↑(⟨y, hY _ hy⟩: X.toSubtype) := rfl
      rw [this, mem_preimage]
      simp [hy]
    · aesop

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

theorem SetTheory.Set.union_empty_eq : union ∅ = ∅ := by
  ext x
  rw [union_axiom, iff_false_right (not_mem_empty _), not_exists]
  intro S
  rw [not_and]
  exact fun _ hS => (not_mem_empty _) hS

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
  ext x
  rw [union_axiom, show x ∈ ({2, 3, 4, 5}: Set) ↔ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 by
    simp_rw [Set.mem_insert, Set.mem_singleton]]
  constructor
  · rintro ⟨S, hx, hS⟩ 
    obtain (hS|hS|hS):= mem_triple _ _ _ _ |>.mp hS
    <;> obtain hS|hS := mem_pair _ _ _ |>.mp ((set_to_object.inj' hS ) ▸ hx)
    <;> simp [hS]
  · rintro (rfl|rfl|rfl|rfl)
    · use {2,3}; simp
    · use {2,3}; simp
    · use {4,5}; simp
    · use {4,5}; simp

/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by grind))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom]; constructor
  . simp_all [replacement_axiom]
  grind [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Connection with Mathlib indexed union -/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext; simp [mem_iUnion]

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by
  ext x
  rw [iUnion, replace_empty, union_empty_eq]

/-- Indexed intersection -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (β:I) (A: I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α:I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
    x ∈ iInter I hI A ↔ ∀ α:I, x ∈ A α := by
  rw [specification_axiom'']
  constructor
  · rintro ⟨hx, h⟩ a
    exact h a
  · intro h
    refine ⟨h (nonempty_choose hI), fun α ↦ h α⟩

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (_hV: V ⊆ Y) :
  image f_inv V = preimage f V := by
    ext x
    rw [mem_image, mem_preimage']
    refine ⟨fun ⟨y',hV, hfy⟩ => ?_, ?_⟩ 
    · use f_inv y', hfy, hf.right y' |>.symm ▸ hV
    rintro ⟨x, rfl, hV⟩ 
    use f x, hV, hf.left x |>.symm ▸ rfl

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f S)` and `S`. -/
theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) 
  : S ⊆ preimage f (image f S) := by
    intro x hx
    rw [mem_preimage']
    use ⟨x, hS _ hx⟩, rfl
    rw [mem_image]
    use ⟨x, hS _ hx⟩


/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`.
Interestingly, it is not needed for U to be a subset of Y. -/
theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) :
  image f (preimage f U) ⊆ U := by
    intro x
    rw [mem_image]
    intro ⟨y, h, hy⟩ 
    exact hy ▸ (mem_preimage _ _ _ |>.mp h)

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f (preimage f U))` and `preimage f U`.
Interestingly, it is not needed for U to be a subset of Y.-/
theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : 
  preimage f (image f (preimage f U)) = preimage f U := by
    ext x
    rw [mem_preimage', mem_preimage']
    constructor
    · rintro ⟨x, rfl, hx⟩ 
      use x, rfl, image_of_preimage _ _ _ hx
    · rintro ⟨x, rfl, hx⟩ 
      refine ⟨x, rfl, ?_⟩
      rw [mem_image]
      refine ⟨x, ?_, rfl⟩
      rw [mem_preimage]
      exact hx

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
  image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
    intro x hx
    rw [mem_inter]
    simp_rw [mem_image] at hx ⊢
    obtain ⟨x, hx, hfx⟩ := hx
    refine ⟨⟨x, ?_, hfx⟩, ⟨x, ?_, hfx⟩⟩ 
    · exact mem_inter _ _ _ |>.mp hx |>.left
    · exact mem_inter _ _ _ |>.mp hx |>.right

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
  (image f A) \ (image f B) ⊆ image f (A \ B) := by
    intro x hx
    rw [mem_sdiff] at hx
    simp_rw [mem_image] at hx ⊢
    push_neg at hx
    obtain ⟨⟨x, hx, hfx⟩, hb⟩ := hx
    have : x.val ∉ B := fun hB => hb x hB hfx
    refine ⟨x, mem_sdiff _ _ _ |>.mpr ⟨hx, this⟩, hfx⟩ 

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
  image f (A ∪ B) = (image f A) ∪ (image f B) := by
    ext x
    simp_rw [mem_union, mem_image]
    constructor
    · rintro ⟨x, hx, hfx⟩ 
      rcases mem_union _ _ _ |>.mp hx with hx|hx
      exact Or.inl ⟨x, hx, hfx⟩ 
      exact Or.inr ⟨x, hx, hfx⟩ 
    · rintro (⟨x, hx, hfx⟩|⟨x, hx, hfx⟩) 
      exact ⟨x, mem_union _ _ _ |>.mpr (Or.inl hx), hfx⟩ 
      exact ⟨x, mem_union _ _ _ |>.mpr (Or.inr hx), hfx⟩ 

open Classical in
def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  have h0o: (0: Object) ∈ ({0, 1}: Set) := mem_pair _ _ _ |>.mpr (Or.inl rfl)
  have h1o: (1: Object) ∈ ({0, 1}: Set) := mem_pair _ _ _ |>.mpr (Or.inr rfl)
  have h0: (0: Object) ∈ ({0, 1, 2}: Set) := mem_triple _ _ _ _ |>.mpr (Or.inl rfl)
  have h1: (1: Object) ∈ ({0, 1, 2}: Set) := mem_triple _ _ _ _ |>.mpr (Or.inr <| Or.inl rfl)
  have h2: (2: Object) ∈ ({0, 1, 2}: Set) := mem_triple _ _ _ _ |>.mpr (Or.inr <| Or.inr rfl)
  let f : ({0, 1, 2}: Set).toSubtype → ({0, 1}: Set).toSubtype := 
    fun x => if x = ⟨1, h1⟩  then ⟨1, h1o⟩  else ⟨0, h0o⟩
  have hf0 : ↑(f ⟨0, h0⟩) = (0: Object) := by
    unfold f
    rw [if_neg]
    simp
  have hf1 : ↑(f ⟨1, h1⟩) = (1: Object) := by
    unfold f
    rw [if_pos]
    simp
  have hf2 : ↑(f ⟨2, h2⟩) = (0: Object) := by 
    unfold f
    rw [if_neg]
    simp
  use {0, 1, 2}, {0, 1}, f
  use {0, 1}, {1, 2}
  rw [
    show ({0,1}: Set) ∩ {1,2} = {1} by aesop,
    image_singleton h1,
    image_pair h0 h1,
    image_pair h1 h2,
    hf0,
    hf1,
    hf2,
    pair_comm,
    inter_self,
    not_eq_iff
  ]
  use 0
  simp

open Classical in
def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  have h0o: (0: Object) ∈ ({0, 1}: Set) := mem_pair _ _ _ |>.mpr (Or.inl rfl)
  have h1o: (1: Object) ∈ ({0, 1}: Set) := mem_pair _ _ _ |>.mpr (Or.inr rfl)
  have h0: (0: Object) ∈ ({0, 1, 2}: Set) := mem_triple _ _ _ _ |>.mpr (Or.inl rfl)
  have h1: (1: Object) ∈ ({0, 1, 2}: Set) := mem_triple _ _ _ _ |>.mpr (Or.inr <| Or.inl rfl)
  have h2: (2: Object) ∈ ({0, 1, 2}: Set) := mem_triple _ _ _ _ |>.mpr (Or.inr <| Or.inr rfl)
  let f : ({0, 1, 2}: Set).toSubtype → ({0, 1}: Set).toSubtype := 
    fun x => if x = ⟨1, h1⟩  then ⟨1, h1o⟩  else ⟨0, h0o⟩
  have hf0 : ↑(f ⟨0, h0⟩) = (0: Object) := by
    unfold f
    rw [if_neg]
    simp
  have hf1 : ↑(f ⟨1, h1⟩) = (1: Object) := by
    unfold f
    rw [if_pos]
    simp
  have hf2 : ↑(f ⟨2, h2⟩) = (0: Object) := by 
    unfold f
    rw [if_neg]
    simp
  use {0, 1, 2}, {0, 1}, f
  use {0, 1}, {1, 2}
  rw [show ({0, 1}: Set) \ {1, 2} = {0} by aesop]
  simp only [mem_insert, ofNat_inj', zero_ne_one, mem_singleton, OfNat.zero_ne_ofNat, or_self,
    or_false, image_singleton, hf0, one_ne_zero, OfNat.one_ne_ofNat, or_true, image_pair, hf1,
    OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, hf2]
  rw [show ({0, 1}: Set) \ {1, 0} = {} by aesop, not_eq_iff]
  use 0
  simp

/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
  preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
    ext x
    simp_rw [mem_inter, mem_preimage']
    constructor
    · rintro ⟨x, hx, h⟩ 
      rw [mem_inter] at h
      refine ⟨⟨x, hx, h.left⟩, ⟨x, hx, h.right⟩⟩ 
    · rintro ⟨⟨x, hx, h_l⟩,⟨x', hx', h_r⟩⟩ 
      obtain rfl : x = x' := coe_inj _ _ _ |>.mp (hx ▸ hx'.symm)
      use x, hx, mem_inter _ _ _ |>.mpr ⟨h_l, h_r⟩ 


theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
  preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
    ext x
    simp_rw [mem_union, mem_preimage']
    constructor
    · rintro ⟨x, hx, hfx⟩ 
      rcases mem_union _ _ _ |>.mp hfx with hfx|hfx
      exact Or.inl ⟨x, hx, hfx⟩ 
      exact Or.inr ⟨x, hx, hfx⟩ 
    · rintro (⟨x, hx, hfx⟩|⟨x, hx, hfx⟩)
      exact ⟨x, hx, mem_union _ _ _ |>.mpr (Or.inl hfx)⟩ 
      exact ⟨x, hx, mem_union _ _ _ |>.mpr (Or.inr hfx)⟩ 

theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
  preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by
    ext x
    simp_rw [mem_sdiff, mem_preimage']
    push_neg
    constructor
    · rintro ⟨x, hx, h⟩ 
      rw [mem_sdiff] at h
      refine ⟨⟨x, hx, h.left⟩, fun x' hx' => ?_⟩ 
      obtain rfl : x = x' := coe_inj _ _ _ |>.mp (hx ▸ hx'.symm)
      exact h.right
    · rintro ⟨⟨x, hx, hfx⟩, hnB⟩ 
      exact ⟨x, hx, mem_sdiff _ _ _ |>.mpr ⟨hfx, hnB _ hx⟩⟩ 

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
  (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
    constructor
    · intro h y
      replace h := h ({y.val}: Set) (fun _ h => (mem_singleton _ _ |>.mp h) ▸ y.prop)
      replace h := Set.ext_iff.mp h
      replace h := h y.val |>.mpr (mem_singleton _ _ |>.mpr rfl)
      obtain ⟨x, _, hx⟩ := mem_image _ _ _ |>.mp h
      exact ⟨x, coe_inj _ _ _ |>.mp hx⟩ 
    · intro h S hS
      ext y
      rw [mem_image]
      constructor
      · intro ⟨x, hx, hf⟩ 
        rw [mem_preimage] at hx
        exact hf ▸ hx
      · intro hy
        obtain ⟨x, hx⟩ := h ⟨y, hS _ hy⟩ 
        replace hx : ↑(f x) = y := by rw [hx]
        refine ⟨x, ?_, hx⟩ 
        rw [mem_preimage]
        exact hx ▸ hy

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
  (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
    unfold Function.Injective
    constructor
    · intro h x1 x2 hf
      have h := h ({x1.val}: Set) (fun _ h => (mem_singleton _ _ |>.mp h) ▸ x1.prop)
      rw [image_singleton', hf, Set.ext_iff] at h
      replace h := h x2 |>.mp (by rw [mem_preimage, mem_singleton])
      replace h := mem_singleton _ _ |>.mp h
      exact (coe_inj _ _ _).mp h.symm
    intro hf S hS
    ext x
    constructor
    · intro hx
      obtain ⟨x, rfl, h⟩ := mem_preimage' _ _ _ |>.mp hx
      have ⟨x', hS, h⟩ := mem_image _ _ _ |>.mp h
      have : x = x' := hf <| (coe_inj _ _ _).mp h.symm
      exact this ▸ hS
    · intro hx
      rw [mem_preimage']
      use ⟨x, hS _ hx⟩, rfl
      rw [mem_image]
      use ⟨x, hS _ hx⟩

/-- Helper lemma for Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Another helper lemma for Exercise 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f := by
    use union (Y.powerset.replace (P := fun Y'' outer =>
        outer = union (X.powerset.replace (P := fun X'' inner =>
          ∃ (X' Y': Set), Y''.val = ↑Y' ∧ X''.val = ↑X' ∧ inner = (Y' ^ X' :Set)
        ) (by aesop))
      ) (by aesop))
    intro F
    rw [mem_union_powerset_replace_iff]
    constructor
    · rintro ⟨Y'', outer, hY'', h_outer⟩ 
      rw [Function.Embedding.injective set_to_object hY'', mem_union_powerset_replace_iff] at h_outer
      obtain ⟨X'', inner, ⟨X', Y', hY', hX', h_inner⟩, hF⟩ := h_outer
      refine ⟨X', Y', by aesop, by aesop, ?_⟩
      rw [Function.Embedding.injective set_to_object h_inner, powerset_axiom] at hF
      obtain ⟨f, hf⟩ := hF
      use f, hf.symm
    rintro ⟨X', Y', hX', hY', ⟨f, rfl⟩⟩ 
    use ⟨Y', mem_powerset'.mpr hY'⟩
    simp [mem_union_powerset_replace_iff]
    grind only

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation `∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  use union {↑X, ↑Y}
  intro x
  rw [union_axiom]
  constructor
  · rintro ⟨S, hx, hS⟩ 
    obtain hS|hS := mem_pair _ _ _ |>.mp hS
    exact (coe_eq_iff _ _).mp hS ▸ (Or.inl hx)
    exact (coe_eq_iff _ _).mp hS ▸ (Or.inr hx)
  · rintro (hx|hx)
    exact ⟨X, hx, mem_pair _ _ _ |>.mpr (Or.inl rfl)⟩ 
    exact ⟨Y, hx, mem_pair _ _ _ |>.mpr (Or.inr rfl)⟩ 

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
  iInter' I β A = iInter' I β' A := by
    ext x
    unfold iInter'
    rw [specification_axiom'', specification_axiom'']
    constructor
    · exact fun ⟨hx, h⟩ => ⟨h β', h⟩ 
    · exact fun ⟨hx, h⟩ => ⟨h β, h⟩ 


/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
  iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
  ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
  = iUnion (I ∪ J) A := by
    ext x
    simp_rw [mem_union, mem_iUnion]
    constructor
    · rintro (⟨a, ha⟩|⟨a, ha⟩)
      use ⟨ a.val, by simp [a.property]⟩
      use ⟨ a.val, by simp [a.property]⟩
    · rintro ⟨⟨a, ha⟩, h⟩
      obtain ha|ha := mem_union _ _ _ |>.mp ha
      exact Or.inl ⟨⟨a, ha⟩, h⟩ 
      exact Or.inr ⟨⟨a, ha⟩, h⟩ 

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) : I ∪ J ≠ ∅ := by
  apply not_eq_iff.mpr
  obtain ⟨x, hx⟩ := nonempty_def hI
  use x
  simp [hx]

theorem SetTheory.Set.union_of_nonempty' {I J:Set} (hJ: J ≠ ∅) : I ∪ J ≠ ∅ :=
  union_comm _ _ ▸ union_of_nonempty hJ
  

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
  iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
  ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
  = iInter (I ∪ J) (union_of_nonempty hI) A := by
    ext x
    simp_rw [mem_inter, mem_iInter]
    refine ⟨fun ⟨h_mem_I, h_mem_J⟩ x' => ?_, fun h => ⟨fun x' => ?_, fun x' => ?_⟩⟩ 
    · obtain hx'|hx' := mem_union _ _ _ |>.mp x'.prop
      exact h_mem_I ⟨x'.val, hx'⟩ 
      exact h_mem_J ⟨x'.val, hx'⟩ 
    exact h ⟨x'.val, mem_union _ _ _ |>.mpr (Or.inl x'.prop)⟩ 
    exact h ⟨x'.val, mem_union _ _ _ |>.mpr (Or.inr x'.prop)⟩ 

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
  X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by
    ext x
    have : Nonempty I.toSubtype := nonempty_subtype.mpr (nonempty_def hI)
    simp_rw [mem_iInter, mem_sdiff, mem_iUnion, not_exists, forall_and_left]

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
  X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by
    ext x
    simp_rw [mem_iUnion, mem_sdiff, mem_iInter, not_forall, exists_and_left]

end Chapter3
