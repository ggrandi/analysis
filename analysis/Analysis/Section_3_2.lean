import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.2: Russell's paradox

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification).
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- This proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  choose Ω hΩ using h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  rw [←hΩ] at this
  contradiction

/-- Axiom 3.9 (Regularity) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  choose x h h' using regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS; specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'
  simp at h'
  exact ⟨_, and_comm.mp h'.choose_spec⟩
  
/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  choose X hX using h (fun x => False)
  refine ⟨X, fun x => ?_⟩
  exact (iff_false_right id).mp (hX x)

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  choose X hX using h (· = x)
  exact ⟨X, (hX ·)⟩

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  choose X hX using h (fun y => y = x₁ ∨ y = x₂)
  exact ⟨X, (hX ·)⟩

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  choose X hX using h (fun y => y ∈ A ∨ y ∈ B)
  exact ⟨X, (hX ·)⟩

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  choose X hX using h (fun z => ∃ h : z ∈ A, P ⟨ z, h ⟩)
  exact ⟨X, (hX ·)⟩

set_option linter.unusedVariables false in
/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  choose X hX using h (fun y => ∃ a : A, P a y)
  exact ⟨X, (hX ·)⟩

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  have ⟨x, hx⟩ := axiom_of_regularity (A := {(A : Object)}) (fun h =>
    have h1 := mem_singleton _ _ |>.mpr rfl
    have h2 := h ▸ not_mem_empty _
    h2 h1)
  simp [disjoint_iff, eq_empty_iff_forall_notMem] at hx
  specialize hx A (mem_singleton _ _ |>.mp x.prop)
  contrapose! hx with h
  exact ⟨A, h, rfl⟩

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  /- by_contra! h -/
  let C: Set := {(A: Object), (B: Object)}
  have hAC : (A: Object) ∈ C := mem_pair _ _ _ |>.mpr (Or.inl rfl)
  have hBC : (B: Object) ∈ C := mem_pair _ _ _ |>.mpr (Or.inr rfl)
  have : C ≠ ∅ := nonempty_of_inhabited hAC
  have ⟨x, h⟩ := axiom_of_regularity this
  contrapose! h
  rcases mem_pair _ _ _ |>.mp x.prop with hA|hB
  · exact ⟨A, hA, not_disjoint_iff _ _ |>.mpr ⟨B, h.right, hBC⟩⟩ 
  · exact ⟨B, hB, not_disjoint_iff _ _ |>.mpr ⟨A, h.left, hAC⟩⟩ 

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔ ∃ (U:Set), ∀ x, x ∈ U := by
  refine ⟨fun h => ?_, fun ⟨U, hU⟩ P => ?_⟩ 
  · choose U hU using h (fun _ => True)
    exact ⟨U, fun x => iff_true (_ ∈ U) ▸ hU x⟩ 
  · refine ⟨U.specify (P ·.val), fun x => ?_⟩ 
    simp [hU]

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := univ_iff.not.mp Russells_paradox

end Chapter3
