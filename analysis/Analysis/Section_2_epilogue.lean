import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers `Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers `ℕ`.

After this epilogue, `Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers `ℕ` throughout.  In particular, one should use the full Mathlib API for `ℕ` for
all subsequent chapters, in lieu of the `Chapter2.Nat` API.

Filling the sorries here requires both the Chapter2.Nat API and the Mathlib API for the standard
natural numbers `ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction `Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

theorem Chapter2.Nat.toNat_inj {x y: Nat} : x.toNat = y.toNat ↔ x = y :=
  Function.Injective.eq_iff <| Equiv.injective equivNat

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  · rw [succ_add, toNat, toNat, hn]
    ring


/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n using induction with n ih
  · rw [zero_mul, toNat, _root_.Nat.zero_mul]
  · rw [succ_mul, map_add, toNat, ih]
    ring

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  rw [le_iff]
  constructor
  · rintro h
    obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨x, rfl⟩ : ∃y, (y: Nat).toNat = x := by
      refine ⟨equivNat.invFun x, ?_⟩
      apply equivNat.right_inv
    refine ⟨x, ?_⟩
    rw [← map_add] at hx
    exact toNat_inj.mp hx
  · rintro ⟨x, rfl⟩
    exact map_add _ _ ▸ Nat.le_add_right _ _

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
  induction' m using induction with m ih
  · simp [toNat]
  · rw [pow_succ, toNat, Nat.pow_add_one, map_mul, ih]

/-- The Peano axioms for an abstract type `Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
abbrev Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

@[simp]
lemma Mathlib_Nat.zero_eq : Mathlib_Nat.zero = (0 : ℕ) := rfl

@[simp]
lemma Mathlib_Nat.succ_eq : Mathlib_Nat.succ (n: ℕ) = (n.succ : ℕ) := rfl

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with `unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  rintro a b hab
  induction' a with a ih generalizing b
  · rw [natCast] at hab
    cases' b with b
    · rfl
    · rw [natCast] at hab
      have := P.succ_ne (P.natCast b) |>.symm
      contradiction
  · rw [natCast] at hab
    cases' b with b
    · have := P.succ_ne (P.natCast a)
      rw [natCast] at hab
      contradiction
    · exact Nat.add_right_cancel_iff.mpr <| ih <| P.succ_cancel hab

/-- One can start the proof here with `unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  refine P.induction _ ?_ (fun n ⟨a, ha⟩ => ?_)
  · refine ⟨0, by rw [natCast]⟩
  · refine ⟨a + 1, ?_⟩
    rw [natCast, ha]

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol `≃` is an alias for Mathlib's `Equiv` class; for instance `P.Nat ≃ Q.Nat` is
    an alias for `_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the `Equiv` class.
    Some of this API can be invoked automatically via the `simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero :=
    (Equiv.symm_apply_eq Equiv.equiv).mpr equiv.equiv_zero.symm
  equiv_succ n := by
    apply_fun equiv.equiv
    simp only [equiv.equiv_succ, Equiv.apply_symm_apply]

/-- This exercise will require application of Mathlib's API for the `Equiv` class.
    Some of this API can be invoked automatically via the `simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    have := equiv1.equiv_zero
    have := this ▸ equiv2.equiv_zero
    exact this
  equiv_succ n := by
    have := equiv1.equiv_succ n
    have := this ▸ (equiv2.equiv_succ <| equiv n)
    exact this

instance [inst : Nonempty ℕ] : Nonempty Mathlib_Nat.Nat := inst

/-- Useful Mathlib tools for inverting bijections include `Function.surjInv` and `Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := Function.invFun P.natCast
    left_inv := Function.leftInverse_invFun (natCast_injective _)
    right_inv := Function.rightInverse_invFun (natCast_surjective _)
  }
  equiv_zero := rfl
  equiv_succ _ := rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q :=
  Equiv.trans (Equiv.fromNat P |>.symm) (Equiv.fromNat Q)


/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  revert n; apply P.induction
  · rw [equiv_zero1, equiv_zero2]
  · intro n ih
    rw [equiv_succ1, equiv_succ2, ih]

#check Nat.rec_add_one

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  have ⟨e, equiv_zero, equiv_succ⟩:= Equiv.fromNat P |>.symm
  have equiv_succ : ∀ n, e (P.succ n) = (e n : ℕ).succ := equiv_succ
  let a : P.Nat → P.Nat := fun n => Nat.rec c (fun n prev => f (P.natCast n) prev) (e n)
  apply existsUnique_of_exists_of_unique ⟨a, ?_⟩ ?_
  · refine ⟨?_, ?_⟩ <;>  unfold a
    · rw [equiv_zero, Nat.rec_zero]
    · intro n
      rw [equiv_succ, Nat.rec_add_one]
      congr
      revert n; apply P.induction
      · rw [equiv_zero]
      · intro n ih
        rw [equiv_succ]
        apply P.succ_cancel 
        apply congrArg P.succ 
        apply congrArg P.succ ih
  · rintro x y hx hy
    ext n
    revert n; apply P.induction
    · rw [hx.left, hy.left]
    · intro n ih
      rw [hx.right, hy.right, ih]

end PeanoAxioms
