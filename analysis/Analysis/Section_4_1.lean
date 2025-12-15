import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ.

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl x := rfl
    symm h := h.symm
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [PreInt.eq, Int.eq] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa [Int.eq]
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  rw [← natCast_inj, natCast_ofNat]

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro ⟨a, b⟩ ⟨c, d⟩ heq
    simp [Int.eq, add_comm] at heq ⊢
    exact heq.symm
  )

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms 
    (fun a b c => by
      obtain ⟨a1, a2, rfl⟩ := eq_diff a
      obtain ⟨b1, b2, rfl⟩ := eq_diff b
      obtain ⟨c1, c2, rfl⟩ := eq_diff c
      simp [add_eq, add_assoc]
    ) 
    (fun a => by
      obtain ⟨a1, a2, rfl⟩ := eq_diff a
      simp [ofNat_eq, add_eq]
    ) 
    (fun a => by
      obtain ⟨a1, a2, rfl⟩ := eq_diff a
      simp [ofNat_eq, neg_eq, add_eq, Int.eq, add_comm]
    ) 

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm a b := by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
    simp [add_eq, add_comm]

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := fun a b => by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
    simp [mul_eq, mul_comm, add_comm]
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul a := by 
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    simp [ofNat_eq, mul_eq]
  mul_one a := by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    simp [ofNat_eq, mul_eq]

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib a b c := by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
    obtain ⟨c1, c2, rfl⟩ := eq_diff c
    simp [mul_eq, add_eq]
    ring_nf
  right_distrib a b c := by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
    obtain ⟨c1, c2, rfl⟩ := eq_diff c
    simp [mul_eq, add_eq]
    ring_nf
  zero_mul a := by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    simp [ofNat_eq, mul_eq]
  mul_zero a := by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    simp [ofNat_eq, mul_eq]

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  simp [natCast_eq, sub_eq, neg_eq, add_eq]

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ha := trichotomous a
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  simp [ofNat_eq, mul_eq, Int.eq, IsPos, IsNeg, natCast_eq, neg_eq, Int.eq] at ha h ⊢
  rcases ha with (h|⟨n, hn, rfl⟩|⟨n, hn, rfl⟩)
  · exact Or.inl h
  · ring_nf at h
    simp at h
    exact Or.inr <| h.elim id (Nat.ne_zero_of_lt hn · |>.elim)
  · ring_nf at h
    simp [mul_comm] at h
    exact Or.inr <| h.elim Eq.symm (Nat.ne_zero_of_lt hn · |>.elim)

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  rcases trichotomous c |>.elim (False.elim ∘ hc) id with ⟨c, hc, rfl⟩|⟨c, hc, rfl⟩
  <;> simp [natCast_eq, ofNat_eq, mul_eq, Int.eq, ← add_mul, neg_eq] at hc h ⊢
  · exact h.elim id (False.elim ∘ hc)
  · replace h := h.elim id (False.elim ∘ (Ne.symm hc))
    ring_nf at h ⊢
    exact h.symm

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

theorem Int.add_zero (a:Int): a + 0 = a := by simp

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  rw [lt_iff]
  constructor
  · rintro ⟨⟨n, hn⟩, hab⟩
    have : n ≠ 0 := fun h => hab (by
      rw [h, show @Nat.cast Int instNatCast 0 = (0: Int) by rfl, add_zero] at hn
      exact hn.symm
    )
    exact ⟨n, this, hn⟩
  rintro ⟨n, hn, rfl⟩
  refine ⟨Exists.intro n rfl, ?_⟩
  by_contra h
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  simp [natCast_eq, ofNat_eq, Int.eq] at h
  exact hn h

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  simp [lt_iff] at h ⊢
  obtain ⟨⟨n, hn⟩, hab⟩ := h
  exact ⟨⟨n, hn ▸ by abel⟩, hab⟩

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  simp only [lt_iff, zero_add] at hab hc ⊢
  obtain ⟨⟨c, rfl⟩, hc⟩ := hc
  obtain ⟨⟨n, hn⟩, hab⟩ := hab
  refine ⟨⟨n * c, hn ▸ ?_⟩, ?_⟩
  · simp [add_mul]
  by_contra h
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  simp [natCast_eq, Int.eq, mul_eq, ← add_mul, ofNat_eq] at h hab hc
  exact h.elim hab (Ne.symm hc)

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  simp [lt_iff, natCast_eq, add_eq, Int.eq, neg_eq] at h ⊢
  ring_nf at h ⊢
  obtain ⟨⟨n, hn⟩, hab⟩ := h
  exact ⟨⟨n, hn ▸ by ring⟩, hab⟩


/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  simp [le_iff, natCast_eq, add_eq, Int.eq, neg_eq] at h ⊢
  ring_nf at h ⊢
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn ▸ by ring⟩

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  simp [lt_iff, natCast_eq] at hab hbc ⊢
  obtain ⟨⟨n, rfl⟩, hab⟩ := hab
  obtain ⟨⟨m, rfl⟩, hbc⟩ := hbc
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  simp [add_eq, Int.eq] at hab hbc ⊢
  exact ⟨⟨n + m, Nat.add_assoc ..⟩, by omega⟩

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  rcases trichotomous (a - b) with (h|h|h)
  all_goals
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
  · refine Or.inr (Or.inr ?_)
    simp [sub_eq, neg_eq, add_eq, ofNat_eq, Int.eq] at h ⊢
    ring_nf at h ⊢
    exact h
  · refine Or.inl ?_
    simp [sub_eq, neg_eq, add_eq, IsPos, natCast_eq, Int.eq, lt_iff] at h ⊢
    ring_nf at h ⊢
    obtain ⟨n, hn, hab⟩ := h
    refine ⟨Exists.intro n (hab ▸ by ring), hab ▸ ?_⟩
    omega
  · refine Or.inr (Or.inl ?_)
    simp [sub_eq, neg_eq, add_eq, IsNeg, natCast_eq, Int.eq, lt_iff] at h ⊢
    ring_nf at h ⊢
    obtain ⟨n, hn, hab⟩ := h
    refine ⟨Exists.intro n (hab ▸ by ring), hab ▸ ?_⟩
    omega

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  simp [lt_iff, Int.eq, natCast_eq, add_eq]
  intro n hn hba m hm
  omega

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by 
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  simp [lt_iff, Int.eq, natCast_eq, add_eq]
  intro n hn hba m
  omega

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b) :=
  eq_comm.eq ▸ not_gt_and_eq b a

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        simp [le_iff, natCast_eq, add_eq, Int.eq]
        obtain ⟨t, ht⟩ := h.dest
        ring_nf at ht ⊢
        exact ⟨t, ht ▸ rfl⟩
      | isFalse h =>
        apply isFalse
        simp [le_iff, natCast_eq, add_eq, Int.eq] at h ⊢
        ring_nf at h ⊢
        intro x hx
        omega
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by 
  simp only [left_eq_add, forall_const]

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl a := ⟨0, left_eq_add.mpr rfl⟩
  le_trans a b c := by
    simp [le_iff]
    intro n hba m hcb
    use n + m
    simp [hba, hcb, add_assoc]
  lt_iff_le_not_ge a b := by
    simp [lt_iff, le_iff]
    rintro n rfl
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    simp [← not_exists, not_iff_not, natCast_eq, add_eq, Int.eq]
    refine ⟨fun h => Exists.intro 0 (h.symm ▸ rfl), ?_⟩
    intro ⟨x,hx⟩
    omega
  le_antisymm a b := by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
    simp [le_iff, natCast_eq, add_eq, Int.eq]
    intro m hm n hn
    omega
  le_total a b := by
    rcases trichotomous' a b with (h|h|rfl)
    · exact Or.inr h.left
    · exact Or.inl h.left
    exact Or.inl ⟨0, left_eq_add.mpr rfl⟩
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by simp 

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  use fun x => x > -1
  have h1 : (-1: Int) < 0 := sign_eq_neg_one_iff.mp rfl
  simp [h1]
  refine ⟨?_, -1, le_refl _⟩
  intro n hn
  apply lt_trans hn
  exact ⟨⟨1, rfl⟩, by 
    obtain ⟨n1, n2, rfl⟩ := eq_diff n
    simp
  ⟩

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  obtain ⟨n1, n2, rfl⟩ := eq_diff n
  simp [le_iff, natCast_eq, mul_eq, eq] at h ⊢
  obtain ⟨t, rfl⟩ := h
  use t * t
  ring

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  rcases trichotomous n with rfl|h|h
  · simp
  all_goals
    obtain ⟨n1, n2, rfl⟩ := eq_diff n
    simp [IsPos, IsNeg, natCast_eq, eq, mul_eq, neg_eq, le_iff] at h ⊢
    obtain ⟨n, h, rfl⟩ := h
    ring_nf at h ⊢
    exact ⟨n ^ 2, by ring⟩

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have := sq_nonneg n
  obtain ⟨m, hm⟩ := le_iff _ _ |>.mp this
  refine ⟨m, ?_⟩
  simp [hm]

/--
  Not in textbook: create an equivalence between Int and ℤ.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    simp at ⊢ h
    grind
  )
  invFun z := if z ≥ 0 then z.toNat else -(-z).toNat
  left_inv n := by
    obtain ⟨n1, n2, rfl⟩ := eq_diff n
    simp
    by_cases h : n2 ≤ n1
    · simp [h, natCast_eq, sub_eq, neg_eq, add_eq]
    simp [h, Nat.cast_sub (Nat.le_of_not_ge h), natCast_eq, sub_eq, neg_eq, add_eq]
  right_inv n := by
    by_cases hn : 0 ≤ n
    <;> simp [hn, natCast_eq, neg_eq]
    omega

example (a b c : ℤ) : a ≤ b - c ↔ a + c ≤ b := by exact Iff.symm Int.add_le_iff_le_sub

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' x y := by
    obtain ⟨x1, x2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, rfl⟩ := eq_diff y
    simp [add_eq]
    ring
  map_mul' x y := by
    obtain ⟨x1, x2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, rfl⟩ := eq_diff y
    simp [mul_eq]
    ring
  map_le_map_iff' := by
    intro x y
    obtain ⟨x1, x2, rfl⟩ := eq_diff x
    obtain ⟨y1, y2, rfl⟩ := eq_diff y
    simp [le_iff, natCast_eq, add_eq, eq, sub_add_eq_add_sub, ← Int.add_le_iff_le_sub]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.dest
      use n
      omega
    rintro ⟨n, hn⟩
    omega


end Section_4_1
