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

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  rw [succ_toNat n]
  rw [succ_add, succ_toNat]
  rw [hn, add_right_comm]

/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  . change (0 * m).toNat = 0 * m.toNat
    rw [zero_mul]
    rw [_root_.Nat.zero_mul]
  rw [succ_mul, map_add, hn]
  rw [succ_toNat]
  rw [_root_.Nat.add_mul, _root_.Nat.one_mul]

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  constructor
  . intro h
    rw [le_iff_exists_add] at h
    obtain ⟨x, h⟩ := h
    have hx :=  equivNat.right_inv x
    simp at hx
    rw [← hx] at h
    rw [← map_add] at h
    use x
    apply_fun equivNat
    simp
    exact h
  intro h
  obtain ⟨x, h⟩ := h
  rw[le_iff_exists_add]
  apply_fun equivNat at h
  simp at h
  rw [map_add] at h
  rw [h]
  use (x.toNat)

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = n^m := by
  induction' m with d hd
  . change n.toNat ^ 0 = n ^ 0
    rw [pow_zero, _root_.pow_zero]
  rw [pow_succ]
  rw [succ_toNat]
  rw [pow_add]
  rw [hd]
  rw [_root_.pow_one]
  congr
  apply equivNat.left_inv

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
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with `unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast  := by
  unfold Function.Injective
  intro x y h
  induction x generalizing y with
  | zero =>
    rw [natCast] at h
    cases y with
    | zero => rfl
    | succ y' =>
      rw [natCast] at h
      symm at h
      apply P.succ_ne at h
      contradiction
  | succ x' ih =>
    rw [← _root_.Nat.succ_eq_add_one] at h
    rw [natCast] at h
    cases y with
    | zero =>
      rw [natCast] at h
      apply P.succ_ne at h
      contradiction
    | succ y' =>
      rw [← _root_.Nat.succ_eq_add_one] at h
      rw [natCast] at h
      apply P.succ_cancel at h
      apply ih at h
      rw [h]

/-- One can start the proof here with `unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  unfold Function.Surjective
  intro b
  revert b; apply P.induction
  . use Nat.zero
  intro n h
  obtain ⟨b, h⟩ := h
  use (Nat.succ b)
  rw [natCast]
  rw [h]

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
  equiv_zero := by
    apply_fun equiv.equiv
    rw [Equiv.apply_symm_apply]
    symm
    exact equiv.equiv_zero
  equiv_succ n := by
    apply_fun equiv.equiv
    rw [Equiv.apply_symm_apply]
    rw [equiv.equiv_succ]
    rw [Equiv.apply_symm_apply]

/-- This exercise will require application of Mathlib's API for the `Equiv` class.
    Some of this API can be invoked automatically via the `simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    rw [Equiv.trans_apply]
    rw [equiv1.equiv_zero, equiv2.equiv_zero]
  equiv_succ n := by
    rw [Equiv.trans_apply]
    rw [equiv1.equiv_succ, equiv2.equiv_succ]
    rw [Equiv.trans_apply]

/-- Useful Mathlib tools for inverting bijections include `Function.surjInv` and `Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := by apply Function.invFun P.natCast
    left_inv := by apply Function.leftInverse_invFun (natCast_injective P)
    right_inv := by apply Function.rightInverse_invFun (natCast_surjective P)
  }
  equiv_zero := by rfl
  equiv_succ n := by rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q := by
  have h1 := Equiv.symm (Equiv.fromNat P)
  have h2 := Equiv.fromNat Q
  exact Equiv.trans h1 h2

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  revert n; apply induction
  . rw [equiv_zero1, equiv_zero2]
  intro n h
  rw [equiv_succ1, equiv_succ2]
  rw [h]

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  apply existsUnique_of_exists_of_unique
  . let equiv := Equiv.fromNat P
    let f': ℕ → ℕ → ℕ := fun x y => equiv.equiv.symm (f (equiv.equiv x) (equiv.equiv y))
    use fun (n: P.Nat) => equiv.equiv (Nat.rec (equiv.equiv.symm c) f' (equiv.equiv.symm n))
    constructor
    . unfold f'
      have h: equiv.equiv.symm P.zero = (0: ℕ) := by
        apply_fun equiv.equiv
        rw [Equiv.apply_symm_apply]
        symm
        exact equiv.equiv_zero
      rw [h]
      rw [Nat.rec_zero]
      rw [Equiv.apply_symm_apply]
    intro n
    unfold f'
    have h: equiv.equiv.symm (P.succ n) = Nat.succ (equiv.equiv.symm n) := by
      apply_fun equiv.equiv
      rw [Equiv.apply_symm_apply]
      rw [show Nat.succ = Mathlib_Nat.succ from rfl]
      rw [equiv.equiv_succ]
      rw [Equiv.apply_symm_apply]
    rw [h]
    simp only [Equiv.apply_symm_apply]
  intro y₁ y₂
  intro h1 h2
  ext n
  revert n; apply induction
  . rw [h1.left, h2.left]
  intro n h
  rw [h1.right, h2.right]
  rw [h]

end PeanoAxioms
