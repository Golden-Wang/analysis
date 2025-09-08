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
  contrapose! h'; simp at h'
  aesop

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  let P : Object → Prop := fun x ↦ false
  obtain ⟨S, hS⟩ := h P
  use S
  intro x
  by_contra h1
  rw[hS] at h1
  contradiction

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  let P : Object → Prop := fun y ↦ ∃ X:Set, y = x
  obtain ⟨S, hS⟩ := h P
  use S
  simp [P] at hS
  exact hS

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  let P : Object → Prop := fun y ↦ ∃ X:Set, y = x₁ ∨ y = x₂
  obtain ⟨S, hS⟩ := h P
  use S
  simp [P] at hS
  exact hS

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  let P : Object → Prop := fun x ↦ ∃ X:Set, x ∈ A ∨ x ∈ B
  obtain ⟨S, hS⟩ := h P
  use S
  simp [P] at hS
  exact hS

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  let Q : Object → Prop := fun x ↦ ∃ h1 : x ∈ A, P ⟨ x, h1 ⟩
  obtain ⟨S, hS⟩ := h Q
  use S

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  let P : Object → Prop := fun x ↦ ∃ a : A, P a x
  obtain ⟨S, hS⟩ := h P
  use S

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  by_contra h
  have h1: {(A: Object)} ≠ (∅: Set) := by
    apply nonempty_of_inhabited
    apply (mem_singleton (set_to_object A) A).2
    rfl
  apply axiom_of_regularity at h1
  obtain ⟨x, hs⟩ := h1
  have h2 := x.property
  rw [mem_singleton] at h2
  apply hs A at h2
  rw [disjoint_iff] at h2
  have h3 := (mem_singleton (set_to_object A) A).2 rfl
  apply And.intro h at h3
  rw [← mem_inter, h2] at h3
  exact not_mem_empty (set_to_object A) h3

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  by_contra h; push_neg at h
  have h1: {(A: Object), (B: Object)} ≠ (∅: Set) := by
    apply nonempty_of_inhabited
    apply (mem_pair (set_to_object A) A B).2
    left; rfl
  apply axiom_of_regularity at h1
  obtain ⟨x, hs⟩ := h1
  have h2 := x.property
  rw [mem_pair] at h2
  rcases h2 with h2a|h2b
  . apply hs A at h2a
    rw [disjoint_iff] at h2a
    have h3: (B: Object) ∈ ({(A: Object), (B: Object)}: Set) := by
      apply (mem_pair (set_to_object B) A B).2
      right; rfl
    apply And.intro h.right at h3
    rw [← mem_inter, h2a] at h3
    exact not_mem_empty (set_to_object B) h3
  apply hs B at h2b
  rw [disjoint_iff] at h2b
  have h3: (A: Object) ∈ ({(A: Object), (B: Object)}: Set) := by
    apply (mem_pair (set_to_object A) A B).2
    left; rfl
  apply And.intro h.left at h3
  rw [← mem_inter, h2b] at h3
  exact not_mem_empty (set_to_object A) h3

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U:Set), ∀ x, x ∈ U := by
  constructor
  . intro h
    let P : Object → Prop := fun x ↦ true
    obtain ⟨S, hS⟩ := h P
    simp [P] at hS
    use S
  intro ⟨U, h⟩
  unfold axiom_of_universal_specification
  intro P
  let P': U → Prop := fun x ↦ P x
  use (U.specify P')
  intro x
  let x': U := ⟨x, h x⟩
  exact specification_axiom' P' x'

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  rw [← univ_iff]
  exact Russells_paradox

end Chapter3
