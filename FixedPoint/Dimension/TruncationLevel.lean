/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Categorical dimension for objects in the Adamek chain.

We define a `TruncationLevel` type mirroring the idea that objects at
position n in the initial chain ⊥ → F(⊥) → F²(⊥) → ⋯ carry a notion
of categorical dimension.  The key definitions are:

  - `TruncationLevel`     : an inductive type with finite and omega levels
  - `chainDimension n`    : maps ℕ to TruncationLevel via iterated dimSucc
  - `HasDimension F X d`  : propositional witness that X is isomorphic to
                            the n-th iterate and n maps to dimension d
  - `dimension_iso_invariant` : dimension is preserved under isomorphism
  - `iterate_has_dimension`   : iterateObj F n has dimension chainDimension n
-/

import FixedPoint.Iteration.InitialChain

open CategoryTheory CategoryTheory.Limits

namespace FixedPoint.Dimension

universe v u

/-! ### TruncationLevel -/

/-- Truncation level for categorical dimension.
    `dimZero` represents the dimension of the initial object,
    `dimSucc` represents the dimension obtained by applying the endofunctor once,
    and `dimOmega` represents the limit (colimit) dimension. -/
inductive TruncationLevel : Type where
  | dimZero : TruncationLevel
  | dimSucc : TruncationLevel → TruncationLevel
  | dimOmega : TruncationLevel
  deriving DecidableEq, Repr

namespace TruncationLevel

/-- Map a natural number to a truncation level: 0 ↦ dimZero, n+1 ↦ dimSucc^{n+1}(dimZero). -/
def chainDimension : ℕ → TruncationLevel
  | 0 => dimZero
  | n + 1 => dimSucc (chainDimension n)

@[simp]
theorem chainDimension_zero : chainDimension 0 = dimZero := rfl

@[simp]
theorem chainDimension_succ (n : ℕ) :
    chainDimension (n + 1) = dimSucc (chainDimension n) := rfl

/-- chainDimension is injective: distinct chain positions give distinct dimensions. -/
theorem chainDimension_injective : Function.Injective chainDimension := by
  intro m n h
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ k =>
      simp only [chainDimension] at h
      exact nomatch h
  | succ m ih =>
    cases n with
    | zero =>
      simp only [chainDimension] at h
      exact nomatch h
    | succ k =>
      simp only [chainDimension, dimSucc.injEq] at h
      exact congrArg Nat.succ (ih h)

end TruncationLevel

/-! ### HasDimension -/

open FixedPoint.Iteration in
/-- `HasDimension F X d` witnesses that object `X` has categorical dimension `d`.
    Concretely, there exists a chain index `n` such that `X ≅ iterateObj F n` and
    `chainDimension n = d`. -/
def HasDimension {C : Type u} [Category.{v} C] [HasInitial C]
    (F : C ⥤ C) (X : C) (d : TruncationLevel) : Prop :=
  ∃ n : ℕ, TruncationLevel.chainDimension n = d ∧ Nonempty (X ≅ iterateObj F n)

/-! ### Dimension is invariant under isomorphism -/

/-- If `X` has dimension `d` and `X ≅ Y`, then `Y` also has dimension `d`. -/
theorem dimension_iso_invariant {C : Type u} [Category.{v} C] [HasInitial C]
    {F : C ⥤ C} {X Y : C} {d : TruncationLevel}
    (hX : HasDimension F X d) (e : X ≅ Y) : HasDimension F Y d := by
  obtain ⟨n, hdim, ⟨i⟩⟩ := hX
  exact ⟨n, hdim, ⟨e.symm ≪≫ i⟩⟩

/-! ### Each iterate has its canonical dimension -/

open FixedPoint.Iteration in
/-- The n-th iterate `iterateObj F n` has dimension `chainDimension n`. -/
theorem iterate_has_dimension {C : Type u} [Category.{v} C] [HasInitial C]
    (F : C ⥤ C) (n : ℕ) :
    HasDimension F (iterateObj F n) (TruncationLevel.chainDimension n) :=
  ⟨n, rfl, ⟨Iso.refl _⟩⟩

/-! ### The initial object has dimension zero -/

open FixedPoint.Iteration in
/-- The initial object ⊥ has dimension dimZero. -/
theorem initial_has_dimZero {C : Type u} [Category.{v} C] [HasInitial C]
    (F : C ⥤ C) : HasDimension F (⊥_ C) TruncationLevel.dimZero :=
  iterate_has_dimension F 0

/-! ### F applied to an object increases dimension by one -/

open FixedPoint.Iteration in
/-- If `iterateObj F n` has dimension `chainDimension n`, then
    `F.obj (iterateObj F n)` has dimension `chainDimension (n + 1)`. -/
theorem functor_succ_dimension {C : Type u} [Category.{v} C] [HasInitial C]
    (F : C ⥤ C) (n : ℕ) :
    HasDimension F (iterateObj F (n + 1)) (TruncationLevel.chainDimension (n + 1)) :=
  iterate_has_dimension F (n + 1)

/-! ### Dimension uniqueness -/

/-- If an object has dimension `d₁` and `d₂`, and both are witnessed by the
    same chain index, then `d₁ = d₂`. -/
theorem dimension_unique_at_index {C : Type u} [Category.{v} C] [HasInitial C]
    {F : C ⥤ C} {X : C} {d₁ d₂ : TruncationLevel}
    (h₁ : HasDimension F X d₁) (h₂ : HasDimension F X d₂)
    (heq : h₁.choose = h₂.choose) : d₁ = d₂ := by
  have := h₁.choose_spec.1
  have := h₂.choose_spec.1
  rw [← ‹TruncationLevel.chainDimension h₁.choose = d₁›,
      ← ‹TruncationLevel.chainDimension h₂.choose = d₂›, heq]

end FixedPoint.Dimension
