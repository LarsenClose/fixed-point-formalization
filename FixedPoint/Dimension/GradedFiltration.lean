/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

The Graded Filtration Theorem.

Unifies the three dimension results (T1: dimension definition, T2: F increments
by 1, T2.5: stabilization) into a single theorem: the Adamek chain is a strict
N-indexed filtration by dimension.

Key results:
  - `chain_is_graded`                  : distinct chain positions give distinct
                                         dimensions (strict grading)
  - `fixedpoint_has_all_higher_dims`   : if a fixed point has dim n, it also
                                         has dim n+k for all k
  - `no_finite_dimension_at_fixedpoint`: under a unique-dimension assumption,
                                         a fixed point cannot have any finite dim
  - `graded_filtration`                : the combined master theorem
-/

import FixedPoint.Dimension.Stabilization

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open FixedPoint.Dimension.TruncationLevel

namespace FixedPoint.Dimension

universe v u

variable {C : Type u} [Category.{v} C] [HasInitial C]

/-! ### Strict grading: distinct positions give distinct dimensions -/

/-- Distinct chain positions have distinct dimensions.
    For all n != m, `chainDimension n != chainDimension m`. -/
theorem chain_is_graded {n m : ℕ} (h : n ≠ m) :
    chainDimension n ≠ chainDimension m :=
  fun heq => h (chainDimension_injective heq)

/-! ### Dimensional consequences at fixed points -/

/-- If a fixed point L has dimension `chainDimension n`, then L also has
    dimension `chainDimension (n + 1)`.

    Proof: L has dim n, so F(L) has dim n+1 by increment. But F(L) ≅ L
    by Lambek, so L has dim n+1. -/
theorem fixedpoint_has_succ_dim {F : C ⥤ C} {L : C} {n : ℕ}
    (lamb : F.obj L ≅ L) (hL : HasDimension F L (chainDimension n)) :
    HasDimension F L (chainDimension (n + 1)) :=
  fixedpoint_dimension_stable_inv lamb (functor_increments_dimension F hL)

/-- If a fixed point L has dimension `chainDimension n`, then for all k,
    L has dimension `chainDimension (n + k)`.

    This is the iteration of `fixedpoint_has_succ_dim`. -/
theorem fixedpoint_has_all_higher_dims {F : C ⥤ C} {L : C} {n : ℕ}
    (lamb : F.obj L ≅ L) (hL : HasDimension F L (chainDimension n)) :
    ∀ k, HasDimension F L (chainDimension (n + k))
  | 0 => by rwa [Nat.add_zero]
  | k + 1 => by
    rw [Nat.add_succ]
    exact fixedpoint_has_succ_dim lamb (fixedpoint_has_all_higher_dims lamb hL k)

/-- **Unique dimension property**: an object has at most one dimension.
    This holds when the chain is non-collapsing (no two distinct iterates
    are isomorphic). We state it as a hypothesis rather than proving it
    in general, since it depends on the specific functor. -/
def HasUniqueDimension (F : C ⥤ C) (X : C) : Prop :=
  ∀ d₁ d₂, HasDimension F X d₁ → HasDimension F X d₂ → d₁ = d₂

/-- A fixed point with unique dimension cannot have any finite dimension
    `chainDimension n`.

    Proof: if L has dim `chainDimension n`, then by `fixedpoint_has_succ_dim`
    L also has dim `chainDimension (n+1)`. By uniqueness,
    `chainDimension n = chainDimension (n+1)`, so `n = n+1` by
    `chainDimension_injective`, contradiction. -/
theorem no_finite_dimension_at_fixedpoint {F : C ⥤ C} {L : C} {n : ℕ}
    (lamb : F.obj L ≅ L) (huniq : HasUniqueDimension F L)
    (hL : HasDimension F L (chainDimension n)) : False := by
  have hsucc := fixedpoint_has_succ_dim lamb hL
  have heq := huniq _ _ hL hsucc
  exact absurd (chainDimension_injective heq) (Nat.succ_ne_self n ∘ Eq.symm)

/-! ### The master theorem -/

/-- **Graded Filtration Theorem.** The Adamek chain is a strict N-indexed
    filtration by dimension, and at the fixed point dimension stabilizes.

    This theorem packages the four key properties of the dimension filtration:

    1. **Canonical dimensions**: Each iterate `iterateObj F n` has dimension
       `chainDimension n`.

    2. **Functor increments**: If X has dimension `chainDimension n`, then
       `F(X)` has dimension `chainDimension (n + 1)`.

    3. **Strict grading**: Distinct chain positions give distinct dimensions:
       `n != m → chainDimension n != chainDimension m`.

    4. **Fixed-point stability**: At a fixed point (F(L) ≅ L), dimension is
       invariant: `HasDimension F L d ↔ HasDimension F (F.obj L) d`. -/
theorem graded_filtration (F : C ⥤ C) (L : C) (lamb : F.obj L ≅ L) :
    -- (1) Each iterate has its canonical dimension
    (∀ n, HasDimension F (iterateObj F n) (chainDimension n)) ∧
    -- (2) F increments dimension by 1
    (∀ (X : C) (n : ℕ), HasDimension F X (chainDimension n) →
      HasDimension F (F.obj X) (chainDimension (n + 1))) ∧
    -- (3) Strict grading: distinct positions give distinct dimensions
    (∀ n m : ℕ, n ≠ m → chainDimension n ≠ chainDimension m) ∧
    -- (4) At the fixed point, dimension is stable
    (∀ d : TruncationLevel,
      HasDimension F L d ↔ HasDimension F (F.obj L) d) :=
  ⟨iterate_has_dimension F,
   fun _ _ h => functor_increments_dimension F h,
   fun _ _ h => chain_is_graded h,
   fun _ => fixedpoint_dimension_iff lamb⟩

end FixedPoint.Dimension
