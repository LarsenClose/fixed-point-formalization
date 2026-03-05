/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

DimensionIncrement typeclass: endofunctors that raise dimension by exactly 1.

Wraps the core dimension-increment and graded-filtration results into a
typeclass interface so downstream code can abstract over any functor with
this property rather than re-stating the hypotheses.

Key definitions and results:
  - `DimensionIncrement F` : typeclass asserting F increments chain dimension by 1
  - `DimensionIncrement` instance for `ihom A` (from `functor_increments_dimension`)
  - `dimensionIncrement_no_finite_dim_at_fixedpoint` : wraps `no_finite_dimension_at_fixedpoint`
  - `dimensionIncrement_has_all_higher_dims` : wraps `fixedpoint_has_all_higher_dims`
  - `dimensionIncrement_graded` : wraps `graded_filtration`

STATUS: Tier 1 (0 sorry).
-/

import FixedPoint.Dimension.GradedFiltration

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open FixedPoint.Dimension.TruncationLevel

namespace FixedPoint.Dimension

universe v u

variable {C : Type u} [Category.{v} C] [HasInitial C]

/-! ### The DimensionIncrement typeclass -/

/-- An endofunctor `F` has the dimension-increment property if, whenever an
    object `X` has dimension `chainDimension n`, the image `F(X)` has
    dimension `chainDimension (n + 1)`. -/
class DimensionIncrement (F : C ⥤ C) : Prop where
  increments : ∀ (X : C) (n : ℕ),
    HasDimension F X (chainDimension n) →
    HasDimension F (F.obj X) (chainDimension (n + 1))

/-! ### Every endofunctor satisfies DimensionIncrement

The property follows from `functor_increments_dimension`, which holds for
any endofunctor on a category with an initial object. -/

/-- Every endofunctor on a category with an initial object increments dimension. -/
instance (F : C ⥤ C) : DimensionIncrement F :=
  ⟨fun _ _ h => functor_increments_dimension F h⟩

/-! ### Typeclass-based wrappers of the graded filtration results -/

/-- A fixed point with unique dimension cannot have any finite dimension.
    Wraps `no_finite_dimension_at_fixedpoint` using the `DimensionIncrement` typeclass. -/
theorem dimensionIncrement_no_finite_dim_at_fixedpoint
    {F : C ⥤ C} [DimensionIncrement F] {L : C} {n : ℕ}
    (lamb : F.obj L ≅ L) (huniq : HasUniqueDimension F L)
    (hL : HasDimension F L (chainDimension n)) : False :=
  no_finite_dimension_at_fixedpoint lamb huniq hL

/-- If a fixed point has dimension `chainDimension n`, then it has all higher
    dimensions `chainDimension (n + k)` for every `k`.
    Wraps `fixedpoint_has_all_higher_dims` using the `DimensionIncrement` typeclass. -/
theorem dimensionIncrement_has_all_higher_dims
    {F : C ⥤ C} [DimensionIncrement F] {L : C} {n : ℕ}
    (lamb : F.obj L ≅ L) (hL : HasDimension F L (chainDimension n)) :
    ∀ k, HasDimension F L (chainDimension (n + k)) :=
  fixedpoint_has_all_higher_dims lamb hL

/-- The graded filtration theorem expressed via the `DimensionIncrement` typeclass.
    Wraps `graded_filtration`: canonical dims, increment, strict grading, stability. -/
theorem dimensionIncrement_graded
    (F : C ⥤ C) [DimensionIncrement F] (L : C) (lamb : F.obj L ≅ L) :
    (∀ n, HasDimension F (iterateObj F n) (chainDimension n)) ∧
    (∀ (X : C) (n : ℕ), HasDimension F X (chainDimension n) →
      HasDimension F (F.obj X) (chainDimension (n + 1))) ∧
    (∀ n m : ℕ, n ≠ m → chainDimension n ≠ chainDimension m) ∧
    (∀ d : TruncationLevel,
      HasDimension F L d ↔ HasDimension F (F.obj L) d) :=
  graded_filtration F L lamb

/-! ### Instance for ihom(A) -/

section Substrate

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C]
variable [HasInitial C]
variable {A : C} [Closed A] [TensorLeftFinitelyPresentable A]

/-- `ihom A` increments dimension by 1. This is an instance of the general
    `DimensionIncrement` property, specialized to the internal-hom endofunctor. -/
example : DimensionIncrement (ihom A) := inferInstance

end Substrate

end FixedPoint.Dimension
