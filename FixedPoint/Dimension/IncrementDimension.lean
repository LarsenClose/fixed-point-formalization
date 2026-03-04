/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Applying the endofunctor F increases dimension by exactly 1.

Given an endofunctor F : C ⥤ C on a category with an initial object,
if an object X has dimension n (i.e., X ≅ F^n(⊥)), then F(X) has
dimension n+1 (i.e., F(X) ≅ F^{n+1}(⊥)).

Key results:
  - `functor_increments_dimension` : HasDimension F X (chainDimension n) →
      HasDimension F (F.obj X) (chainDimension (n+1))
  - `functor_maps_dimSucc` : HasDimension F X d → (∃ n, chainDimension n = d) →
      HasDimension F (F.obj X) (dimSucc d)
-/

import FixedPoint.Dimension.TruncationLevel

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open FixedPoint.Dimension.TruncationLevel

namespace FixedPoint.Dimension

universe v u

variable {C : Type u} [Category.{v} C] [HasInitial C]

/-- If X has dimension n, then F(X) has dimension n+1.

The proof proceeds as follows:
1. From `HasDimension F X (chainDimension n)`, extract m with
   `chainDimension m = chainDimension n` and `X ≅ iterateObj F m`.
2. By `chainDimension_injective`, m = n, so `X ≅ iterateObj F n`.
3. Applying F gives `F(X) ≅ F(iterateObj F n) = iterateObj F (n+1)`.
4. Therefore `F(X)` has dimension `chainDimension (n+1)`. -/
theorem functor_increments_dimension (F : C ⥤ C) {X : C} {n : ℕ}
    (hX : HasDimension F X (chainDimension n)) :
    HasDimension F (F.obj X) (chainDimension (n + 1)) := by
  obtain ⟨m, hm, ⟨iso⟩⟩ := hX
  have hmn : m = n := chainDimension_injective hm
  subst hmn
  exact ⟨m + 1, rfl, ⟨F.mapIso iso⟩⟩

/-- Corollary: if X has a finite dimension d, then F(X) has dimension dimSucc d.

This restates `functor_increments_dimension` using an arbitrary truncation level d
rather than a specific chain dimension. -/
theorem functor_maps_dimSucc (F : C ⥤ C) {X : C} {d : TruncationLevel}
    (hX : HasDimension F X d) (hfin : ∃ n, chainDimension n = d) :
    HasDimension F (F.obj X) (TruncationLevel.dimSucc d) := by
  obtain ⟨n, rfl⟩ := hfin
  exact functor_increments_dimension F hX

/-- If X has dimension 0, then F(X) has dimension 1. -/
theorem functor_zero_to_one (F : C ⥤ C) {X : C}
    (hX : HasDimension F X dimZero) :
    HasDimension F (F.obj X) (dimSucc dimZero) :=
  functor_increments_dimension (n := 0) F hX

/-- The n-th iterate of the initial object has dimension n,
    and applying F gives dimension n+1.
    This specializes `functor_increments_dimension` to the concrete iterates. -/
theorem iterate_functor_dimension (F : C ⥤ C) (n : ℕ) :
    HasDimension F (F.obj (iterateObj F n)) (chainDimension (n + 1)) :=
  functor_increments_dimension F (iterate_has_dimension F n)

/-- Applying F twice increments dimension by 2. -/
theorem functor_increments_twice (F : C ⥤ C) {X : C} {n : ℕ}
    (hX : HasDimension F X (chainDimension n)) :
    HasDimension F (F.obj (F.obj X)) (chainDimension (n + 2)) :=
  functor_increments_dimension F (functor_increments_dimension F hX)

end FixedPoint.Dimension
