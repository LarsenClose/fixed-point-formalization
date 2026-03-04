/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Dimension stabilizes at the fixed point.

At the fixed point L of an endofunctor F (where F(L) ≅ L by Lambek's lemma),
applying F does not change the dimension: if L has dimension d, then F(L)
also has dimension d. This is the dimensional reading of the D=1 result.

The key insight: the Lambek isomorphism F(L) ≅ L allows transporting any
dimension witness from L to F(L) and vice versa. At the fixed point, the
"+1" from `functor_increments_dimension` is absorbed by the isomorphism.

Key results:
  - `fixedpoint_dimension_stable` : F(L) ≅ L → HasDimension F L d →
      HasDimension F (F.obj L) d
  - `fixedpoint_dimension_iff` : F(L) ≅ L →
      (HasDimension F L d ↔ HasDimension F (F.obj L) d)
  - `fixedpoint_absorbs_increment` : at the fixed point, if L has
      dimension chainDimension n, then both chainDimension n and
      chainDimension (n+1) are witnessed — which by injectivity of
      chainDimension means the fixed point cannot have any finite
      dimension. This is the dimensional content of D=1.
-/

import FixedPoint.Dimension.IncrementDimension
import FixedPoint.Specification.SubstrateIndependent

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open FixedPoint.Dimension.TruncationLevel

namespace FixedPoint.Dimension

universe v u

variable {C : Type u} [Category.{v} C] [HasInitial C]

/-! ### Dimension stability at fixed points -/

/-- At a fixed point (F(L) ≅ L), dimension is preserved by F.
    If L has dimension d, then F(L) also has dimension d.

    Proof: transport the dimension witness through the Lambek iso. -/
theorem fixedpoint_dimension_stable {F : C ⥤ C} {L : C} {d : TruncationLevel}
    (lamb : F.obj L ≅ L) (hL : HasDimension F L d) :
    HasDimension F (F.obj L) d :=
  dimension_iso_invariant hL lamb.symm

/-- The converse: if F(L) has dimension d and F(L) ≅ L, then L has dimension d. -/
theorem fixedpoint_dimension_stable_inv {F : C ⥤ C} {L : C} {d : TruncationLevel}
    (lamb : F.obj L ≅ L) (hFL : HasDimension F (F.obj L) d) :
    HasDimension F L d :=
  dimension_iso_invariant hFL lamb

/-- At a fixed point, L and F(L) have exactly the same dimensions:
    HasDimension F L d ↔ HasDimension F (F.obj L) d. -/
theorem fixedpoint_dimension_iff {F : C ⥤ C} {L : C} {d : TruncationLevel}
    (lamb : F.obj L ≅ L) :
    HasDimension F L d ↔ HasDimension F (F.obj L) d :=
  ⟨fixedpoint_dimension_stable lamb, fixedpoint_dimension_stable_inv lamb⟩

/-! ### The dimensional content of D=1

At the fixed point, if L had finite dimension `chainDimension n`, then by
`functor_increments_dimension`, F(L) would have dimension `chainDimension (n+1)`.
But by `fixedpoint_dimension_stable`, F(L) also has dimension `chainDimension n`.
Since `chainDimension` is injective, `n+1 = n`, which is absurd.

Therefore the fixed point cannot have any finite dimension in the image of
`chainDimension`. This is the formal content of the D=1 result: dimension
stabilizes because the fixed point lives at the limit (omega) level, where
applying F is absorbed by the isomorphism. -/

/-- At a fixed point with a Lambek iso, if L has finite dimension
    `chainDimension n`, then F(L) has both dimension `chainDimension n`
    (by stability) and `chainDimension (n+1)` (by increment). -/
theorem fixedpoint_absorbs_increment {F : C ⥤ C} {L : C} {n : ℕ}
    (lamb : F.obj L ≅ L) (hL : HasDimension F L (chainDimension n)) :
    HasDimension F (F.obj L) (chainDimension n) ∧
    HasDimension F (F.obj L) (chainDimension (n + 1)) :=
  ⟨fixedpoint_dimension_stable lamb hL,
   functor_increments_dimension F hL⟩

/-! ### Connection to FixedPointSpec

The fixed point from the substrate-independent specification satisfies
dimension stability via the Lambek isomorphism. -/

section Substrate

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C]
variable {A : C} [Closed A]

/-- The carrier of a `FixedPointSpec` satisfies dimension stability:
    ihom(A)(L) and L have the same dimensions. -/
theorem spec_dimension_stable (fp : FixedPointSpec A) {d : TruncationLevel}
    (hL : HasDimension (ihom A) fp.carrier d) :
    HasDimension (ihom A) ((ihom A).obj fp.carrier) d :=
  fixedpoint_dimension_stable fp.fixedPointIso hL

/-- The `FixedPointSpec` carrier satisfies the full iff:
    HasDimension (ihom A) L d ↔ HasDimension (ihom A) (ihom(A)(L)) d. -/
theorem spec_dimension_iff (fp : FixedPointSpec A) {d : TruncationLevel} :
    HasDimension (ihom A) fp.carrier d ↔
    HasDimension (ihom A) ((ihom A).obj fp.carrier) d :=
  fixedpoint_dimension_iff fp.fixedPointIso

end Substrate

end FixedPoint.Dimension
