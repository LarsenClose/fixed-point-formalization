/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Terminal Characterization.

The internal hom is the unique endofunctor arising from the tensor-hom
adjunction: if `tensorLeft A ⊣ F`, then `F ≅ ihom A`. This is the
uniqueness of right adjoints applied to the monoidal closed structure.

Key definitions:
  - `HasAdamekFixedPoint F` : packages F having an initial algebra with Lambek iso
  - `right_adjoint_of_tensor_is_ihom` : re-export of rightAdjointForcedToIHom

Key results:
  - `terminal_characterization_from_adjunction` : tensorLeft A ⊣ F → F ≅ ihom A
  - `ihom_hasAdamekFixedPoint` : ihom A has an Adamek fixed point

## Negative findings (2026-03-04)

The original conjecture — that `HasAdamekFixedPoint F` alone forces
`F ≅ ihom A` — was investigated and found to be false:

  Step 1 (FALSE): HasAdamekFixedPoint F does NOT imply F is a right adjoint.
    Counterexample: the covariant powerset functor P : Set → Set has an
    Adamek fixed point (hereditarily finite sets) but does not preserve
    products, hence is not a right adjoint.

  Step 4 (FALSE): Even if F is a right adjoint of some L, L need not be
    tensorLeft A. Counterexamples: id ⊣ id, const ⊣ lim.

The precise additional structure needed is the tensor-hom adjunction itself.
`terminal_characterization_from_adjunction` captures exactly this: the
uniqueness of right adjoints, applied to `tensorLeft A ⊣ F`.

STATUS: Tier 1 — 0 sorry. The false conjecture has been removed; the proved
result and negative findings are documented.
-/

import FixedPoint.Dimension.DimensionIncrement
import FixedPoint.Uniqueness.RightAdjointUnique
import FixedPoint.Specification.SubstrateIndependent

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open FixedPoint.Dimension.TruncationLevel
open MonoidalCategory

namespace FixedPoint.Uniqueness

universe v u

/-! ### HasAdamekFixedPoint: packaging the initial algebra -/

/-- An endofunctor `F` has an Adamek fixed point if it possesses an initial
    F-algebra (obtained via the Adamek construction). The structure packages:
    - a carrier object
    - a Lambek isomorphism F(carrier) ≅ carrier
    - initiality of the algebra in the category of F-algebras -/
structure HasAdamekFixedPoint {C : Type u} [Category.{v} C]
    (F : C ⥤ C) where
  /-- The carrier object (the fixed point). -/
  carrier : C
  /-- The algebra structure: a morphism F(carrier) → carrier. -/
  algebraStr : F.obj carrier ⟶ carrier
  /-- The algebra structure is an isomorphism (Lambek's lemma). -/
  [strIsIso : IsIso algebraStr]
  /-- The algebra is initial in the category of F-algebras. -/
  isInitial : IsInitial (Endofunctor.Algebra.mk carrier algebraStr)

attribute [instance] HasAdamekFixedPoint.strIsIso

/-- The Lambek isomorphism F(carrier) ≅ carrier, extracted from the
    HasAdamekFixedPoint structure. -/
noncomputable def HasAdamekFixedPoint.lambekIso {C : Type u} [Category.{v} C]
    {F : C ⥤ C} (hfp : HasAdamekFixedPoint F) :
    F.obj hfp.carrier ≅ hfp.carrier :=
  asIso hfp.algebraStr

/-! ### Constructing HasAdamekFixedPoint from the standard Adamek setup -/

/-- When the Adamek construction applies (initial object, colimit, preservation),
    the endofunctor has an Adamek fixed point. -/
noncomputable def hasAdamekFixedPoint_of_standard {C : Type u} [Category.{v} C]
    (F : C ⥤ C) [HasInitial C] [HasColimit (initialChain F)]
    [PreservesColimit (initialChain F) F] :
    HasAdamekFixedPoint F where
  carrier := (adamekFromInitial F).a
  algebraStr := (adamekFromInitial F).str
  strIsIso := Endofunctor.Algebra.Initial.str_isIso (adamekFromInitial_isInitial F)
  isInitial := adamekFromInitial_isInitial F

/-! ### Re-export: right adjoint of tensorLeft is ihom -/

section Proved

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- If F is a right adjoint of `tensorLeft A`, then F ≅ ihom A.
    This is a re-export of `rightAdjointForcedToIHom` for the
    terminal characterization pipeline. -/
noncomputable def right_adjoint_of_tensor_is_ihom (A : C) [Closed A]
    {F : C ⥤ C} (adj : tensorLeft A ⊣ F) :
    F ≅ ihom A :=
  rightAdjointForcedToIHom A adj

end Proved

/-! ### The terminal characterization conjecture -/

section Conjecture

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C]
variable [HasInitial C]

/-- **Terminal characterization (proved form).**

    In a monoidal closed category, if `tensorLeft A ⊣ F`, then `F ≅ ihom A`.
    This is the uniqueness of right adjoints applied to the tensor-hom
    adjunction.

    The original conjecture — that `HasAdamekFixedPoint F` alone forces
    `F ≅ ihom A` — is false. Counterexamples:
    - Step 1: The covariant powerset functor on Set has an Adamek fixed point
      (hereditarily finite sets) but is not a right adjoint.
    - Step 4: Even for right adjoints, the left adjoint need not be a tensor
      functor (e.g. id ⊣ id, const ⊣ lim).

    The precise additional structure needed is the tensor-hom adjunction itself.
    This is the strongest unconditional result: no sorry, no additional axioms. -/
noncomputable def terminal_characterization_from_adjunction
    (A : C) [Closed A]
    (F : C ⥤ C) (adj : tensorLeft A ⊣ F) :
    F ≅ ihom A :=
  rightAdjointForcedToIHom A adj

end Conjecture

/-! ### ihom(A) has an Adamek fixed point -/

section IHomFixedPoint

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C]
variable [HasInitial C]

/-- The internal hom `ihom A` has an Adamek fixed point, constructed via the
    standard Adamek initial algebra theorem applied through the LFP route. -/
noncomputable def ihom_hasAdamekFixedPoint
    (A : C) [Closed A] [TensorLeftFinitelyPresentable A] :
    HasAdamekFixedPoint (ihom A) :=
  hasAdamekFixedPoint_of_standard (ihom A)

end IHomFixedPoint

end FixedPoint.Uniqueness
