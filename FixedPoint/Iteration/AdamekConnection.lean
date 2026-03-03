/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Connection of the Adamek theorem to the fixed-point specification.

This file provides the interface between the Adamek initial algebra theorem
and the downstream fixed-point constructions needed by the series' claims.

Key results:
  - `adamekFixedPoint`     : the carrier of the initial algebra as a fixed point
  - `adamekStructureIso`   : F(L) ≅ L (Lambek's lemma applied to the initial algebra)
  - `adamekFromInitial`    : the full construction from HasInitial + HasColimit + PreservesColimit
-/

import FixedPoint.Iteration.AdamekTheorem

open CategoryTheory CategoryTheory.Limits

namespace FixedPoint.Iteration

universe v u

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ C) [HasInitial C]

section Connection

variable [HasColimit (initialChain F)]
variable [PreservesColimit (initialChain F) F]

/-- The standard colimit cocone for the initial chain. -/
noncomputable def standardCocone : Cocone (initialChain F) :=
  colimit.cocone (initialChain F)

/-- The standard colimit is indeed a colimit. -/
noncomputable def standardIsColimit : IsColimit (standardCocone F) :=
  colimit.isColimit (initialChain F)

-- ✓ TIER 1
/-- The Adamek initial algebra constructed from the standard colimit. -/
noncomputable def adamekFromInitial : Endofunctor.Algebra F :=
  adamekAlgebra F (standardCocone F) (standardIsColimit F)

-- ✓ TIER 1
/-- The Adamek algebra is initial. -/
noncomputable def adamekFromInitial_isInitial :
    IsInitial (adamekFromInitial F) :=
  adamekIsInitial F (standardIsColimit F)

-- ✓ TIER 1 (follows from Lambek's lemma in Mathlib)
/-- The structure map of the initial algebra is an isomorphism: F(L) ≅ L.
    This is Lambek's lemma applied to the Adamek initial algebra. -/
noncomputable def adamekStructureIso :
    F.obj (adamekFromInitial F).a ≅ (adamekFromInitial F).a := by
  haveI : IsIso (adamekFromInitial F).str :=
    Endofunctor.Algebra.Initial.str_isIso (adamekFromInitial_isInitial F)
  exact asIso (adamekFromInitial F).str

/-- The colimit of the initial chain is a fixed point of F: F(L) ≅ L. -/
noncomputable def adamekFixedPoint :
    F.obj (colimit (initialChain F)) ≅ colimit (initialChain F) :=
  adamekStructureIso F

end Connection

end FixedPoint.Iteration
