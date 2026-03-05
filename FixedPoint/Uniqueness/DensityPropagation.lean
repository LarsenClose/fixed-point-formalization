/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Density Propagation.

Infrastructure lemma for the terminal characterization conjecture:
if two ω-cocontinuous endofunctors on a locally finitely presentable (LFP)
category agree (up to natural isomorphism) on all finitely presentable
objects, then they are naturally isomorphic as functors.

## Mathematical background

In an LFP category C, the finitely presentable objects form a dense
subcategory (Mathlib: `IsFinitelyAccessibleCategory.instIsDense`).
This means every object X is the colimit of the canonical diagram
  CostructuredArrow (isFinitelyPresentable C).ι X ⥤ C
over all finitely presentable objects mapping into X, and this colimit
is filtered.

If F, G : C ⥤ C both preserve filtered colimits, and there is a
natural family of isomorphisms F(P) ≅ G(P) for all finitely presentable P,
then for each X:
  F(X) ≅ F(colim P_i) ≅ colim F(P_i) ≅ colim G(P_i) ≅ G(colim P_i) ≅ G(X)

The naturality of this composite in X gives F ≅ G.

## What is proved here

The key Mathlib ingredient -- that the composite colimit manipulations above
yield a well-defined natural isomorphism -- would require assembling
`IsColimit.map`, `isColimitOfPreserves`, and naturality of the dense
colimit cocone. This assembly is nontrivial and not packaged in Mathlib.

We provide:
1. `PresentableAgreement F G`: structure packaging natural agreement on
   finitely presentable objects (the hypothesis).
2. `densityPropagation`: the main theorem, stated with the proof
   delegated through a clearly documented gap. If Mathlib adds a result
   like "agreement on dense generators + filtered colimit preservation
   implies NatIso," the sorry can be eliminated.
3. `densityPropagation_ihom`: specialization to the terminal conjecture.

STATUS: Tier 2 -- 1 sorry (the density propagation core).
The sorry is mathematically justified; it is a standard result in
accessible category theory (see Adamek-Rosicky, Theorem 1.46).
-/

import FixedPoint.Specification.SubstrateIndependent
import Mathlib.CategoryTheory.Presentable.Dense
import Mathlib.CategoryTheory.Presentable.Finite

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open MonoidalCategory

namespace FixedPoint.Uniqueness

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### PresentableAgreement: natural agreement on finitely presentable objects -/

/-- Two endofunctors `F` and `G` on `C` agree on all finitely presentable objects,
    naturally. That is, there is a family of isomorphisms `F(P) ≅ G(P)` for each
    finitely presentable `P`, and these are compatible with morphisms between
    finitely presentable objects. -/
structure PresentableAgreement (F G : C ⥤ C) where
  /-- For each finitely presentable object P, an isomorphism F(P) ≅ G(P). -/
  isoAt : ∀ (P : C), IsFinitelyPresentable P → (F.obj P ≅ G.obj P)
  /-- The isomorphisms are natural: for any morphism f : P → Q between finitely
      presentable objects, the square commutes. -/
  naturality : ∀ (P Q : C) (hP : IsFinitelyPresentable P) (hQ : IsFinitelyPresentable Q)
    (f : P ⟶ Q),
    F.map f ≫ (isoAt Q hQ).hom = (isoAt P hP).hom ≫ G.map f

/-! ### The density propagation theorem -/

section DensityPropagation

variable [MonoidalCategory C] [SubstrateCategory C]

/-- **Density propagation theorem.**

    If F and G are endofunctors on a locally finitely presentable category,
    both preserving filtered colimits, and they agree naturally on all finitely
    presentable objects, then F ≅ G as functors.

    **Proof sketch** (standard, see Adamek-Rosicky Theorem 1.46):
    Every object X is the filtered colimit of the canonical diagram of
    finitely presentable objects mapping into X (density). Since F and G
    preserve this colimit, F(X) and G(X) are both colimits of the same
    shape. The natural agreement on presentable objects induces a cocone
    morphism, yielding F(X) ≅ G(X). Naturality in X follows from
    universality of colimits.

    **Gap**: Assembling `IsColimit.map`, `isColimitOfPreserves`, and the
    naturality of the dense colimit cocone into a single NatIso requires
    infrastructure not currently packaged in Mathlib. The sorry here is
    mathematically justified and isolates the precise Mathlib gap. -/
noncomputable def densityPropagation
    (F G : C ⥤ C)
    [PreservesFilteredColimits F] [PreservesFilteredColimits G]
    (agree : PresentableAgreement F G) :
    F ≅ G := by
  -- The finitely presentable objects form a dense subcategory in any LFP category.
  -- Mathlib provides: (ObjectProperty.isFinitelyPresentable C).ι.IsDense
  -- Every X is a filtered colimit of presentable objects.
  -- F and G both preserve this colimit.
  -- The agreement on presentable objects induces an isomorphism on each colimit.
  -- This is Adamek-Rosicky Theorem 1.46; the formal assembly from Mathlib
  -- pieces requires IsColimit.map + isColimitOfPreserves + naturality bookkeeping.
  sorry

end DensityPropagation

/-! ### Specialization to the terminal conjecture -/

section TerminalConjecture

set_option linter.unusedSectionVars false

variable [MonoidalCategory C] [SubstrateCategory C] [HasInitial C]

/-- If F preserves filtered colimits and agrees with ihom(A) on all finitely
    presentable objects, then F ≅ ihom(A).

    This is the density propagation lemma specialized to the case G = ihom(A),
    which is the key infrastructure for the terminal characterization conjecture:
    once we show F and ihom(A) agree on generators, we get F ≅ ihom(A) globally. -/
noncomputable def densityPropagation_ihom
    (A : C) [Closed A]
    (F : C ⥤ C) [PreservesFilteredColimits F]
    [PreservesFilteredColimits (ihom A)]
    (agree : PresentableAgreement F (ihom A)) :
    F ≅ ihom A :=
  densityPropagation F (ihom A) agree

/-- **Connection to the self-indexed terminal conjecture.**

    The density propagation approach reduces the conjecture
      "F with self-indexed fixed point implies F ≅ ihom(A)"
    to two sub-goals:

    1. **Identify A**: Given a self-indexed fixed point D of F, take A := D.
       The self-indexing condition forces D ≅ [D, D], making ihom(D) the
       candidate.

    2. **Verify agreement on generators**: Show that F and ihom(D) agree
       on all finitely presentable objects. This is the remaining mathematical
       content: the self-indexing condition + Adamek chain structure must
       propagate agreement from the fixed point D to all presentable objects.

    Sub-goal 2 is where the mathematical difficulty concentrates. The chain
    objects F^n(⊥) are finitely presentable (being finite colimits of the
    initial object), and agreement on these propagates to the fixed point.
    But agreement at chain stages does not automatically extend to ALL
    finitely presentable objects -- only to those in the essential image of
    the chain functor. This is the "local-to-global gap" that density
    propagation is designed to bridge. -/
theorem density_approach_reduces_conjecture
    (A : C) [Closed A]
    (F : C ⥤ C) [PreservesFilteredColimits F]
    [PreservesFilteredColimits (ihom A)]
    (agree : PresentableAgreement F (ihom A)) :
    Nonempty (F ≅ ihom A) :=
  ⟨densityPropagation_ihom A F agree⟩

end TerminalConjecture

/-! ### Density of finitely presentable objects: Mathlib reference

For documentation: Mathlib provides the density instance we rely on.

In `Mathlib.CategoryTheory.Presentable.Dense`:
```
instance [IsFinitelyAccessibleCategory.{w} C] :
    (ObjectProperty.isFinitelyPresentable.{w} C).ι.IsDense
```

This means: in any finitely accessible category (hence in any LFP category),
the inclusion functor from the full subcategory of finitely presentable objects
is dense. Every object X is the colimit of the canonical filtered diagram of
finitely presentable objects over X.

`IsLocallyFinitelyPresentable C` extends `HasCardinalFilteredGenerators C aleph₀`
(making C finitely accessible) and `HasColimitsOfSize.{0,0}`.
-/

end FixedPoint.Uniqueness
