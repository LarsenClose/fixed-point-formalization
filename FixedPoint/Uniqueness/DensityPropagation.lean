/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Density Propagation (Adamek-Rosicky Theorem 1.46).

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

We provide a full proof of Adamek-Rosicky Theorem 1.46 by assembling
Mathlib's density infrastructure (`IsDense`, `isColimitOfPreserves`,
`IsColimit.coconePointsIsoOfNatIso`) with a manual naturality argument.

1. `PresentableAgreement F G`: structure packaging natural agreement on
   finitely presentable objects (the hypothesis).
2. `densityPropagation`: the main theorem (0 sorry).
3. `densityPropagation_ihom`: specialization to the terminal conjecture.

STATUS: Tier 1 -- fully proved, 0 sorry.
-/

import FixedPoint.Specification.SubstrateIndependent
import Mathlib.CategoryTheory.Presentable.Dense
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Filtered

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

/-- Abbreviation for the inclusion of the finitely presentable full subcategory. -/
private abbrev ιFP := (ObjectProperty.isFinitelyPresentable.{0} C).ι

/-- Given agreement on presentable objects, build a natural isomorphism between the
    density diagrams composed with F and G. For each `j : CostructuredArrow ι X`,
    `j.left` is a finitely presentable object, and we use the agreement at that object. -/
private noncomputable def densityDiagramIso
    {F G : C ⥤ C} (agree : PresentableAgreement F G) (X : C) :
    (CostructuredArrow.proj ιFP X ⋙ ιFP) ⋙ F ≅
    (CostructuredArrow.proj ιFP X ⋙ ιFP) ⋙ G :=
  NatIso.ofComponents
    (fun j => by
      have : ObjectProperty.isFinitelyPresentable.{0} C (ιFP.obj j.left) :=
        j.left.property
      unfold ObjectProperty.isFinitelyPresentable at this
      exact agree.isoAt (ιFP.obj j.left) this)
    (fun {j₁ j₂} f => by
      dsimp
      have h1 : ObjectProperty.isFinitelyPresentable.{0} C (ιFP.obj j₁.left) :=
        j₁.left.property
      have h2 : ObjectProperty.isFinitelyPresentable.{0} C (ιFP.obj j₂.left) :=
        j₂.left.property
      unfold ObjectProperty.isFinitelyPresentable at h1 h2
      exact agree.naturality _ _ h1 h2 _)

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1600000 in
/-- **Density propagation theorem** (Adamek-Rosicky Theorem 1.46).

    If F and G are endofunctors on a locally finitely presentable category,
    both preserving filtered colimits (of shape up to `Type (max u v)`),
    and they agree naturally on all finitely presentable objects, then F ≅ G
    as functors.

    The proof uses three Mathlib ingredients:
    1. **Density**: Every object X is a filtered colimit of finitely presentable
       objects via `IsDense` (Mathlib.CategoryTheory.Presentable.Dense).
    2. **Preservation**: `isColimitOfPreserves` transports the colimit through F, G.
    3. **Comparison**: `IsColimit.coconePointsIsoOfNatIso` builds the component iso.
    Naturality in X follows by checking on coprojections of the density colimit.

    **Universe note**: The hypothesis `PreservesFilteredColimitsOfSize.{v, max u v}`
    is needed because the index category `CostructuredArrow ι X` lives in
    `Type (max u v)`. For categories where `u ≤ v`, the standard
    `PreservesFilteredColimits` suffices. -/
noncomputable def densityPropagation
    (F G : C ⥤ C)
    [PreservesFilteredColimitsOfSize.{v, max u v} F]
    [PreservesFilteredColimitsOfSize.{v, max u v} G]
    (agree : PresentableAgreement F G) :
    F ≅ G := by
  -- Build the NatIso from component isomorphisms + naturality.
  -- Component iso at X: use density colimit + preservation + comparison.
  refine NatIso.ofComponents
    (fun X =>
      IsColimit.coconePointsIsoOfNatIso
        (isColimitOfPreserves F (ιFP.denseAt X))
        (isColimitOfPreserves G (ιFP.denseAt X))
        (densityDiagramIso agree X))
    (fun {X Y} f => ?_)
  -- Naturality: F.map f ≫ iso_Y.hom = iso_X.hom ≫ G.map f.
  -- Strategy: check equality on coprojections of the F-colimit at X,
  -- then reduce both sides to agree.isoAt ≫ G.map (j.hom ≫ f).
  apply (isColimitOfPreserves F (ιFP.denseAt X)).hom_ext; intro j
  simp only [← Category.assoc]
  rw [IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ j]
  -- RHS: ((densityDiagramIso agree X).hom.app j ≫ (G.mapCocone _).ι.app j) ≫ G.map f
  -- Simplify the density cocone coprojections.
  have eqF : (F.mapCocone ((LeftExtension.mk (𝟭 C) ιFP.rightUnitor.inv).coconeAt X)).ι.app j =
    F.map j.hom := by simp [Functor.mapCocone_ι_app, LeftExtension.coconeAt]
  have eqG : (G.mapCocone ((LeftExtension.mk (𝟭 C) ιFP.rightUnitor.inv).coconeAt X)).ι.app j =
    G.map j.hom := by simp [Functor.mapCocone_ι_app, LeftExtension.coconeAt]
  rw [eqF, eqG, Category.assoc ((densityDiagramIso agree X).hom.app j), ← G.map_comp]
  -- RHS: (densityDiagramIso agree X).hom.app j ≫ G.map (j.hom ≫ f)
  -- LHS: (F.map j.hom ≫ F.map f) ≫ iso_Y.hom
  conv_lhs => rw [← F.map_comp]
  -- LHS: F.map (j.hom ≫ f) ≫ iso_Y.hom
  -- Rewrite as coprojection at Y for k = CostructuredArrow.mk (j.hom ≫ f).
  let k : CostructuredArrow ιFP Y := CostructuredArrow.mk (j.hom ≫ f)
  have eqFK : F.map (j.hom ≫ f) =
    (F.mapCocone ((LeftExtension.mk (𝟭 C) ιFP.rightUnitor.inv).coconeAt Y)).ι.app k := by
    symm; simp [Functor.mapCocone_ι_app, LeftExtension.coconeAt, k]
  rw [eqFK, IsColimit.comp_coconePointsIsoOfNatIso_hom]
  -- LHS: (densityDiagramIso agree Y).hom.app k ≫ (G.mapCocone _).ι.app k
  have eqGK : (G.mapCocone ((LeftExtension.mk (𝟭 C) ιFP.rightUnitor.inv).coconeAt Y)).ι.app k =
    G.map (j.hom ≫ f) := by simp [Functor.mapCocone_ι_app, LeftExtension.coconeAt, k]
  rw [eqGK]
  -- Both sides: agree.isoAt (ιFP.obj j.left) _ ≫ G.map (j.hom ≫ f)
  -- Equal because k.left = j.left (definitionally).
  dsimp [densityDiagramIso, k]

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
    (F : C ⥤ C)
    [PreservesFilteredColimitsOfSize.{v, max u v} F]
    [PreservesFilteredColimitsOfSize.{v, max u v} (ihom A)]
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
    (F : C ⥤ C)
    [PreservesFilteredColimitsOfSize.{v, max u v} F]
    [PreservesFilteredColimitsOfSize.{v, max u v} (ihom A)]
    (agree : PresentableAgreement.{v, u, 0} F (ihom A)) :
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
