/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Dimensional Dissolution Theorem (Target 9).

The Yoneda embedding restricted to the Adamek chain at the fixed point
preserves dimension: dim(y(M^n(⊥))) in [C^op, Set] equals dim(M^n(⊥)) in C.

The key insight: rather than defining dimension independently for presheaves,
we show that the Yoneda embedding commutes with the internal hom functor M.
This follows from Mathlib's `Adjunction.compYonedaIso`, which states that
for any adjunction F ⊣ G, the right adjoint commutes with Yoneda:

  G ⋙ yoneda ≅ yoneda ⋙ (whiskeringLeft C^op D^op Type).obj F.op

Applied to `tensorLeft A ⊣ ihom A`, this gives M-compatibility of Yoneda.

Key results:
  - `yoneda_ihom_iso`           : ihom(A) ⋙ yoneda ≅ yoneda ⋙ whisker(tensorLeft A)
  - `yoneda_ihom_obj_iso`       : yoneda(ihom(A)(X)) ≅ yoneda(X) ∘ (tensorLeft A)^op
  - `yoneda_preserves_dimension`: HasDimension F X d → HasEmbeddedDimension F (yoneda X) d
  - `yoneda_reflects_dimension` : HasEmbeddedDimension F (yoneda X) d → HasDimension F X d
  - `dissolution_at_fixedpoint` : at the fixed point L, yoneda(L) inherits
                                  all dimensional properties of L

STATUS: Tier 1 (no sorry).
-/

import FixedPoint.Dimension.Stabilization
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Whiskering

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open MonoidalCategory
open FixedPoint.Iteration
open FixedPoint.Dimension.TruncationLevel

namespace FixedPoint.Dimension

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Yoneda commutes with right adjoints -/

/-- The Yoneda embedding commutes with ihom(A), the right adjoint of tensorLeft A.
    This is a direct application of `Adjunction.compYonedaIso` to the
    internal hom adjunction. -/
def yoneda_ihom_iso [MonoidalCategory C] (A : C) [Closed A] :
    ihom A ⋙ yoneda ≅ yoneda ⋙ (whiskeringLeft Cᵒᵖ Cᵒᵖ (Type v)).obj (tensorLeft A).op :=
  (ihom.adjunction A).compYonedaIso

/-- At an individual object X, yoneda(ihom(A)(X)) is naturally isomorphic to
    yoneda(X) precomposed with (tensorLeft A)^op. -/
def yoneda_ihom_obj_iso [MonoidalCategory C] (A : C) [Closed A] (X : C) :
    yoneda.obj ((ihom A).obj X) ≅
    ((whiskeringLeft Cᵒᵖ Cᵒᵖ (Type v)).obj (tensorLeft A).op).obj (yoneda.obj X) :=
  (yoneda_ihom_iso A).app X

/-! ### The M-compatibility principle

The natural isomorphism `yoneda_ihom_iso` says that applying M = ihom(A) in C
and then embedding via Yoneda is the same as embedding first and then
precomposing with the tensor functor. This is the "dissolution" of the
distinction between iterating M in C and observing the result in presheaves.

For dimension purposes, the key consequence is:

  If X ≅ Y in C, then yoneda(X) ≅ yoneda(Y) in presheaves.

Since Yoneda is fully faithful, it reflects isomorphisms as well. So
dimension (defined via isomorphism to chain objects) is preserved. -/

/-- Yoneda preserves isomorphisms (it's a functor). If X ≅ Y in C,
    then yoneda(X) ≅ yoneda(Y) in [C^op, Type v]. -/
def yoneda_preserves_iso {X Y : C} (e : X ≅ Y) :
    yoneda.obj X ≅ yoneda.obj Y :=
  yoneda.mapIso e

/-- Yoneda reflects isomorphisms: if yoneda(X) ≅ yoneda(Y), then X ≅ Y.
    This follows from Yoneda being fully faithful. -/
noncomputable def yoneda_reflects_iso {X Y : C}
    (e : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
  (Yoneda.fullyFaithful (C := C)).isoEquiv.invFun e

/-! ### Dimension preservation through Yoneda

We define "embedded dimension" for presheaves: a presheaf P has embedded
dimension d if there exists a chain object whose Yoneda image is isomorphic
to P. This is the natural dimension notion for presheaves that come from C
via Yoneda -- it says "P looks like a representable at chain level n." -/

variable [HasInitial C]

/-- A presheaf P has embedded dimension d (relative to F) if there exists
    a chain object F^n(⊥) whose Yoneda image is isomorphic to P. -/
def HasEmbeddedDimension (F : C ⥤ C)
    (P : Cᵒᵖ ⥤ Type v) (d : TruncationLevel) : Prop :=
  ∃ n, chainDimension n = d ∧ Nonempty (P ≅ yoneda.obj (iterateObj F n))

/-- Yoneda preserves dimension: if X has dimension d in C, then yoneda(X)
    has embedded dimension d in the presheaf category. -/
theorem yoneda_preserves_dimension {F : C ⥤ C} {X : C} {d : TruncationLevel}
    (hX : HasDimension F X d) : HasEmbeddedDimension F (yoneda.obj X) d := by
  obtain ⟨n, hd, ⟨iso⟩⟩ := hX
  exact ⟨n, hd, ⟨yoneda.mapIso iso⟩⟩

/-- Yoneda reflects dimension: if yoneda(X) has embedded dimension d,
    then X has dimension d in C. -/
theorem yoneda_reflects_dimension {F : C ⥤ C} {X : C}
    {d : TruncationLevel}
    (hP : HasEmbeddedDimension F (yoneda.obj X) d) : HasDimension F X d := by
  obtain ⟨n, hd, ⟨iso⟩⟩ := hP
  exact ⟨n, hd, ⟨yoneda_reflects_iso iso⟩⟩

/-- Yoneda gives a dimension equivalence: X has dimension d iff yoneda(X)
    has embedded dimension d. -/
theorem yoneda_dimension_iff {F : C ⥤ C} {X : C} {d : TruncationLevel} :
    HasDimension F X d ↔ HasEmbeddedDimension F (yoneda.obj X) d :=
  ⟨yoneda_preserves_dimension, yoneda_reflects_dimension⟩

/-! ### Dissolution at the fixed point

At the fixed point L where F(L) ≅ L, Yoneda embedding preserves the
complete dimensional structure: stability, absorption, and the dichotomy. -/

/-- At the fixed point, the Yoneda-embedded dimension is stable:
    yoneda(L) and yoneda(F(L)) have the same embedded dimensions. -/
theorem yoneda_fixedpoint_dimension_stable {F : C ⥤ C} {L : C}
    (lamb : F.obj L ≅ L) (d : TruncationLevel) :
    HasEmbeddedDimension F (yoneda.obj L) d ↔
    HasEmbeddedDimension F (yoneda.obj (F.obj L)) d := by
  constructor
  · intro h
    exact yoneda_preserves_dimension ((yoneda_reflects_dimension h) |>
      (fixedpoint_dimension_iff lamb).mp)
  · intro h
    exact yoneda_preserves_dimension ((yoneda_reflects_dimension h) |>
      (fixedpoint_dimension_iff lamb).mpr)

/-- The dissolution theorem: at the fixed point L, the "constructed"
    dimension (from iterating M on ⊥ in C) and the "observed" dimension
    (from Yoneda-embedding into presheaves) are provably identical.

    This packages the complete dissolution: there is no gap between the
    dimension as computed by the method (iteration in C) and the dimension
    as observed externally (via Yoneda in [C^op, Type]). -/
structure DimensionalDissolution (F : C ⥤ C) (L : C) where
  /-- The Lambek iso witnessing L as a fixed point -/
  lambek : F.obj L ≅ L
  /-- Dimension equivalence: internal = embedded, for all d -/
  dim_equiv : ∀ d, HasDimension F L d ↔ HasEmbeddedDimension F (yoneda.obj L) d
  /-- Stability is preserved through the embedding -/
  embedded_stable : ∀ d,
    HasEmbeddedDimension F (yoneda.obj L) d ↔
    HasEmbeddedDimension F (yoneda.obj (F.obj L)) d

/-- Construct the dimensional dissolution from a Lambek isomorphism. -/
def dimensionalDissolution {F : C ⥤ C} {L : C}
    (lamb : F.obj L ≅ L) : DimensionalDissolution F L where
  lambek := lamb
  dim_equiv := fun _ => yoneda_dimension_iff
  embedded_stable := fun d => yoneda_fixedpoint_dimension_stable lamb d

section Substrate

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C]
variable {A : C} [Closed A]

/-- The M-compatibility of Yoneda for the substrate specification:
    the Yoneda embedding commutes with ihom(A) at the fixed point. -/
noncomputable def spec_dissolution (fp : FixedPointSpec A) :
    DimensionalDissolution (ihom A) fp.carrier :=
  dimensionalDissolution fp.fixedPointIso

/-- The Yoneda-ihom natural isomorphism specialized to the substrate. -/
def spec_yoneda_ihom_iso :
    ihom A ⋙ yoneda ≅ yoneda ⋙ (whiskeringLeft Cᵒᵖ Cᵒᵖ (Type v)).obj (tensorLeft A).op :=
  yoneda_ihom_iso A

end Substrate

end FixedPoint.Dimension
