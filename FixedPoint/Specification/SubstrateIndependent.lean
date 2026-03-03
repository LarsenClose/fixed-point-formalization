/-
  SubstrateIndependent.lean

  The substrate-independent fixed-point specification.

  Central claim: in any monoidal closed, locally presentable category C,
  the internal-hom endofunctor ihom(A) : C ⥤ C has an initial algebra
  whose structure map is an isomorphism (Lambek's lemma), yielding the
  fixed-point equation ihom(A)(X) ≅ X.

  This file defines the specification against Mathlib typeclasses without
  committing to a particular algebraic-theory substrate (EAT, Lawvere, etc.).
  Instantiation happens in Theories/.

  STATUS: Tier 1 for iterationFromInitial and fixedPoint_exists (modulo
  an explicit colimit-preservation hypothesis — see MATHLIB GAP below).
  REVIEW APPROVED: User reviewed 2026-03-02. Approved for Uniqueness/ to build on.

  ## MATHLIB GAP: PreservesColimit for ihom

  The Adamek initial algebra theorem requires that the endofunctor F preserves
  the colimit of the initial chain (an omega-indexed sequential colimit).

  For F = ihom(A), this functor is the RIGHT adjoint of (- ⊗ A). Right
  adjoints preserve limits, NOT colimits in general. The mathematical
  justification is:

    In a locally presentable category, every right adjoint is accessible
    (Adamek-Rosicky, Theorem 2.23). An accessible functor preserves
    kappa-filtered colimits for some regular cardinal kappa. When kappa = aleph_0,
    this gives preservation of all filtered (= omega-filtered) colimits,
    which includes the initial chain.

  However, Mathlib (as of March 2026) does NOT have:
    (1) The theorem that right adjoints between locally presentable categories
        are accessible (Adamek-Rosicky 2.23).
    (2) Therefore, no way to derive `PreservesColimit (initialChain (ihom A)) (ihom A)`
        from `SubstrateCategory` alone.

  We add `PreservesColimit (initialChain (ihom A)) (ihom A)` as an explicit
  hypothesis. When Mathlib gains (1), this hypothesis can be removed and
  derived from `SubstrateCategory` automatically.

  What IS available from SubstrateCategory:
    - `HasColimit (initialChain (ihom A))` — follows from cocompleteness
      (IsLocallyPresentable => HasColimitsOfSize => HasColimitsOfShape Nat)
    - `HasInitial C` — same reasoning (colimit of the empty diagram)
-/
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import FixedPoint.Iteration.AdamekConnection

universe w v u

open CategoryTheory
open CategoryTheory.Endofunctor
open CategoryTheory.Limits
open FixedPoint.Iteration

namespace FixedPoint

/-- A category satisfying the substrate-independent conditions for the
    fixed-point construction: monoidal closed and locally presentable. -/
class SubstrateCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  [closed : MonoidalClosed C]
  [presentable : IsLocallyPresentable.{w} C]

attribute [instance] SubstrateCategory.closed SubstrateCategory.presentable

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SubstrateCategory.{w} C]

/-! ### Cocompleteness derived from local presentability

`SubstrateCategory` wraps `IsLocallyPresentable`, which asserts the existence of a
regular cardinal `kappa` witnessing `IsCardinalLocallyPresentable C kappa`. That class
extends `HasColimitsOfSize.{w, w}`, which we shrink to `HasColimitsOfSize.{0, 0}` to
obtain colimits for omega-indexed diagrams (the initial chain). -/

/-- A substrate category has all small colimits (in universe 0), hence in particular
    initial objects and colimits of omega-chains. -/
noncomputable instance : HasColimitsOfSize.{0, 0} C := by
  obtain ⟨_, _, hLP⟩ := IsLocallyPresentable.exists_cardinal C
  exact hasColimitsOfSizeShrink.{0, 0, w, w} C

/-- An algebra for the ihom(A) endofunctor: an object X with a morphism
    ihom(A)(X) ⟶ X. Mathlib's `ihom A` is already a functor `C ⥤ C`,
    so no wrapper is needed. -/
abbrev IHomAlgebra (A : C) [Closed A] := Algebra (ihom A)

/-- The fixed-point specification: there exists an initial algebra of ihom(A),
    and by Lambek's lemma its structure map is an isomorphism.

    This packages both existence (the initial algebra) and the fixed-point
    property (structure map is iso) into a single structure.

    The definition is parameterized over any closed object A. The series'
    specific construction specializes to A = ⊥_ C (the initial object);
    see `iterationFromInitial` below. -/
structure FixedPointSpec (A : C) [Closed A] where
  /-- The initial algebra of the ihom(A) endofunctor. -/
  algebra : IHomAlgebra A
  /-- Witness that the algebra is initial in the category of ihom(A)-algebras. -/
  isInitial : Limits.IsInitial algebra
  /-- The structure map is an isomorphism (Lambek's lemma, Tier 1 — fully
      verified from Mathlib's `Algebra.Initial.str_isIso`). -/
  strIso : IsIso algebra.str := Algebra.Initial.str_isIso isInitial

/-- The carrier of the fixed point: the object X such that ihom(A)(X) ≅ X. -/
def FixedPointSpec.carrier {A : C} [Closed A] (fp : FixedPointSpec A) : C :=
  fp.algebra.a

/-- The fixed-point isomorphism: ihom(A)(X) ≅ X, extracted from the
    initial algebra structure via Lambek's lemma. -/
noncomputable def FixedPointSpec.fixedPointIso {A : C} [Closed A]
    (fp : FixedPointSpec A) : (ihom A).obj fp.carrier ≅ fp.carrier :=
  haveI := fp.strIso
  asIso fp.algebra.str

/-- Main existence theorem: for any closed object A in a substrate category,
    the ihom(A) endofunctor has an initial algebra, provided ihom(A) preserves
    the colimit of the initial chain.

    The colimit existence follows from cocompleteness of locally presentable
    categories. The preservation hypothesis is the content of
    Adamek-Rosicky Theorem 2.23 (right adjoints between locally presentable
    categories are accessible), which Mathlib does not yet formalize.
    See the MATHLIB GAP note at the top of this file. -/
theorem fixedPoint_exists (A : C) [Closed A]
    [PreservesColimit (initialChain (ihom A)) (ihom A)] :
    ∃ _ : FixedPointSpec A, True :=
  ⟨{ algebra := adamekFromInitial (ihom A)
     isInitial := adamekFromInitial_isInitial (ihom A) }, trivial⟩

omit [SubstrateCategory C] in
/-- Uniqueness: any two fixed points (initial algebras of ihom(A)) are
    isomorphic, by initiality. Tier 1 — no sorry, follows from the
    universal property of initial objects. -/
noncomputable def fixedPoint_unique {A : C} [Closed A]
    (fp₁ fp₂ : FixedPointSpec A) :
    fp₁.algebra ≅ fp₂.algebra :=
  fp₁.isInitial.uniqueUpToIso fp₂.isInitial

/-! ## Initial-object specialization

The series' specific construction: iterate ihom from the initial object ⊥_ C.
G_Cat is the fixed point of ihom(⊥_ C), obtained as the colimit of the
Adamek chain ⊥ → ihom(⊥)(⊥) → ihom(⊥)²(⊥) → ⋯ -/

/-- The series' central construction: the fixed point of ihom applied from
    the initial object. This is the specific instance that yields G_Cat.

    The `HasInitial C` hypothesis is redundant (it follows from
    `SubstrateCategory`), but retained for clarity at use sites.
    The `PreservesColimit` hypothesis is the Mathlib gap documented above. -/
noncomputable def iterationFromInitial [HasInitial C]
    [PreservesColimit (initialChain (ihom (⊥_ C))) (ihom (⊥_ C))] :
    FixedPointSpec (⊥_ C) :=
  { algebra := adamekFromInitial (ihom (⊥_ C))
    isInitial := adamekFromInitial_isInitial (ihom (⊥_ C)) }

end FixedPoint
