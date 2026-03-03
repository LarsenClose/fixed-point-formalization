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

  STATUS: Tier 2 — definition compiles, key theorems stated with sorry.
  REVIEW APPROVED: User reviewed 2026-03-02. Approved for Uniqueness/ to build on.
-/
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

universe w v u

open CategoryTheory
open CategoryTheory.Endofunctor
open CategoryTheory.Limits

namespace FixedPoint

/-- A category satisfying the substrate-independent conditions for the
    fixed-point construction: monoidal closed and locally presentable. -/
class SubstrateCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  [closed : MonoidalClosed C]
  [presentable : IsLocallyPresentable.{w} C]

attribute [instance] SubstrateCategory.closed SubstrateCategory.presentable

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SubstrateCategory.{w} C]

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

/-- Main existence conjecture: for any closed object A in a substrate category,
    the ihom(A) endofunctor has an initial algebra.

    In the paper series, this is established via the Adamek construction
    (iteration from the initial object), which requires the colimit-preservation
    properties guaranteed by local presentability. -/
theorem fixedPoint_exists (A : C) [Closed A] :
    ∃ fp : FixedPointSpec A, True := by
  sorry

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
    the initial object. This is the specific instance that yields G_Cat. -/
noncomputable def iterationFromInitial [HasInitial C] :
    FixedPointSpec (⊥_ C) := by
  sorry

end FixedPoint
