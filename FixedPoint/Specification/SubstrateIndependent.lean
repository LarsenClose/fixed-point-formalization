/-
  SubstrateIndependent.lean

  The substrate-independent fixed-point specification.

  Central claim: in any monoidal closed, locally finitely presentable category C
  where `tensorLeft A` preserves finite presentability, the internal-hom endofunctor
  ihom(A) : C ⥤ C has an initial algebra whose structure map is an isomorphism
  (Lambek's lemma), yielding the fixed-point equation ihom(A)(X) ≅ X.

  This file defines the specification against Mathlib typeclasses without
  committing to a particular algebraic-theory substrate (EAT, Lawvere, etc.).
  Instantiation happens in Theories/.

  STATUS: Tier 1 (no sorry).
  - SubstrateCategory: monoidal closed + locally finitely presentable (LFP).
  - TensorLeftFinitelyPresentable A: typeclass asserting A ⊗ - preserves finite
    presentability. Together with LFP, this gives ihom(A) finitely accessible
    (AR 2.23 at κ = aleph₀), which implies PreservesColimitsOfShape ℕ (ihom A).
  - fixedPoint_exists: no PreservesColimit hypothesis; derived from LFP + tensor
    assumption via the LFP route in RightAdjointAccessible.lean.
  - iterationFromInitial: similarly cleaned up.
  REVIEW APPROVED: User reviewed 2026-03-02. Approved for Uniqueness/ to build on.

  ## LFP ROUTE: Eliminating the PreservesColimit hypothesis

  The ω-Adamek initial algebra theorem requires that the endofunctor F preserves
  the colimit of the initial chain (an omega-indexed sequential colimit).

  For F = ihom(A), this functor is the RIGHT adjoint of tensorLeft A. Right
  adjoints preserve limits, NOT colimits in general.

  The LFP route (implemented here) closes this gap as follows:
  1. Assume C is locally FINITELY presentable (κ = aleph₀).
  2. Assume tensorLeft A sends finitely presentable objects to finitely presentable
     objects (TensorLeftFinitelyPresentable A).
  3. By AR 2.23 specialized to κ = κ' = aleph₀ (proved in RightAdjointAccessible.lean):
     ihom(A) is aleph₀-accessible = finitely accessible.
  4. An aleph₀-accessible functor preserves all filtered colimits.
  5. ℕ is filtered, so ihom(A) preserves colimits of shape ℕ.
  6. In particular, ihom(A) preserves the colimit of the initial chain.

  What IS available from SubstrateCategory:
    - `HasColimit (initialChain (ihom A))` — follows from cocompleteness
      (IsLocallyFinitelyPresentable extends HasColimitsOfSize.{0,0})
    - `HasInitial C` — same reasoning (colimit of the empty diagram)
-/
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import FixedPoint.Iteration.AdamekConnection
import FixedPoint.Accessibility.RightAdjointAccessible

universe v u

open CategoryTheory
open CategoryTheory.Endofunctor
open CategoryTheory.Limits
open FixedPoint.Iteration
open MonoidalCategory

namespace FixedPoint

/-- A category satisfying the substrate-independent conditions for the
    fixed-point construction: monoidal closed and locally **finitely**
    presentable (κ = aleph₀).

    Locally finitely presentable (LFP) is the standard condition for
    categories of algebraic structures (modules, presheaves, sets, etc.).
    It is strictly stronger than locally presentable but holds in all
    categories of interest for the series. -/
class SubstrateCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  [closed : MonoidalClosed C]
  [presentable : IsLocallyFinitelyPresentable.{0} C]

attribute [instance] SubstrateCategory.closed SubstrateCategory.presentable

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SubstrateCategory C]

/-! ### Cocompleteness derived from local finite presentability

`SubstrateCategory` wraps `IsLocallyFinitelyPresentable`, which asserts
`IsCardinalLocallyPresentable C aleph₀`. That class extends
`HasColimitsOfSize.{0, 0}`, giving colimits for omega-indexed diagrams. -/

/-- A substrate category has all small colimits (in universe 0), hence in particular
    initial objects and colimits of omega-chains. -/
noncomputable instance : HasColimitsOfSize.{0, 0} C := inferInstance

/-! ### The tensor preservation typeclass

For the LFP route to work, we need that for the specific closed object A,
the functor `tensorLeft A` (i.e., X ↦ A ⊗ X) sends finitely presentable objects
to finitely presentable objects. -/

/-- `TensorLeftFinitelyPresentable A` asserts that `tensorLeft A` preserves finite
    presentability: if X is finitely presentable (aleph₀-presentable), so is A ⊗ X.

    This holds, for example, when:
    - A is itself finitely presentable in a symmetric monoidal category where the
      tensor product preserves filtered colimits in each variable separately.
    - In the category of R-modules, A ⊗_R - preserves filtered colimits iff A is
      finitely presented (= aleph₀-presentable), which is exactly our hypothesis.

    This typeclass replaces the old `[PreservesColimit (initialChain (ihom A)) (ihom A)]`
    hypothesis. It is mathematically cleaner: it asserts finite presentability of
    A ⊗ X (a property of objects) rather than colimit preservation (a property of
    functors), and from it we derive the colimit preservation via AR 2.23. -/
class TensorLeftFinitelyPresentable (A : C) : Prop where
  /-- A ⊗ X is finitely presentable whenever X is. -/
  preserves : ∀ (X : C), IsFinitelyPresentable.{0} X → IsFinitelyPresentable.{0} (A ⊗ X)

/-- From `TensorLeftFinitelyPresentable A`, derive that `ihom A` preserves colimits
    of shape ℕ. This is the key derivation via the LFP route (AR 2.23 at aleph₀). -/
noncomputable instance ihom_preservesColimitsOfShape_nat_of_tensor
    (A : C) [Closed A] [h : TensorLeftFinitelyPresentable A] :
    PreservesColimitsOfShape ℕ (ihom A) :=
  FixedPoint.Accessibility.ihom_preservesColimitsOfShape_nat A
    (fun X hX => h.preserves X hX)

/-- From `TensorLeftFinitelyPresentable A`, derive that `ihom A` preserves the
    colimit of any specific ℕ-indexed diagram (including the initial chain). -/
noncomputable instance ihom_preservesColimit_of_tensor
    (A : C) [Closed A] [TensorLeftFinitelyPresentable A] (K : ℕ ⥤ C) :
    PreservesColimit K (ihom A) := inferInstance

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
    the ihom(A) endofunctor has an initial algebra.

    **No PreservesColimit hypothesis required.** The colimit preservation is
    derived from the LFP structure:
    - SubstrateCategory gives IsLocallyFinitelyPresentable C (LFP).
    - TensorLeftFinitelyPresentable A gives that A ⊗ - preserves finite presentability.
    - By AR 2.23 at κ = aleph₀, ihom(A) is aleph₀-accessible.
    - ℕ is filtered, so ihom(A) preserves ℕ-indexed colimits.
    - The ω-Adamek theorem then gives the initial algebra. -/
theorem fixedPoint_exists (A : C) [Closed A] [TensorLeftFinitelyPresentable A] :
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

    **No PreservesColimit hypothesis required** — it is derived from
    TensorLeftFinitelyPresentable via the LFP route. -/
noncomputable def iterationFromInitial [HasInitial C]
    [TensorLeftFinitelyPresentable (⊥_ C)] :
    FixedPointSpec (⊥_ C) :=
  { algebra := adamekFromInitial (ihom (⊥_ C))
    isInitial := adamekFromInitial_isInitial (ihom (⊥_ C)) }

end FixedPoint
