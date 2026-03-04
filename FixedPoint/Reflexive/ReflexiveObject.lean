/-
  ReflexiveObject.lean

  Defines a `ReflexiveObject` structure that packages the fixed-point
  isomorphism `[A, L] ≅ L` (from `FixedPointSpec`) together with
  derived operations: self-application and reflexive currying.

  Given a fixed point L of the internal-hom endofunctor ihom(A),
  the Lambek isomorphism φ : [A, L] ≅ L says that L encodes its own
  function space. This gives rise to:

  - `selfApp : A ⊗ L ⟶ L` — decode an element of L as a function
    A → L via φ⁻¹, then evaluate.
  - `reflexiveCurry : (A ⊗ X ⟶ L) → (X ⟶ L)` — curry a morphism
    into the internal hom [A, L], then collapse via φ.

  STATUS: Tier 1 (no sorry).
-/
import FixedPoint.Specification.SubstrateIndependent

universe v u

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

namespace FixedPoint.Reflexive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### ReflexiveObject structure

A reflexive object packages a fixed-point specification (initial algebra
of ihom(A) with Lambek iso) together with the derived self-application
and currying operations. -/

/-- A reflexive object for a closed object A in a monoidal category C.
    This packages the fixed-point isomorphism `[A, L] ≅ L` together
    with derived operations.

    The carrier L satisfies the reflexive domain equation: it is
    isomorphic to its own internal function space `[A, L]`. -/
structure ReflexiveObject (A : C) [Closed A] where
  /-- The underlying fixed-point specification (initial algebra + Lambek iso). -/
  spec : FixedPointSpec A

variable {A : C} [Closed A]

/-- The carrier object L of a reflexive object. -/
def ReflexiveObject.carrier (r : ReflexiveObject A) : C :=
  r.spec.carrier

/-- The fixed-point (Lambek) isomorphism: `[A, L] ≅ L`. -/
noncomputable def ReflexiveObject.iso (r : ReflexiveObject A) :
    (ihom A).obj r.carrier ≅ r.carrier :=
  r.spec.fixedPointIso

/-- Self-application: `A ⊗ L ⟶ L`.

    Given the Lambek iso `φ : [A, L] ≅ L`, self-application is:
      `A ⊗ L --A◁φ⁻¹--> A ⊗ [A, L] --ev--> L`

    This decodes an element of L as a function `A → L` via φ⁻¹,
    then applies the evaluation morphism. -/
noncomputable def ReflexiveObject.selfApp (r : ReflexiveObject A) :
    A ⊗ r.carrier ⟶ r.carrier :=
  A ◁ r.iso.inv ≫ (ihom.ev A).app r.carrier

/-- Reflexive currying: given `f : A ⊗ X ⟶ L`, produce `X ⟶ L`.

    This composes standard currying `A ⊗ X ⟶ L ↦ X ⟶ [A, L]` with
    the Lambek iso `φ : [A, L] ⟶ L` to collapse the internal hom. -/
noncomputable def ReflexiveObject.reflexiveCurry (r : ReflexiveObject A)
    {X : C} (f : A ⊗ X ⟶ r.carrier) : X ⟶ r.carrier :=
  MonoidalClosed.curry f ≫ r.iso.hom

/-- Reflexive uncurrying: given `g : X ⟶ L`, produce `A ⊗ X ⟶ L`.

    This decomposes g through the Lambek iso inverse and uncurries:
    `X --g--> L --φ⁻¹--> [A, L]` then uncurry to get `A ⊗ X ⟶ L`. -/
noncomputable def ReflexiveObject.reflexiveUncurry (r : ReflexiveObject A)
    {X : C} (g : X ⟶ r.carrier) : A ⊗ X ⟶ r.carrier :=
  MonoidalClosed.uncurry (g ≫ r.iso.inv)

/-! ### Factorization theorem

Self-application factors through the evaluation morphism via the
Lambek iso inverse. This is essentially the definition, but stated
as an equational lemma for rewriting. -/

/-- Self-application factors as `A ◁ φ⁻¹ ≫ ev`. -/
theorem ReflexiveObject.selfApp_eq (r : ReflexiveObject A) :
    r.selfApp = A ◁ r.iso.inv ≫ (ihom.ev A).app r.carrier :=
  rfl

/-- Self-application is the uncurrying of the Lambek iso inverse. -/
theorem ReflexiveObject.selfApp_eq_uncurry (r : ReflexiveObject A) :
    r.selfApp = MonoidalClosed.uncurry r.iso.inv := by
  simp only [selfApp, MonoidalClosed.uncurry_eq]

/-- Reflexive curry and uncurry are inverse operations (curry direction). -/
theorem ReflexiveObject.reflexiveCurry_reflexiveUncurry (r : ReflexiveObject A)
    {X : C} (g : X ⟶ r.carrier) :
    r.reflexiveCurry (r.reflexiveUncurry g) = g := by
  simp only [reflexiveCurry, reflexiveUncurry, MonoidalClosed.curry_uncurry,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Reflexive curry and uncurry are inverse operations (uncurry direction). -/
theorem ReflexiveObject.reflexiveUncurry_reflexiveCurry (r : ReflexiveObject A)
    {X : C} (f : A ⊗ X ⟶ r.carrier) :
    r.reflexiveUncurry (r.reflexiveCurry f) = f := by
  simp only [reflexiveCurry, reflexiveUncurry, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, MonoidalClosed.uncurry_curry]

/-- Self-application composed with the Lambek iso recovers evaluation.
    That is: `(A ◁ φ) ≫ selfApp = ev`. -/
theorem ReflexiveObject.whiskerLeft_iso_hom_selfApp (r : ReflexiveObject A) :
    A ◁ r.iso.hom ≫ r.selfApp = (ihom.ev A).app r.carrier := by
  simp only [selfApp, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-! ### Construction from FixedPointSpec

Any `FixedPointSpec A` gives rise to a `ReflexiveObject A`. -/

/-- Construct a `ReflexiveObject` from a `FixedPointSpec`. -/
def ReflexiveObject.fromSpec (fp : FixedPointSpec A) : ReflexiveObject A :=
  ⟨fp⟩

/-- The carrier of a reflexive object constructed from a spec agrees
    with the spec's carrier. -/
theorem ReflexiveObject.fromSpec_carrier (fp : FixedPointSpec A) :
    (ReflexiveObject.fromSpec fp).carrier = fp.carrier :=
  rfl

/-- The iso of a reflexive object constructed from a spec agrees
    with the spec's fixedPointIso. -/
theorem ReflexiveObject.fromSpec_iso (fp : FixedPointSpec A) :
    (ReflexiveObject.fromSpec fp).iso = fp.fixedPointIso :=
  rfl

/-! ### The reflexive curry-uncurry equivalence -/

/-- The equivalence between morphisms `A ⊗ X ⟶ L` and `X ⟶ L`
    given by reflexive currying. This witnesses the fact that L is
    a retract of its own function space. -/
noncomputable def ReflexiveObject.curryEquiv (r : ReflexiveObject A) (X : C) :
    (A ⊗ X ⟶ r.carrier) ≃ (X ⟶ r.carrier) where
  toFun := r.reflexiveCurry
  invFun := r.reflexiveUncurry
  left_inv f := r.reflexiveUncurry_reflexiveCurry f
  right_inv g := r.reflexiveCurry_reflexiveUncurry g

end FixedPoint.Reflexive
