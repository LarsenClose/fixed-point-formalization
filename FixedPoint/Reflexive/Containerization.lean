/-
  Containerization.lean

  Makes explicit that the reflexive fixed point L ≅ [A, L] IS a container:
  L is closed under its generating operation. The Lambek isomorphism is the
  container boundary — it witnesses that one more application of the generator
  doesn't leave L.

  This connects the abstract categorical structure to the concept of
  containerization: the simplest organizational principle that enables
  computation.

  STATUS: Tier 1 (no sorry).
-/
import FixedPoint.Reflexive.FixedPointCombinator

universe v u

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

namespace FixedPoint.Reflexive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### ClosedContainer structure

A closed container is an object that contains its own transformation space
and is closed under application. The Lambek isomorphism serves as the
container boundary: it witnesses that applying the generating operation
does not escape the container. -/

/-- A closed container: an object L that contains its own transformation space
    [A, L] and is closed under the generating operation (applying the endofunctor
    doesn't escape L). The Lambek isomorphism is the container boundary —
    it witnesses that one more application of the generator doesn't leave L.

    A closed container is the categorical formalization of containerization:
    the act of creating a boundary (inside/outside) that persists under the
    generating operation. This is the minimal organizational structure that
    enables self-reference and computation. -/
structure ClosedContainer (A : C) [Closed A] where
  /-- The carrier object: what's inside the container. -/
  carrier : C
  /-- The container boundary: [A, L] ≅ L witnesses closure. -/
  boundary : (ihom A).obj carrier ≅ carrier
  /-- Evaluation: open the container (decode an element as a function, apply). -/
  eval : A ⊗ carrier ⟶ carrier
  /-- Naming: close the container (reify a morphism as an element). -/
  name : ∀ {X : C}, (A ⊗ X ⟶ carrier) → (X ⟶ carrier)
  /-- Opening after closing recovers the content (beta). -/
  eval_name : ∀ {X : C} (f : A ⊗ X ⟶ carrier),
    (A ◁ name f) ≫ eval = f
  /-- Closing after opening recovers the name (eta). -/
  name_eval : ∀ {X : C} (g : X ⟶ carrier),
    name ((A ◁ g) ≫ eval) = g

variable {A : C} [Closed A]

/-! ### Every reflexive object is a closed container -/

/-- Every reflexive object IS a closed container. The Lambek isomorphism
    provides the boundary, selfApp provides evaluation, and reflexiveCurry
    provides naming. The beta/eta laws follow from the curry-uncurry
    equivalence of the reflexive object. -/
noncomputable def ReflexiveObject.toClosedContainer (r : ReflexiveObject A) :
    ClosedContainer A where
  carrier := r.carrier
  boundary := r.iso
  eval := r.selfApp
  name := r.reflexiveCurry
  eval_name := fun f => by
    show A ◁ r.reflexiveCurry f ≫ r.selfApp = f
    have : A ◁ r.reflexiveCurry f ≫ r.selfApp = r.reflexiveUncurry (r.reflexiveCurry f) := by
      simp only [ReflexiveObject.reflexiveCurry, ReflexiveObject.selfApp,
        ReflexiveObject.reflexiveUncurry, MonoidalClosed.uncurry_eq,
        ← Category.assoc, ← whiskerLeft_comp]
    rw [this, r.reflexiveUncurry_reflexiveCurry]
  name_eval := fun g => by
    show r.reflexiveCurry (A ◁ g ≫ r.selfApp) = g
    have : A ◁ g ≫ r.selfApp = r.reflexiveUncurry g := by
      simp only [ReflexiveObject.selfApp, ReflexiveObject.reflexiveUncurry,
        MonoidalClosed.uncurry_eq, ← Category.assoc, ← whiskerLeft_comp]
    rw [this, r.reflexiveCurry_reflexiveUncurry]

/-! ## Containerization IS computation

A closed container provides:
- **Self-reference**: `selfReference = name(eval)` — the container can name
  its own evaluation
- **Fixed points**: `omega f = name(eval ≫ f)` — every transformation has
  a fixed point
- **Beta-reduction**: opening a closed thing recovers the content
- **Eta-expansion**: closing an opened thing recovers the name

These four properties are exactly what the untyped lambda calculus provides.
Containerization (creating a persistent boundary with eval/name operations)
is not a step toward computation — it IS computation. The simplest
organizational structure that maintains a boundary is already computationally
universal.

The reflexive fixed point L ≅ [A, L] is the minimal closed container for the
endofunctor ihom(A). The Adamek chain builds it from nothing (the initial
object), making containerization the first non-trivial structure that forced
development produces. -/

/-- A closed container can refer to itself: naming the evaluation morphism
    gives the self-reference element (the quine). -/
noncomputable def ClosedContainer.selfReference (c : ClosedContainer A) :
    c.carrier ⟶ c.carrier :=
  c.name c.eval

/-- In a closed container, every endomorphism has a fixed point witness:
    `name(eval ≫ f)` is a morphism whose evaluation composes to `eval ≫ f`. -/
noncomputable def ClosedContainer.omega (c : ClosedContainer A)
    (f : c.carrier ⟶ c.carrier) : c.carrier ⟶ c.carrier :=
  c.name (c.eval ≫ f)

/-- The fixed-point equation for closed containers:
    evaluating `omega f` equals evaluating then applying f.

    This is the categorical Y combinator equation expressed purely in terms
    of the container's eval/name interface. -/
theorem ClosedContainer.omega_fixed_point (c : ClosedContainer A)
    (f : c.carrier ⟶ c.carrier) :
    (A ◁ c.omega f) ≫ c.eval = c.eval ≫ f := by
  unfold omega
  rw [c.eval_name]

/-- Self-reference is omega of the identity: the quine is the fixed point
    of doing nothing. -/
theorem ClosedContainer.selfReference_eq_omega_id (c : ClosedContainer A) :
    c.selfReference = c.omega (𝟙 c.carrier) := by
  unfold selfReference omega
  rw [Category.comp_id]

/-- The reflexive object's omega agrees with the container's omega. -/
theorem ReflexiveObject.toClosedContainer_omega (r : ReflexiveObject A)
    (f : r.carrier ⟶ r.carrier) :
    r.toClosedContainer.omega f = r.omega f :=
  rfl

end FixedPoint.Reflexive
