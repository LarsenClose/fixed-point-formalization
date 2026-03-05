/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Convergence Criterion Theorem (Target 10).

The forward direction: chain convergence + Lambek → reflexive object →
self-application → Y combinator → computation. This assembles T2.5 + T3 + T4
into a single pipeline showing that dimensional convergence is sufficient for
the full computational structure.

The converse: if the Adamek chain for F does not converge (no initial F-algebra
exists), then there is no *initial* reflexive object from which to derive the
canonical Y combinator. Non-initial fixed points might exist but they would not
be canonical.

Key results:
  - `convergence_gives_reflexive`     : FixedPointSpec → ReflexiveObject
  - `convergence_gives_computation`   : FixedPointSpec → omega + omega_fixed_point
  - `ConvergencePipeline`             : structure packaging the full pipeline
  - `no_initial_algebra_no_canonical` : ¬ initial algebra → no ConvergencePipeline
-/

import FixedPoint.Reflexive.FixedPointCombinator
import FixedPoint.Dimension.Stabilization

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory

namespace FixedPoint.Dimension

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Forward direction: convergence → computation -/

/-- Step 1: A FixedPointSpec gives a ReflexiveObject. -/
def convergence_gives_reflexive {A : C} [Closed A]
    (fp : FixedPointSpec A) : Reflexive.ReflexiveObject A :=
  Reflexive.ReflexiveObject.fromSpec fp

/-- Step 2: The carrier of the reflexive object agrees with the spec's carrier. -/
theorem convergence_carrier_eq {A : C} [Closed A]
    (fp : FixedPointSpec A) :
    (convergence_gives_reflexive fp).carrier = fp.carrier :=
  rfl

/-- The full convergence pipeline: from a FixedPointSpec, we obtain all the
    computational primitives in sequence.

    This structure packages the complete forward direction:
    1. Fixed point L with ihom(A)(L) ≅ L (from Adamek + Lambek)
    2. Reflexive object with selfApp : A ⊗ L ⟶ L
    3. Y combinator omega with the fixed-point equation
    4. Dimension stability at L -/
structure ConvergencePipeline (A : C) [Closed A] where
  /-- The underlying fixed-point specification. -/
  spec : FixedPointSpec A
  /-- The reflexive object derived from the spec. -/
  reflexive : Reflexive.ReflexiveObject A
  /-- The reflexive object is derived from the spec. -/
  reflexive_eq : reflexive = Reflexive.ReflexiveObject.fromSpec spec

/-- Construct the full convergence pipeline from a FixedPointSpec. -/
def convergencePipeline {A : C} [Closed A]
    (fp : FixedPointSpec A) : ConvergencePipeline A where
  spec := fp
  reflexive := convergence_gives_reflexive fp
  reflexive_eq := rfl

/-- From the pipeline, extract self-application. -/
noncomputable def ConvergencePipeline.selfApp {A : C} [Closed A]
    (p : ConvergencePipeline A) : A ⊗ p.reflexive.carrier ⟶ p.reflexive.carrier :=
  p.reflexive.selfApp

/-- From the pipeline, extract the omega map (categorical Y combinator). -/
noncomputable def ConvergencePipeline.omega {A : C} [Closed A]
    (p : ConvergencePipeline A) (f : p.reflexive.carrier ⟶ p.reflexive.carrier) :
    p.reflexive.carrier ⟶ p.reflexive.carrier :=
  p.reflexive.omega f

/-- The pipeline's omega satisfies the fixed-point equation. -/
theorem ConvergencePipeline.omega_fixed_point {A : C} [Closed A]
    (p : ConvergencePipeline A) (f : p.reflexive.carrier ⟶ p.reflexive.carrier) :
    A ◁ p.omega f ≫ p.selfApp = p.selfApp ≫ f :=
  Reflexive.ReflexiveObject.omega_fixed_point p.reflexive f

/-- The pipeline's carrier satisfies dimension stability. -/
theorem ConvergencePipeline.dimension_stable {A : C} [Closed A]
    [SubstrateCategory C]
    (p : ConvergencePipeline A) {d : TruncationLevel} :
    HasDimension (ihom A) p.spec.carrier d ↔
    HasDimension (ihom A) ((ihom A).obj p.spec.carrier) d :=
  spec_dimension_iff p.spec

/-! ### Converse: no convergence → no canonical computation -/

/-- If no initial algebra of ihom(A) exists, then no ConvergencePipeline can
    be constructed. This is the contrapositive: the pipeline requires a
    FixedPointSpec, which requires an initial algebra.

    Note: non-initial fixed points might still exist (the functor could have
    non-initial algebras), but they would not yield the canonical construction.
    The convergence criterion is about *initial* algebras, which give uniqueness. -/
theorem no_initial_algebra_no_pipeline {A : C} [Closed A]
    (h : ∀ (alg : Endofunctor.Algebra (ihom A)), IsEmpty (IsInitial alg)) :
    ¬ ∃ _ : ConvergencePipeline A, True := by
  intro ⟨cp, _⟩
  exact (h cp.spec.algebra).false cp.spec.isInitial

/-- Equivalent formulation: from the non-existence of a FixedPointSpec,
    conclude the non-existence of all downstream constructions. -/
theorem no_spec_no_reflexive {A : C} [Closed A]
    (h : ¬ ∃ _ : FixedPointSpec A, True) :
    ¬ ∃ _ : Reflexive.ReflexiveObject A, True := by
  intro ⟨r, _⟩
  exact h ⟨r.spec, trivial⟩

/-! ### Categorical Lindstrom characterization -/

/-- A closed object A in a substrate category is computationally universal
    if the ihom(A) chain converges: there exists a FixedPointSpec yielding
    the full computational structure (reflexive object, Y combinator,
    dimension stability).

    This makes "computationally universal" a model-theoretic property of
    a category-with-structure, not a property of encodings. -/
def ComputationallyUniversal (A : C) [Closed A] : Prop :=
  ∃ _ : ConvergencePipeline A, True

/-- **Categorical Lindstrom characterization.**

    Computational universality (existence of the full pipeline: reflexive object,
    Y combinator, dimension stability) is equivalent to convergence of the
    ihom(A) chain (existence of an initial algebra with Lambek iso).

    This is a Lindstrom-type result: it characterizes computational universality
    as a closure/convergence property of a category-with-structure, not as a
    property of any particular encoding or model. Combined with the classical
    characterization theorem (`FixedPoint.ChurchTuring.characterization`), this
    says: once the chain converges, the resulting computation is unique up to
    equivalence. -/
theorem categorical_lindstrom (A : C) [Closed A] :
    ComputationallyUniversal A ↔ (∃ _ : FixedPointSpec A, True) :=
  ⟨fun ⟨cp, _⟩ => ⟨cp.spec, trivial⟩,
   fun ⟨fp, _⟩ => ⟨convergencePipeline fp, trivial⟩⟩

/-- In a substrate category where tensorLeft A preserves finite presentability,
    A is automatically computationally universal. The ihom(A) chain converges
    by the LFP route (AR 2.23 + Adamek). -/
theorem computationally_universal_of_tensor [SubstrateCategory C]
    (A : C) [Closed A] [TensorLeftFinitelyPresentable A] :
    ComputationallyUniversal A :=
  let ⟨fp, _⟩ := fixedPoint_exists A
  ⟨convergencePipeline fp, trivial⟩

end FixedPoint.Dimension
