/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Self-Indexed Computation (Layer 2 of the Kleene bridge).

A reflexive object D with [A, D] ≅ D is already a self-indexed computation
model: D indexes its own function space, selfApp is the universal evaluator,
and the Y combinator provides self-reference. No external enumeration (ℕ) is
needed — the object D serves as both the "type of programs" and the "type of
data."

This file repackages ReflexiveObject's categorical data as computation
vocabulary, making explicit that the reflexive structure IS a computation
model (self-indexed by D rather than ℕ-indexed).

## Architecture

Layer 1 (done): ReflexiveObject — categorical data (iso, selfApp, omega)
Layer 2 (this file): SelfIndexedComputation — computation vocabulary
Layer 3 (KleeneDerivation): ℕ-bridge via ComputabilityStructure → CompModel

The key insight: universality and self-reference are not added axioms but
consequences of D ≅ [A, D]. The Lambek isomorphism IS the naming function.
The CCC curry IS the s-m-n theorem. The Y combinator IS Kleene's recursion
theorem. These identifications are the content of this file.

## What is proved

- `naming_equiv`: every morphism A ⊗ X → D bijects with morphisms X → D
  (programs name parameterized families)
- `global_section_naming`: every morphism A → D is named by a unique global
  section of D (specialization at X = 𝟙_ C)
- `selfApp_evaluates`: selfApp composed with a global section recovers the
  named morphism
- `self_indexed_kleene`: omega_fixed_point rephrased in computation terms
- `selfIndexedAFPP`: connection to AbstractFixedPointProperty

STATUS: Tier 1 (no sorry).
-/

import FixedPoint.Reflexive.FixedPointCombinator

universe v u

open CategoryTheory
open MonoidalCategory

namespace FixedPoint.Reflexive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A : C} [Closed A]

/-! ### The naming equivalence

The reflexive isomorphism [A, D] ≅ D induces a bijection between
morphisms A ⊗ X → D and morphisms X → D for every X. This is the
curryEquiv of the reflexive object.

In computation terms: morphisms X → D are "programs parameterized by X",
and morphisms A ⊗ X → D are "functions from A-inputs parameterized by X."
The bijection says every parameterized function has a unique program name,
and every program name denotes a unique parameterized function. -/

/-- The naming equivalence: morphisms A ⊗ X → D biject with morphisms X → D.
    This is universality at object X — every A-valued function parameterized
    by X is uniquely named by a morphism X → D. -/
noncomputable def naming_equiv (r : ReflexiveObject A) (X : C) :
    (A ⊗ X ⟶ r.carrier) ≃ (X ⟶ r.carrier) :=
  r.curryEquiv X

/-- At X = 𝟙_ C: every morphism A ⊗ 𝟙_ C → D is named by a global section.
    Since A ⊗ 𝟙_ C ≅ A (right unitor), this says every A-morphism into D
    has a unique global section name in D. -/
noncomputable def global_section_naming (r : ReflexiveObject A) :
    (A ⊗ 𝟙_ C ⟶ r.carrier) ≃ (𝟙_ C ⟶ r.carrier) :=
  r.curryEquiv (𝟙_ C)

/-! ### Universality: the Lambek iso names all functions

The naming equivalence is surjective in both directions (it's an Equiv).
This means:
- Every A-valued function has a name (universality / no gaps)
- Every name denotes a function (representability / no junk)

These correspond exactly to the `universal` and `representable` axioms
of CompModel, but without reference to ℕ or Code. -/

/-- Universality: every morphism A ⊗ X → D is named by some morphism X → D.
    This is surjectivity of the naming equivalence. -/
theorem naming_surjective (r : ReflexiveObject A) (X : C)
    (f : A ⊗ X ⟶ r.carrier) : ∃ p : X ⟶ r.carrier,
    r.reflexiveUncurry p = f :=
  ⟨r.reflexiveCurry f, r.reflexiveUncurry_reflexiveCurry f⟩

/-- Representability: every morphism X → D names some morphism A ⊗ X → D.
    This is surjectivity of the inverse naming. -/
theorem naming_representable (r : ReflexiveObject A) (X : C)
    (p : X ⟶ r.carrier) : ∃ f : A ⊗ X ⟶ r.carrier,
    r.reflexiveCurry f = p :=
  ⟨r.reflexiveUncurry p, r.reflexiveCurry_reflexiveUncurry p⟩

/-! ### selfApp as the universal evaluator

selfApp : A ⊗ D → D is the universal evaluation morphism. Given a
"program" (element of D) and an "input" (element of A), it decodes the
program via the Lambek iso and evaluates it.

The key property: selfApp is the uncurrying of the identity on D.
Composing a global section with selfApp evaluates the named function. -/

/-- selfApp is exactly reflexiveUncurry of the identity: the universal
    evaluator that decodes any element of D as a function and runs it. -/
theorem selfApp_is_uncurry_id (r : ReflexiveObject A) :
    r.selfApp = r.reflexiveUncurry (𝟙 r.carrier) :=
  r.selfApp_eq_reflexiveUncurry_id

/-- Composing a name p : X → D with selfApp recovers the named function
    (up to the reflexive curry/uncurry round trip). -/
theorem selfApp_recovers_named (r : ReflexiveObject A)
    {X : C} (f : A ⊗ X ⟶ r.carrier) :
    (A ◁ r.reflexiveCurry f) ≫ r.selfApp = f := by
  -- General whisker-selfApp identity: (A ◁ g) ≫ selfApp = reflexiveUncurry g
  have whisker_selfApp : ∀ {Y : C} (g : Y ⟶ r.carrier),
      (A ◁ g) ≫ r.selfApp = r.reflexiveUncurry g := by
    intro Y g
    simp only [ReflexiveObject.selfApp, ReflexiveObject.reflexiveUncurry,
      MonoidalClosed.uncurry_eq, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  rw [whisker_selfApp, r.reflexiveUncurry_reflexiveCurry]

/-! ### Self-indexed Kleene recursion theorem

The omega construction gives: for every endomorphism f : D → D, there
exists omega(f) : D → D satisfying the fixed-point equation

  A ◁ omega(f) ≫ selfApp = selfApp ≫ f

In computation terms: omega(f) is a program whose evaluation under
selfApp equals the evaluation of selfApp post-composed with f. This
is the morphism-level Kleene recursion theorem — every "computable
transformation" (endomorphism) has a semantic fixed point. -/

/-- The self-indexed Kleene recursion theorem: every endomorphism of D
    has a semantic fixed point, witnessed by the omega construction. -/
theorem self_indexed_kleene (r : ReflexiveObject A)
    (f : r.carrier ⟶ r.carrier) :
    A ◁ r.omega f ≫ r.selfApp = r.selfApp ≫ f :=
  r.omega_fixed_point f

/-! ### The self-indexed computation structure

Package everything into a single structure that says: a reflexive object
IS a computation model, with D as both the program space and the data space. -/

/-- A self-indexed computation: D simultaneously serves as the type of
    programs and the type of data. The Lambek iso provides naming,
    selfApp provides evaluation, and omega provides self-reference.

    This is NOT a CompModel (which requires ℕ-indexing). It is a
    strictly more general structure that captures the computational
    content of D ≅ [A, D] without reference to natural numbers. -/
structure SelfIndexedComputation (A : C) [Closed A] where
  /-- The reflexive object providing all the structure. -/
  refl : ReflexiveObject A
  /-- Naming equivalence: programs biject with functions at every base. -/
  naming : ∀ X, (A ⊗ X ⟶ refl.carrier) ≃ (X ⟶ refl.carrier)
  /-- The evaluation morphism: decode and run. -/
  evaluator : A ⊗ refl.carrier ⟶ refl.carrier
  /-- Evaluation recovers the named function. -/
  eval_recovers : ∀ {X : C} (f : A ⊗ X ⟶ refl.carrier),
    (A ◁ (naming X).toFun f) ≫ evaluator = f
  /-- Every endomorphism has a semantic fixed point. -/
  fixed_point : ∀ f : refl.carrier ⟶ refl.carrier,
    A ◁ refl.omega f ≫ evaluator = evaluator ≫ f

/-- Every reflexive object gives a self-indexed computation. -/
noncomputable def selfIndexedComputation (r : ReflexiveObject A) :
    SelfIndexedComputation A where
  refl := r
  naming := fun X => r.curryEquiv X
  evaluator := r.selfApp
  eval_recovers := fun f => selfApp_recovers_named r f
  fixed_point := fun f => r.omega_fixed_point f

/-! ### Connection to AbstractFixedPointProperty

The self-indexed computation satisfies the abstract fixed-point property
from KleeneBridge.lean, with:
- Obj = endomorphisms D → D
- Equiv = selfApp-mediated equality -/

/-- The self-indexed computation gives an abstract fixed-point property
    for post-composition endomorphisms, mediated by selfApp.

    For every endomorphism f : L → L, omega(f) is a fixed point of
    "post-compose with f" under the selfApp equivalence:
      A ◁ omega(f) ≫ selfApp = selfApp ≫ f = A ◁ id ≫ selfApp ≫ f -/
theorem selfIndexedAFPP (r : ReflexiveObject A) (f : r.carrier ⟶ r.carrier) :
    ∃ p : r.carrier ⟶ r.carrier,
      A ◁ p ≫ r.selfApp = r.selfApp ≫ f :=
  ⟨r.omega f, r.omega_fixed_point f⟩

/-! ### The bridge to ℕ-indexed computation (Layer 3 interface)

To go from SelfIndexedComputation to CompModel requires three things:
1. Denumerable (𝟙_ C ⟶ D) — countable global sections (programs)
2. An interpretation : (𝟙_ C ⟶ D) → ℕ →. ℕ — semantics extraction
3. Compatibility with Nat.Partrec.Code — connecting to Mathlib's partrec

These are the axioms of KleeneDerivation.ComputabilityStructure. They
are not derivable from category theory alone — they require the ambient
category to be "effectively presentable" (hom-sets between finitely
presentable objects are countable).

The self-indexed computation structure is the substrate-independent part.
The ℕ-bridge is the classical-recursion-theory part. The paper's claim
is that the substrate-independent part already carries all the structural
content of computation; the ℕ-bridge is a representation choice. -/

end FixedPoint.Reflexive
