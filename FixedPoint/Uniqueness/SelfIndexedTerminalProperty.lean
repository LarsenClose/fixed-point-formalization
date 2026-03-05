/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Self-Indexed Terminal Property.

Revised terminal characterization conjecture using the self-indexing condition:
the fixed point D of an endofunctor F satisfies Hom(𝟙, D) ≃ Hom(D, D)
(global sections biject with endomorphisms).

## Mathematical context

The naive terminal characterization — "any endofunctor with a least fixed point
is isomorphic to the internal hom" — is false. Counterexamples:
- Powerset functor: has Adamek fixed point but is not a right adjoint
- Identity functor: id ⊣ id but the fixed point is trivial

The self-indexing condition discriminates:
- Powerset: P(D) ≅ D does NOT give Hom(𝟙, D) ≅ Hom(D, D)
- Identity: trivial fixed points don't self-index nontrivially
- Internal hom at A = D: [D, D] ≅ D DOES give self-indexing via curryEquiv

Key finding: self-indexing Hom(𝟙, D) ≅ Hom(D, D) requires A = D in the
reflexive object framework. That is, the object we take ihom of IS the
fixed point itself. This gives D ≅ [D, D]: the reflexive domain equation.

## What is proved

- `SelfIndexedFixedPoint F` : structure packaging the self-indexing condition
- `selfIndexingEquiv` : constructs the self-indexing Equiv from a reflexive
  object with A ≅ carrier (the reflexive domain equation)
- `hasAdamekFixedPoint_of_spec` : builds HasAdamekFixedPoint from FixedPointSpec
- `ihom_selfIndexedFixedPoint` : ihom(D) satisfies SelfIndexedFixedPoint
  when D is itself the parameter (A = D case, requires carrier ≅ D)

## What is conjectured

- `self_indexed_terminal_conjecture` : if F has a self-indexed Adamek fixed
  point in a monoidal closed LFP category, then F ≅ ihom(A) for some A

STATUS: Tier 1 definitions + Tier 2 conjecture. 0 sorry in proved results.
-/

import FixedPoint.Uniqueness.TerminalCharacterization
import FixedPoint.Reflexive.SelfIndexedComputation

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open MonoidalCategory

namespace FixedPoint.Uniqueness

universe v u

/-! ### SelfIndexedFixedPoint: the self-indexing condition -/

/-- An endofunctor `F` has a self-indexed fixed point if it has an Adamek
    fixed point D whose global sections biject with its endomorphisms:
    `(𝟙_ C ⟶ D) ≃ (D ⟶ D)`.

    This condition says D's "points" parametrize all of D's self-maps.
    It is the categorical abstraction of computational universality:
    every program (global section) names a unique function (endomorphism),
    and every function has a name. -/
structure SelfIndexedFixedPoint {C : Type u} [Category.{v} C]
    [MonoidalCategory C] (F : C ⥤ C) where
  /-- The Adamek fixed point data. -/
  adamek : HasAdamekFixedPoint F
  /-- Global sections of the carrier biject with its endomorphisms. -/
  selfIndexing : (𝟙_ C ⟶ adamek.carrier) ≃ (adamek.carrier ⟶ adamek.carrier)

/-! ### Self-indexing from a reflexive object with A = D

When the reflexive object has parameter A equal to its carrier D
(i.e., D ≅ [D, D]), the curryEquiv at X = 𝟙_ C gives:

  (D ⊗ 𝟙_ C ⟶ D) ≃ (𝟙_ C ⟶ D)

Via the right unitor D ⊗ 𝟙_ C ≅ D, this becomes (D ⟶ D) ≃ (𝟙_ C ⟶ D).
Inverting: (𝟙_ C ⟶ D) ≃ (D ⟶ D). That is the self-indexing condition. -/

section SelfIndexingFromReflexive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The self-indexing equivalence for a reflexive object with A = carrier.
    Uses curryEquiv at X = 𝟙_ C composed with the right unitor.

    When the reflexive object has parameter A = carrier D, curryEquiv at
    X = 𝟙_ C gives `(D ⊗ 𝟙_ C ⟶ D) ≃ (𝟙_ C ⟶ D)`. Composing the
    inverse with the right unitor `D ⊗ 𝟙_ C ≅ D` gives
    `(𝟙_ C ⟶ D) ≃ (D ⟶ D)`: the self-indexing condition. -/
noncomputable def selfIndexingEquiv {D : C} [Closed D]
    (r : Reflexive.ReflexiveObject D)
    (hcarrier : r.carrier ≅ D) :
    (𝟙_ C ⟶ r.carrier) ≃ (r.carrier ⟶ r.carrier) where
  toFun s := hcarrier.hom ≫ (ρ_ D).inv ≫ (r.curryEquiv (𝟙_ C)).symm s
  invFun f := (r.curryEquiv (𝟙_ C)) ((ρ_ D).hom ≫ hcarrier.inv ≫ f)
  left_inv s := by
    simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    exact (r.curryEquiv (𝟙_ C)).apply_symm_apply s
  right_inv f := by
    simp only [Equiv.symm_apply_apply,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

end SelfIndexingFromReflexive

/-! ### ihom(D) has a self-indexed fixed point when D ≅ [D, D]

If D is a closed object with a `FixedPointSpec D` whose carrier is isomorphic
to D itself (the reflexive domain equation D ≅ [D, D]), then ihom(D)
has a self-indexed Adamek fixed point. -/

section IHomSelfIndexed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C] [HasInitial C]

/-- Build a `HasAdamekFixedPoint` directly from a `FixedPointSpec`. -/
noncomputable def hasAdamekFixedPoint_of_spec
    {A : C} [Closed A] (fp : FixedPointSpec A) :
    HasAdamekFixedPoint (ihom A) where
  carrier := fp.carrier
  algebraStr := fp.algebra.str
  strIsIso := fp.strIso
  isInitial := fp.isInitial

/-- ihom(D) has a self-indexed Adamek fixed point when D satisfies the
    reflexive domain equation: D is the carrier of its own FixedPointSpec.
    This is the A = D case where self-indexing holds. -/
noncomputable def ihom_selfIndexedFixedPoint
    (D : C) [Closed D]
    (fp : FixedPointSpec D) (hrefl : fp.carrier ≅ D) :
    SelfIndexedFixedPoint (ihom D) where
  adamek := hasAdamekFixedPoint_of_spec fp
  selfIndexing :=
    selfIndexingEquiv (Reflexive.ReflexiveObject.fromSpec fp) hrefl

end IHomSelfIndexed

/-! ### Negative findings: why the naive conditions fail

Documenting the obstructions found during T17 investigation.

**Condition (i) from the original proposal: F(⊥) ≅ ⊥.**

In a Cartesian closed category: [⊥, B] ≅ 𝟙_ C (terminal, not initial).
This is Mathlib's `powZero`. So ihom(⊥) does NOT preserve the initial object
in CCC. For ihom(A) with A ≇ ⊥: in Set, [A, ∅] = ∅ when A ≠ ∅, so
ihom(A) DOES preserve initial when A is "nonempty." The general monoidal
closed case is uncharted in Mathlib.

**Condition (iii): self-indexing requires A = D.**

The curryEquiv `(A ⊗ X ⟶ D) ≃ (X ⟶ D)` at X = 𝟙 gives `(A ⟶ D) ≃ (𝟙 ⟶ D)`
(via right unitor). At X = D it gives `(A ⊗ D ⟶ D) ≃ (D ⟶ D)`. To bridge
these into `(𝟙 ⟶ D) ≃ (D ⟶ D)` requires `(A ⟶ D) ≃ (A ⊗ D ⟶ D)`, which
is NOT generally true. It holds precisely when A = D (the reflexive domain
equation D ≅ [D, D]).

**The chain-propagation argument gap.**

Even granting self-indexing, the argument "F and [A, -] agree at ⊥ and at D,
hence they agree on the whole chain" requires F and [A, -] to agree at each
chain stage, which is exactly what we're trying to prove. The argument is
circular without additional structure (e.g., F being determined by its
behavior on a generating set that includes the chain objects). -/

/-! ### The revised conjecture -/

section Conjecture

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C]
variable [HasInitial C]

/-- **Revised terminal property (formal conjecture).**

    In a monoidal closed, locally finitely presentable category, if an
    ω-continuous endofunctor F has a self-indexed Adamek fixed point, then
    F is naturally isomorphic to the internal hom functor ihom(A) for some
    closed object A.

    This is stated as a Prop to make clear it is a conjecture. The self-indexing
    condition excludes the known counterexamples (powerset, identity).

    The conjecture is plausible because:
    - Self-indexing forces the fixed point to satisfy D ≅ [D, D]
    - In LFP categories, accessible functors are determined by behavior on
      presentable objects
    - The Adamek chain from ⊥ generates the fixed point

    Known obstructions to proving it:
    - Identifying A: likely A = D (the carrier), but proving F ≅ [D, -] as
      functors (not just at D) requires density/generation arguments
    - No Mathlib result for "terminal is a detector" in abstract categories
    - Chain propagation argument has a circularity (see negative findings above) -/
def self_indexed_terminal_conjecture : Prop :=
  ∀ (F : C ⥤ C) [PreservesColimitsOfShape ℕ F],
    SelfIndexedFixedPoint F →
    ∃ (A : C) (_ : Closed A), Nonempty (F ≅ ihom A)

end Conjecture

end FixedPoint.Uniqueness
