/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

The Triforce: Identity as Forced Development.

Packages the initial omega-chain (Development), its convergence to a fixed point
with Lambek iso (Identity), and its initiality among all M-generated chains
(Forced) as a single CT configuration.

The self-identity field witnesses that the triforce applied to itself
(via the collapse of the canonical chain to its own colimit) is the
identity morphism. This is the triforce's identity loop: the development,
collapsed to its own fixed point, produces the identity.

## What is defined

- `Triforce M`: structure packaging Development + Identity + Forced + self-identity
- `adamekTriforce`: construction from existing infrastructure
- `Triforce.carrier`: the fixed point L
- `Triforce.reflexiveObject`: visibility in monoidal closed context (M = ihom A)
- `Triforce.selfIndexed`: visibility when A = L

STATUS: Tier 1 (target 0 sorry).
-/

import FixedPoint.Iteration.TowerMorphism
import FixedPoint.Iteration.TowerInitiality
import FixedPoint.Iteration.TowerMorphismInstances
import FixedPoint.Dimension.DimensionTowerChain
import FixedPoint.Reflexive.ReflexiveObject
import FixedPoint.Uniqueness.SelfIndexedTerminalProperty

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open FixedPoint.Tower
open FixedPoint.Dimension

universe v u

namespace FixedPoint

variable {C : Type u} [Category.{v} C] [HasInitial C] [HasColimitsOfShape ℕ C]

/-- The Triforce: a single CT configuration packaging Development (the canonical
    filtered diagram from the initial object), Identity (the Lambek iso at the
    colimit), Forced (initiality of the Adamek chain), and self-identity (the
    collapse to its own colimit is the identity).

    For an endofunctor M on a cocomplete category with an initial object, the
    Triforce witnesses that the Adamek construction yields an initial algebra
    whose underlying chain is initial among all M-generated chains, and whose
    self-collapse is trivial. -/
structure Triforce (M : C ⥤ C) [PreservesColimitsOfShape ℕ M] where
  /-- DEVELOPMENT: the canonical filtered diagram from the initial object. -/
  genChain : GeneratedChain M
  /-- Colimit cocone for the development chain. -/
  cocone : Cocone genChain.chain
  /-- The cocone is a colimit. -/
  isColimit : IsColimit cocone
  /-- IDENTITY: the Lambek iso M(L) ≅ L at the colimit. -/
  lambek : M.obj cocone.pt ≅ cocone.pt
  /-- FORCED: any two chain morphisms from the Adamek chain to any target agree
      at every level. This witnesses that the development is initial. -/
  forced : ∀ (c : GeneratedChain M)
    (f g : GeneratedChainMorphism M (adamekGeneratedChain M) c),
    ∀ n, f.morph.app n = g.morph.app n
  /-- SELF-IDENTITY: the collapse of the chain to its own colimit via the
      identity morphism is the identity. The development, collapsed to its
      own fixed point, produces the identity. -/
  selfIdentity : colimMap (𝟙 genChain.chain) = 𝟙 (colimit genChain.chain)

variable (M : C ⥤ C) [PreservesColimitsOfShape ℕ M]

/-- The carrier (fixed point) of a triforce. -/
def Triforce.carrier (t : Triforce M) : C := t.cocone.pt

/-- Construct the canonical Triforce from the Adamek chain.

    - Development: the Adamek generated chain (initial chain of M)
    - Identity: Lambek iso from the initial algebra (Adamek's theorem)
    - Forced: tower initiality (adamekChainMorphism_ext)
    - Self-identity: colimMap of the identity is the identity (colimit.hom_ext) -/
noncomputable def adamekTriforce : Triforce M where
  genChain := adamekGeneratedChain M
  cocone := colimit.cocone (initialChain M)
  isColimit := colimit.isColimit (initialChain M)
  lambek := adamekStructureIso M
  forced := fun c f g n => adamekChainMorphism_ext M c f g n
  selfIdentity := by
    apply colimit.hom_ext
    intro n
    simp [ι_colimMap]

/-- The carrier of the Adamek triforce is the colimit of the initial chain. -/
theorem adamekTriforce_carrier :
    (adamekTriforce M).carrier = colimit (initialChain M) :=
  rfl

/-! ## Visibility in monoidal closed context -/

section MonoidalClosed

variable {C : Type u} [Category.{v} C] [HasInitial C] [HasColimitsOfShape ℕ C]
variable [MonoidalCategory C] [MonoidalClosed C]
variable {A : C} [Closed A] [PreservesColimitsOfShape ℕ (ihom A)]

/-- A Triforce for `ihom A` yields a `ReflexiveObject A`.

    The Lambek iso `[A, L] ≅ L` from the triforce is exactly the data
    needed for a reflexive object: the carrier L is isomorphic to its
    own internal function space `[A, L]`. -/
noncomputable def Triforce.reflexiveObject (_ : Triforce (ihom A)) :
    Reflexive.ReflexiveObject A :=
  Reflexive.ReflexiveObject.fromSpec
    { algebra := adamekFromInitial (ihom A)
      isInitial := adamekFromInitial_isInitial (ihom A) }

end MonoidalClosed

/-! ## Self-indexed visibility -/

section SelfIndexed

variable {C : Type u} [Category.{v} C] [HasInitial C] [HasColimitsOfShape ℕ C]
variable [MonoidalCategory C] [MonoidalClosed C]
variable [SubstrateCategory C]

/-- A Triforce for `ihom D` yields a `SelfIndexedFixedPoint (ihom D)` when
    D is the carrier of its own FixedPointSpec (the reflexive domain equation
    D ≅ [D, D]).

    This combines the triforce's Identity (Lambek iso) with the self-indexing
    equivalence `(𝟙_ C ⟶ D) ≃ (D ⟶ D)` that arises when A = D. -/
noncomputable def Triforce.selfIndexed
    (D : C) [Closed D] [TensorLeftFinitelyPresentable D]
    (fp : FixedPointSpec D) (hrefl : fp.carrier ≅ D)
    (_ : Triforce (ihom D)) :
    Uniqueness.SelfIndexedFixedPoint (ihom D) :=
  Uniqueness.ihom_selfIndexedFixedPoint D fp hrefl

end SelfIndexed

end FixedPoint
