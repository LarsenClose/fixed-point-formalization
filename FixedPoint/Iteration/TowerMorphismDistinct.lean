/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Tower Morphism Distinct Instance: two FixedPointSpec chains collapse to initiality iso.

Given two `FixedPointSpec A` instances for the same closed object A, both produce
initial algebras of `ihom A`. The underlying Adamek chain is the same functor
`initialChain (ihom A)`, so both yield the canonical `GeneratedChain (ihom A)`.
The identity natural transformation is the chain morphism.

The non-trivial content: each `FixedPointSpec` identifies the chain's colimit with
its own carrier via the initiality isomorphism. The tower framework's `collapseMap`
(identity on the shared chain) composed with these identifications yields the
canonical initial algebra isomorphism `fixedPoint_unique fp₁ fp₂`.

This demonstrates the tower morphism framework on genuinely distinct colimit data:
two different initial algebra witnesses, two different carriers (in general),
connected by the universal property of initiality.

STATUS: Tier 1 (0 sorry).
-/

import FixedPoint.Iteration.TowerMorphismInstances
import FixedPoint.Specification.SubstrateIndependent

open CategoryTheory CategoryTheory.Limits Endofunctor
open FixedPoint.Iteration

universe v u

namespace FixedPoint.Tower

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SubstrateCategory C]
variable (A : C) [Closed A] [TensorLeftFinitelyPresentable A]

/-! ## Infrastructure: identification of colimit with FixedPointSpec carrier -/

/-- The Adamek algebra from the standard colimit of `initialChain (ihom A)`. -/
noncomputable def adamekSpec : FixedPointSpec A where
  algebra := adamekFromInitial (ihom A)
  isInitial := adamekFromInitial_isInitial (ihom A)

/-- The unique algebra isomorphism from the Adamek standard algebra to any
    FixedPointSpec's algebra, given by initiality. -/
noncomputable def adamekToSpec (fp : FixedPointSpec A) :
    (adamekSpec A).algebra ≅ fp.algebra :=
  (adamekSpec A).isInitial.uniqueUpToIso fp.isInitial

/-- The underlying morphism on carriers:
    `colimit (initialChain (ihom A)) ⟶ fp.algebra.a`. -/
noncomputable def colimitToCarrier (fp : FixedPointSpec A) :
    colimit (Iteration.initialChain (ihom A)) ⟶ fp.algebra.a :=
  (adamekToSpec A fp).hom.f

/-- The inverse: `fp.algebra.a ⟶ colimit (initialChain (ihom A))`. -/
noncomputable def carrierToColimit (fp : FixedPointSpec A) :
    fp.algebra.a ⟶ colimit (Iteration.initialChain (ihom A)) :=
  (adamekToSpec A fp).inv.f

/-- Round-trip: carrier → colimit → carrier is identity. -/
theorem carrierToColimit_colimitToCarrier (fp : FixedPointSpec A) :
    carrierToColimit A fp ≫ colimitToCarrier A fp = 𝟙 _ := by
  have h := congr_arg Algebra.Hom.f (Iso.inv_hom_id (adamekToSpec A fp))
  simp only [Algebra.comp_f, Algebra.id_f] at h
  exact h

/-- Round-trip: colimit → carrier → colimit is identity. -/
theorem colimitToCarrier_carrierToColimit (fp : FixedPointSpec A) :
    colimitToCarrier A fp ≫ carrierToColimit A fp = 𝟙 _ := by
  have h := congr_arg Algebra.Hom.f (Iso.hom_inv_id (adamekToSpec A fp))
  simp only [Algebra.comp_f, Algebra.id_f] at h
  exact h

/-! ## Two-spec generated chains and chain morphism -/

/-- Given two `FixedPointSpec A`, both produce the canonical `GeneratedChain (ihom A)`.
    We package them as a pair to make the distinct-chain structure explicit. -/
noncomputable def twoSpecGeneratedChains (_ _ : FixedPointSpec A) :
    GeneratedChain (ihom A) × GeneratedChain (ihom A) :=
  (generatedChainOfIHom A, generatedChainOfIHom A)

/-- The identity chain morphism between the two (identical) generated chains. -/
noncomputable def twoSpecChainMorphism (fp₁ fp₂ : FixedPointSpec A) :
    GeneratedChainMorphism (ihom A)
      (twoSpecGeneratedChains A fp₁ fp₂).1
      (twoSpecGeneratedChains A fp₁ fp₂).2 :=
  identityChainMorphism A

/-- **The distinct-spec collapse.** The tower framework's `collapseMap` on the
    identity chain morphism, composed with the initiality identifications, yields
    a morphism `fp₁.algebra.a ⟶ fp₂.algebra.a`.

    This is the non-trivial content: the chain is shared, but the colimit
    identifications go through two *different* initial algebra witnesses. -/
noncomputable def twoSpecCollapse (fp₁ fp₂ : FixedPointSpec A) :
    fp₁.algebra.a ⟶ fp₂.algebra.a :=
  carrierToColimit A fp₁ ≫
    collapseEndoOfIHom A ≫
    colimitToCarrier A fp₂

/-- **Key theorem: the collapse equals the initiality iso.**
    The tower-mediated morphism `fp₁.algebra.a ⟶ fp₂.algebra.a` equals
    `(fixedPoint_unique fp₁ fp₂).hom.f`, the canonical initial algebra
    isomorphism between the two carriers. -/
theorem twoSpecCollapse_is_unique (fp₁ fp₂ : FixedPointSpec A) :
    twoSpecCollapse A fp₁ fp₂ = (fixedPoint_unique fp₁ fp₂).hom.f := by
  unfold twoSpecCollapse
  -- collapseEndoOfIHom is the identity endomorphism
  have h_id := collapseEndoOfIHom_eq_id A
  -- Simplify: carrierToColimit ≫ 𝟙 ≫ colimitToCarrier = carrierToColimit ≫ colimitToCarrier
  conv_lhs => rw [h_id]; erw [Category.id_comp]
  -- Goal: carrierToColimit A fp₁ ≫ colimitToCarrier A fp₂ = (fixedPoint_unique fp₁ fp₂).hom.f
  -- LHS = (adamekToSpec fp₁).inv.f ≫ (adamekToSpec fp₂).hom.f
  --      = ((adamekToSpec fp₁).inv ≫ (adamekToSpec fp₂).hom).f
  change (adamekToSpec A fp₁).inv.f ≫ (adamekToSpec A fp₂).hom.f =
    (fixedPoint_unique fp₁ fp₂).hom.f
  rw [← Algebra.comp_f]
  -- Both sides are algebra homs fp₁ → fp₂; by initiality of fp₁, they're equal
  congr 1
  exact fp₁.isInitial.hom_ext _ _

/-- The collapse is an isomorphism, with inverse given by the reverse collapse. -/
noncomputable def twoSpecCollapseIso (fp₁ fp₂ : FixedPointSpec A) :
    fp₁.algebra.a ≅ fp₂.algebra.a where
  hom := twoSpecCollapse A fp₁ fp₂
  inv := twoSpecCollapse A fp₂ fp₁
  hom_inv_id := by
    rw [twoSpecCollapse_is_unique, twoSpecCollapse_is_unique, ← Algebra.comp_f]
    have : (fixedPoint_unique fp₂ fp₁).hom = (fixedPoint_unique fp₁ fp₂).inv :=
      fp₂.isInitial.hom_ext _ _
    rw [this, Iso.hom_inv_id]
    exact Algebra.id_f _
  inv_hom_id := by
    rw [twoSpecCollapse_is_unique, twoSpecCollapse_is_unique, ← Algebra.comp_f]
    have : (fixedPoint_unique fp₁ fp₂).hom = (fixedPoint_unique fp₂ fp₁).inv :=
      fp₁.isInitial.hom_ext _ _
    rw [this, Iso.hom_inv_id]
    exact Algebra.id_f _

end FixedPoint.Tower
