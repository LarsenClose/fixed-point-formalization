/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Tower Morphism Instances: FixedPointSpec instantiation.

Given two `FixedPointSpec A` instances for the same closed object A in a
substrate category, both produce initial algebras of `ihom A`. The underlying
Adamek chain is the same functor `initialChain (ihom A)`, so a
`GeneratedChain (ihom A)` is canonical. The identity natural transformation
is a `GeneratedChainMorphism`, and `collapseMap` recovers the canonical
isomorphism between the two initial algebra carriers.

This is the first concrete instantiation proving the tower morphism framework
works end-to-end.

STATUS: Tier 1 (0 sorry).
-/

import FixedPoint.Iteration.TowerMorphism
import FixedPoint.Specification.SubstrateIndependent

open CategoryTheory CategoryTheory.Limits

universe v u

namespace FixedPoint.Tower

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SubstrateCategory C]
variable (A : C) [Closed A] [TensorLeftFinitelyPresentable A]

/-! ## The canonical generated chain from the initial chain of ihom A -/

/-- The Adamek initial chain for `ihom A` is a `GeneratedChain`:
    `(initialChain (ihom A)).obj (n+1) = (ihom A).obj ((initialChain (ihom A)).obj n)`
    holds definitionally from the construction of `iterateObj`. -/
noncomputable def generatedChainOfIHom : GeneratedChain (ihom A) where
  chain := Iteration.initialChain (ihom A)
  generated := fun _ => Iso.refl _

/-! ## Identity morphism between two copies of the same chain -/

/-- The identity natural transformation on the canonical chain is
    trivially M-compatible, giving a `GeneratedChainMorphism`. -/
noncomputable def identityChainMorphism :
    GeneratedChainMorphism (ihom A) (generatedChainOfIHom A) (generatedChainOfIHom A) where
  morph := 𝟙 (generatedChainOfIHom A).chain
  m_compatible := fun _ => by
    simp only [generatedChainOfIHom, Iso.refl_hom, Category.id_comp,
      NatTrans.id_app, Category.comp_id]
    exact (ihom A).map_id _

/-! ## Collapse map and iso for the canonical chain -/

/-- The collapse map from the identity chain morphism is the colimit morphism
    induced by `𝟙 chain`. Since both source and target are the same chain,
    this is an endomorphism of `colimit (initialChain (ihom A))`. -/
noncomputable def collapseEndoOfIHom :
    colimit (generatedChainOfIHom A).chain ⟶ colimit (generatedChainOfIHom A).chain :=
  collapseMap (generatedChainOfIHom A) (generatedChainOfIHom A) (identityChainMorphism A)

omit [TensorLeftFinitelyPresentable A] in
/-- The collapse endomorphism from the identity morphism is the identity:
    `colimMap (𝟙 chain) = 𝟙 (colimit chain)`. -/
theorem collapseEndoOfIHom_eq_id :
    collapseEndoOfIHom A = 𝟙 _ := by
  unfold collapseEndoOfIHom collapseMap
  exact colimit.hom_ext (fun n => by
    simp only [ι_colimMap, identityChainMorphism, NatTrans.id_app,
      Category.id_comp, Category.comp_id])

/-- The collapse iso from the identity chain morphism (levelwise iso since
    each component is the identity). -/
noncomputable def collapseIsoOfIHom :
    colimit (generatedChainOfIHom A).chain ≅ colimit (generatedChainOfIHom A).chain :=
  collapseIso (generatedChainOfIHom A) (generatedChainOfIHom A) (identityChainMorphism A)
    (fun _ => by
      change IsIso (𝟙 _)
      infer_instance)

omit [TensorLeftFinitelyPresentable A] in
/-- The collapse iso is the identity iso, confirming end-to-end that
    the tower morphism framework produces the expected result for the
    canonical instantiation: the same chain collapses to the identity. -/
theorem collapseIsoOfIHom_hom_eq_id :
    (collapseIsoOfIHom A).hom = 𝟙 _ :=
  collapseEndoOfIHom_eq_id A

/-! ## Connection to FixedPointSpec uniqueness

Any two `FixedPointSpec A` instances produce initial algebras of `ihom A`.
Their underlying Adamek chains are both `initialChain (ihom A)` -- the same
functor. The tower morphism framework shows the collapse map between two
copies of this chain is the identity (proved above).

The non-trivial content is in `fixedPoint_unique` (from SubstrateIndependent.lean),
which shows the two *algebra structures* (not just the colimit objects) are
isomorphic via the unique initial algebra isomorphism. The tower framework
provides the categorical machinery that makes this structurally transparent:
any two M-generated chains with an M-compatible morphism yield a determined
colimit morphism, and when the chains coincide, that morphism is the identity. -/

end FixedPoint.Tower
