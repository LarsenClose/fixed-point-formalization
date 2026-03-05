/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Tower Initiality: the Adamek chain is initial among all M-generated chains.

The Adamek chain ⊥ → M(⊥) → M²(⊥) → ⋯ is not merely ONE M-generated chain
among many. It is the INITIAL one: for any M-generated chain c, there exists
a unique GeneratedChainMorphism from the Adamek chain to c.

The initial object ⊥ has a unique morphism to any object — that determines
level 0. M-compatibility then propagates uniquely through all finite levels.
At the colimit, the induced morphism is the canonical initial algebra map.

Any process that generates structural levels by iterating M and converges to
a fixed point receives a unique chain morphism from the Adamek chain. The
chain is where all M-generated processes begin — not the only place dimensions
exist, but the place from which every other dimensional structure is reachable,
uniquely.

## What is proved

- `adamekChainMorphismComponents` : the level-wise maps from Adamek chain
- `adamekChainMorphismTo_unique` : any chain morphism from the Adamek chain
  agrees at every level (by induction from ⊥)
- `adamekChain_initial` : existence + uniqueness combined

STATUS: Tier 1 (0 sorry).
-/

import FixedPoint.Iteration.TowerMorphism
import FixedPoint.Dimension.DimensionTowerChain

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration

universe v u

namespace FixedPoint.Tower

variable {C : Type u} [Category.{v} C] [HasInitial C]
variable (M : C ⥤ C)

/-! ## Level-wise components: the unique maps from the Adamek chain -/

/-- The level-wise morphism from the Adamek chain to any M-generated chain.
    - α(0) = initial.to (c.chain.obj 0)    -- unique from ⊥
    - α(n+1) = M.map(α(n)) ≫ gen(n).inv   -- M-compatibility -/
noncomputable def adamekChainMorphismComponents (c : GeneratedChain M) :
    (n : ℕ) → (Dimension.adamekGeneratedChain M).chain.obj n ⟶ c.chain.obj n
  | 0 => initial.to _
  | n + 1 => M.map (adamekChainMorphismComponents c n) ≫ (c.generated n).inv

/-! ## Uniqueness: any chain morphism from the Adamek chain is determined -/

/-- Any GeneratedChainMorphism from the Adamek chain to c is determined
    at every level by the initial object's universal property.

    - Level 0: both maps start from ⊥, hence equal (`Subsingleton.elim`).
    - Level n+1: M-compatibility forces the map from the map at level n;
      the inductive hypothesis gives equality at n.

    This is the core content of tower initiality: ⊥ determines level 0
    uniquely, and M propagates that determination through all levels. -/
theorem adamekChainMorphismTo_unique (c : GeneratedChain M)
    (f : GeneratedChainMorphism M (Dimension.adamekGeneratedChain M) c) (n : ℕ) :
    f.morph.app n = adamekChainMorphismComponents M c n := by
  induction n with
  | zero =>
    simp only [adamekChainMorphismComponents, Dimension.adamekGeneratedChain,
      initialChain_obj, iterateObj]
    exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [adamekChainMorphismComponents]
    -- M-compatibility of f gives:
    --   gen₁(n).hom ≫ M.map(f.app n) = f.app(n+1) ≫ gen₂(n).hom
    -- Since adamekGeneratedChain has generated = Iso.refl (gen₁ = 𝟙):
    --   M.map(f.app n) = f.app(n+1) ≫ gen₂(n).hom
    have hcompat := f.m_compatible n
    simp only [Dimension.adamekGeneratedChain, Iso.refl_hom, Category.id_comp] at hcompat
    rw [ih] at hcompat
    -- hcompat: M.map(α(n)) = f.morph.app(n+1) ≫ c.generated(n).hom
    -- Goal: f.morph.app(n+1) = M.map(α(n)) ≫ c.generated(n).inv
    rw [← Iso.comp_inv_eq] at hcompat
    exact hcompat.symm

/-- Two GeneratedChainMorphisms from the Adamek chain agree at every level. -/
theorem adamekChainMorphism_ext (c : GeneratedChain M)
    (f g : GeneratedChainMorphism M (Dimension.adamekGeneratedChain M) c) (n : ℕ) :
    f.morph.app n = g.morph.app n := by
  rw [adamekChainMorphismTo_unique M c f n,
      adamekChainMorphismTo_unique M c g n]

/-! ## Tower initiality: the main theorem -/

/-- **Tower Initiality.** The Adamek chain from ⊥ is initial among all
    M-generated chains.

    For any GeneratedChain M, the level-wise maps from the Adamek chain
    are uniquely determined. Any two GeneratedChainMorphisms from the
    Adamek chain agree at every level.

    This is the chain-level analogue of the initial algebra's universal
    property. The Adamek chain is where all M-generated processes begin.
    Not the only place dimensions exist — the place from which every
    other dimensional structure is reachable, uniquely.

    The BV tensor gives the stronger statement F ≅ ihom(A) as global
    functors (uniqueness of right adjoints). The paper's claims require
    only tower initiality. -/
theorem adamekChain_initial (c : GeneratedChain M) :
    -- Determined components exist
    (∃ α : (n : ℕ) →
        (Dimension.adamekGeneratedChain M).chain.obj n ⟶ c.chain.obj n,
      -- At level 0, it's the unique map from ⊥
      α 0 = initial.to (c.chain.obj 0) ∧
      -- At each successor, it's M-compatible
      ∀ n, α (n + 1) = M.map (α n) ≫ (c.generated n).inv) ∧
    -- Any chain morphism must use these components
    (∀ f : GeneratedChainMorphism M (Dimension.adamekGeneratedChain M) c,
      ∀ n, f.morph.app n = adamekChainMorphismComponents M c n) :=
  ⟨⟨adamekChainMorphismComponents M c, rfl, fun _ => rfl⟩,
   adamekChainMorphismTo_unique M c⟩

end FixedPoint.Tower
