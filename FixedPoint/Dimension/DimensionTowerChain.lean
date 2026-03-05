/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Dimension-Tower Chain Bridge.

Connects the dimension/iteration infrastructure to the TowerMorphism
GeneratedChain framework. The Adamek initial chain for any endofunctor F
on a category with an initial object is a `GeneratedChain F`, and each
level carries its canonical dimension from the graded filtration.

This bridges the paper's claim that "every dimensional tower instantiates
the collapse principle": the graded filtration produces a strict N-indexed
tower, and that tower is a GeneratedChain, so it inherits the full
collapse theorem from TowerMorphism.lean.

Key definitions and results:
  - `adamekGeneratedChain F`          : the initial chain as a GeneratedChain
  - `adamekIdentityMorphism F`        : identity self-morphism of the chain
  - `generatedChain_hasDimension`     : level n has dimension chainDimension n
  - `generatedChain_strict_grading`   : distinct levels have distinct dimensions
  - `generatedChain_dimension_stable` : at a fixed point, dimension is stable

STATUS: Tier 1 (0 sorry).
-/

import FixedPoint.Iteration.TowerMorphism
import FixedPoint.Dimension.DimensionIncrement

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open FixedPoint.Dimension
open FixedPoint.Dimension.TruncationLevel

namespace FixedPoint.Dimension

universe v u

variable {C : Type u} [Category.{v} C] [HasInitial C]

/-! ## The Adamek chain as a GeneratedChain -/

/-- The Adamek initial chain for any endofunctor F is a `GeneratedChain F`.
    The key property `chain.obj (n+1) ≅ F.obj (chain.obj n)` holds
    definitionally since `iterateObj F (n+1) = F.obj (iterateObj F n)`. -/
noncomputable def adamekGeneratedChain (F : C ⥤ C) :
    Tower.GeneratedChain F where
  chain := initialChain F
  generated := fun _ => Iso.refl _

/-! ## Identity self-morphism -/

/-- The identity natural transformation on the Adamek chain is trivially
    F-compatible, yielding a `GeneratedChainMorphism`. This is the
    canonical self-morphism whose collapse is the identity (see
    TowerMorphismInstances for the ihom specialization). -/
noncomputable def adamekIdentityMorphism (F : C ⥤ C) :
    Tower.GeneratedChainMorphism F
      (adamekGeneratedChain F) (adamekGeneratedChain F) where
  morph := 𝟙 (adamekGeneratedChain F).chain
  m_compatible := fun _ => by
    simp only [adamekGeneratedChain, Iso.refl_hom, Category.id_comp,
      NatTrans.id_app, Category.comp_id]
    exact F.map_id _

/-! ## Dimension at each level of the generated chain -/

/-- Each level of the Adamek generated chain carries its canonical
    dimension from the graded filtration: level n has dimension
    `chainDimension n`. -/
theorem generatedChain_hasDimension (F : C ⥤ C) (n : ℕ) :
    HasDimension F ((adamekGeneratedChain F).chain.obj n) (chainDimension n) :=
  iterate_has_dimension F n

/-- The graded filtration ensures distinct levels of the generated chain
    have distinct dimensions, making the chain a strict filtration. -/
theorem generatedChain_strict_grading {n m : ℕ} (h : n ≠ m) :
    chainDimension n ≠ chainDimension m :=
  chain_is_graded h

/-- At a fixed point L of F, dimension is stable under F: an object has
    dimension d iff F applied to it has dimension d. Combined with the
    generated chain structure, this shows the collapse at the colimit
    preserves the dimensional filtration. -/
theorem generatedChain_dimension_stable (F : C ⥤ C) (L : C)
    (lamb : F.obj L ≅ L) (d : TruncationLevel) :
    HasDimension F L d ↔ HasDimension F (F.obj L) d :=
  (graded_filtration F L lamb).2.2.2 d

end FixedPoint.Dimension
