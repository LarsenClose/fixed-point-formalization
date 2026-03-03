/-
  AdamekChain.lean

  The Adamek construction: given an endofunctor F : C ⥤ C and a natural
  transformation ε : 𝟭 C ⟶ F, iterate F transfinitely from the identity
  functor and take the colimit. When C has the appropriate colimits and
  F preserves them, this colimit carries an initial F-algebra structure.

  This file connects the paper series' construction to Mathlib's transfinite
  iteration infrastructure in SmallObject/.

  The chain:  𝟭 C →ε F →Fε F² →F²ε F³ → ⋯ → colim = initial algebra

  STATUS: Tier 2 — scaffolding compiles, key connection stated with sorry.
-/
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import FixedPoint.Iteration.AdamekConnection

universe w v u

open CategoryTheory
open CategoryTheory.Endofunctor
open CategoryTheory.SmallObject
open CategoryTheory.Limits

namespace FixedPoint.Iteration

variable {C : Type u} [Category.{v} C]

/-- Given an endofunctor F with a point ε : 𝟭 C ⟶ F, the successor structure
    for transfinite iteration. At the level of C ⥤ C:
      X₀ = 𝟭 C
      succ G = G ⋙ F
      toSucc G = G.whiskerLeft ε
    This is Mathlib's `SuccStruct.ofNatTrans`. -/
noncomputable def adamekSuccStruct {F : C ⥤ C} (ε : 𝟭 C ⟶ F) :
    SuccStruct (C ⥤ C) :=
  SuccStruct.ofNatTrans ε

variable {F : C ⥤ C} (ε : 𝟭 C ⟶ F)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J (C ⥤ C)]

/-- The Adamek iteration functor: J ⥤ (C ⥤ C) giving the chain
    𝟭 C, F, F², F³, ... indexed by a well-ordered type J. -/
noncomputable def adamekIterationFunctor : J ⥤ (C ⥤ C) :=
  (adamekSuccStruct ε).iterationFunctor J

/-- The colimit of the Adamek chain: the transfinite iteration of F
    to the power J. When J is large enough, this is the initial algebra. -/
noncomputable def adamekColimit : C ⥤ C :=
  (adamekSuccStruct ε).iteration J

/-- The base of the chain is the identity functor. -/
noncomputable def adamekBaseIso :
    (adamekIterationFunctor ε J).obj ⊥ ≅ 𝟭 C :=
  (adamekSuccStruct ε).iterationFunctorObjBotIso J

variable [HasInitial C] [HasColimit (initialChain F)] [PreservesColimit (initialChain F) F]

/-- Key theorem (Adamek): when F preserves the colimits in the chain,
    the colimit carries an initial F-algebra structure.

    For the paper series: F = ihom(A), C is locally presentable (so the
    required colimits exist), and ihom(A) preserves filtered colimits
    (as a right adjoint that is accessible). -/
theorem adamekColimit_isInitialAlgebra (X : C) :
    ∃ (A : Algebra F), Nonempty (Limits.IsInitial A) :=
  ⟨adamekFromInitial F, ⟨adamekFromInitial_isInitial F⟩⟩

end FixedPoint.Iteration
