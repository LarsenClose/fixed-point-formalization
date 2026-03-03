/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

The initial chain functor ℕ ⥤ C for an endofunctor F : C ⥤ C.

Given a category C with an initial object ⊥ and an endofunctor F,
the initial chain is the sequence ⊥ → F(⊥) → F²(⊥) → ⋯ viewed as
a functor from ℕ (as a preorder category) to C.

Key definitions:
  - `iterateObj F n`    : the n-th iterate F^n(⊥)
  - `iterateMap F n`    : the successor map F^n(⊥) → F^{n+1}(⊥)
  - `initialChain F`    : the functor ℕ ⥤ C

Main results:
  - `initialChain_obj`          : (initialChain F).obj n = iterateObj F n
  - `initialChain_map_succ`     : the map for n ≤ n+1 is iterateMap F n
  - `initialChain_map_succ_eq`  : the chain map at successor indices = F applied to chain map
-/

import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory CategoryTheory.Limits

namespace FixedPoint.Iteration

universe v u

variable {C : Type u} [Category.{v} C]

section Definitions

variable (F : C ⥤ C) [HasInitial C]

/-- The n-th iterate of F applied to the initial object: F^n(⊥). -/
noncomputable def iterateObj : ℕ → C
  | 0 => ⊥_ C
  | n + 1 => F.obj (iterateObj n)

/-- The successor map F^n(!) : F^n(⊥) → F^{n+1}(⊥), defined by applying F to the
    unique map from the initial object. -/
noncomputable def iterateMap : (n : ℕ) → iterateObj F n ⟶ iterateObj F (n + 1)
  | 0 => initial.to _
  | n + 1 => F.map (iterateMap n)

end Definitions

section Functor

variable (F : C ⥤ C) [HasInitial C]

-- ✓ TIER 1
/-- The initial chain: the functor ℕ ⥤ C sending n to F^n(⊥),
    constructed via `Functor.ofSequence` from the successor maps. -/
noncomputable def initialChain : ℕ ⥤ C :=
  Functor.ofSequence (X := iterateObj F) (iterateMap F)

-- ✓ TIER 1
@[simp]
theorem initialChain_obj (n : ℕ) :
    (initialChain F).obj n = iterateObj F n := rfl

-- ✓ TIER 1
@[simp]
theorem initialChain_map_succ (n : ℕ) :
    (initialChain F).map (homOfLE (Nat.le_add_right n 1)) = iterateMap F n :=
  Functor.ofSequence_map_homOfLE_succ (iterateMap F) n

-- ✓ TIER 1
/-- The chain map at successor indices equals F applied to the chain map.
    This is the key structural property: the (m+1)-to-(n+1) map in the chain
    is F applied to the m-to-n map. -/
theorem initialChain_map_succ_eq {m n : ℕ} (h : m ≤ n) :
    (initialChain F).map (homOfLE (Nat.succ_le_succ h)) =
    F.map ((initialChain F).map (homOfLE h)) := by
  induction h with
  | refl =>
    have h1 : (homOfLE (Nat.succ_le_succ (le_refl m)) : (m+1 : ℕ) ⟶ (m+1 : ℕ)) = 𝟙 _ :=
      Subsingleton.elim _ _
    have h2 : (homOfLE (le_refl m) : (m : ℕ) ⟶ (m : ℕ)) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [h1, h2, Functor.map_id, Functor.map_id, F.map_id]
    rfl
  | @step k h' ih =>
    have decomp_lhs :
        (homOfLE (Nat.succ_le_succ (Nat.le.step h')) : (m+1 : ℕ) ⟶ (k+2 : ℕ)) =
        (homOfLE (Nat.succ_le_succ h') : (m+1 : ℕ) ⟶ (k+1 : ℕ)) ≫
        (homOfLE (Nat.le_add_right (k+1) 1) : (k+1 : ℕ) ⟶ (k+2 : ℕ)) :=
      Subsingleton.elim _ _
    have decomp_rhs :
        (homOfLE (Nat.le.step h') : (m : ℕ) ⟶ (k+1 : ℕ)) =
        (homOfLE h' : (m : ℕ) ⟶ (k : ℕ)) ≫
        (homOfLE (Nat.le_add_right k 1) : (k : ℕ) ⟶ (k+1 : ℕ)) :=
      Subsingleton.elim _ _
    rw [decomp_lhs, Functor.map_comp, ih, decomp_rhs, Functor.map_comp, F.map_comp]
    congr 1
    rw [initialChain_map_succ, initialChain_map_succ]
    rfl

end Functor

end FixedPoint.Iteration
