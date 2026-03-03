/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

The shifted chain has the same colimit as the initial chain.

Given a cocone over the initial chain ⊥ → F(⊥) → F²(⊥) → ⋯ with colimit L,
we construct a cocone over the "shifted" chain F(⊥) → F²(⊥) → F³(⊥) → ⋯
(equivalently, the composite functor initialChain F ⋙ F) with the same point L.

The key result is that applying F to the colimit cocone yields a colimit for the
shifted chain, and the colimit of the shifted chain agrees with the colimit of the
original chain. This is the foundation for constructing the Adamek algebra.
-/

import FixedPoint.Iteration.InitialChain
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic

open CategoryTheory CategoryTheory.Limits

namespace FixedPoint.Iteration

universe v u

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ C) [HasInitial C]

/-- Given a cocone over the initial chain with point L, construct a cocone
    over `initialChain F ⋙ F` (the shifted chain) with the same point L.
    The legs are the original cocone legs shifted by one: ι_{n+1} for each n. -/
noncomputable def shiftCocone (c : Cocone (initialChain F)) :
    Cocone (initialChain F ⋙ F) where
  pt := c.pt
  ι :=
  { app := fun n => c.ι.app (n + 1)
    naturality := by
      intro m n α
      simp only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
        Functor.const_obj_map, Category.comp_id]
      -- Goal: F.map ((initialChain F).map α) ≫ c.ι.app (n+1) = c.ι.app (m+1)
      -- Convert α to homOfLE form, apply initialChain_map_succ_eq in reverse,
      -- then use the cocone condition c.w.
      have hle := leOfHom α
      rw [show (initialChain F).map α = (initialChain F).map (homOfLE hle) from
        congr_arg _ (Subsingleton.elim _ _)]
      rw [← initialChain_map_succ_eq F hle]
      exact c.w (homOfLE (Nat.succ_le_succ hle)) }

-- ✓ TIER 1
@[simp]
theorem shiftCocone_ι_app (c : Cocone (initialChain F)) (n : ℕ) :
    (shiftCocone F c).ι.app n = c.ι.app (n + 1) := rfl

/-- Extend a cocone over the shifted chain to one over the full initial chain,
    by adding initial.to as the zeroth leg. -/
noncomputable def extendCocone (s : Cocone (initialChain F ⋙ F)) :
    Cocone (initialChain F) where
  pt := s.pt
  ι :=
  { app := fun n =>
      match n with
      | 0 => initial.to s.pt
      | n + 1 => s.ι.app n
    naturality := by
      intro m n α
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      -- All maps from ⊥ are equal by initiality
      match m, n with
      | 0, 0 =>
        rw [show α = 𝟙 _ from Subsingleton.elim _ _, Functor.map_id, Category.id_comp]
      | 0, (n + 1) =>
        exact initial.hom_ext _ _
      | (m + 1), (n + 1) =>
        -- Need: chain.map α ≫ s.ι.app n = s.ι.app m
        -- chain.map α at (m+1, n+1) = F.map (chain.map α') for α' : m → n
        have hle := Nat.le_of_succ_le_succ (leOfHom α)
        rw [show (initialChain F).map α =
          (initialChain F).map (homOfLE (Nat.succ_le_succ hle)) from
          congr_arg _ (Subsingleton.elim _ _)]
        rw [initialChain_map_succ_eq F hle]
        -- Now: F.map (chain.map (homOfLE hle)) ≫ s.ι.app n = s.ι.app m
        -- This is the cocone condition for s
        have := s.w (homOfLE hle)
        simp only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj] at this
        exact this }

/-- If `c` is a colimit cocone for the initial chain, then `shiftCocone F c` is a
    colimit cocone for `initialChain F ⋙ F`. -/
noncomputable def shiftCoconeIsColimit (c : Cocone (initialChain F))
    (hc : IsColimit c) : IsColimit (shiftCocone F c) where
  desc s := hc.desc (extendCocone F s)
  fac s n := by
    simp only [shiftCocone_ι_app]
    exact hc.fac (extendCocone F s) (n + 1)
  uniq s g hg := by
    apply hc.uniq (extendCocone F s)
    intro n
    match n with
    | 0 => exact initial.hom_ext _ _
    | n + 1 => exact hg n

end FixedPoint.Iteration
