/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Adamek's Initial Algebra Theorem.

Given an endofunctor F : C ⥤ C on a category with an initial object,
if the initial chain ⊥ → F(⊥) → F²(⊥) → ⋯ has a colimit L and F
preserves this colimit, then L carries the structure of an initial
F-algebra. The algebra structure map F(L) → L is an isomorphism
(Lambek's lemma applied to the initial algebra).

Key definitions:
  - `adamekAlgebra`          : the F-algebra on the colimit L
  - `adamekAlgebraHom`       : the unique algebra homomorphism to any other algebra

Main results:
  - `adamekIsInitial`        : the Adamek algebra is initial in Algebra F
-/

import FixedPoint.Iteration.ChainShift
import Mathlib.CategoryTheory.Endofunctor.Algebra

open CategoryTheory CategoryTheory.Limits

namespace FixedPoint.Iteration

universe v u

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ C) [HasInitial C]

/-! ### Algebra structure on the colimit -/

section AlgebraConstruction

variable {c : Cocone (initialChain F)} (hc : IsColimit c)
variable [PreservesColimit (initialChain F) F]

/-- The colimit of F applied to the initial chain is a colimit (by preservation). -/
noncomputable def preservedColimit :
    IsColimit (F.mapCocone c) :=
  isColimitOfPreserves F hc

/-- The algebra structure map F(L) → L for the Adamek algebra. -/
noncomputable def adamekStr : F.obj c.pt ⟶ c.pt :=
  (preservedColimit F hc).desc (shiftCocone F c)

/-- The structure map commutes with the colimit inclusions:
    F.map (ι_n) ≫ adamekStr = ι_{n+1}. -/
theorem adamekStr_fac (n : ℕ) :
    F.map (c.ι.app n) ≫ adamekStr F hc = c.ι.app (n + 1) :=
  (preservedColimit F hc).fac (shiftCocone F c) n

end AlgebraConstruction

section AlgebraDefinition

variable (c : Cocone (initialChain F)) (hc : IsColimit c)
variable [PreservesColimit (initialChain F) F]

/-- The Adamek algebra: the colimit of the initial chain, equipped with the
    algebra structure map F(L) → L obtained from the preserved colimit. -/
noncomputable def adamekAlgebra : Endofunctor.Algebra F where
  a := c.pt
  str := adamekStr F hc

@[simp]
theorem adamekAlgebra_a : (adamekAlgebra F c hc).a = c.pt := rfl

@[simp]
theorem adamekAlgebra_str : (adamekAlgebra F c hc).str = adamekStr F hc := rfl

end AlgebraDefinition

/-! ### Algebra cocone and initiality -/

section AlgebraCoconeApp

variable (F : C ⥤ C) [HasInitial C]

/-- The n-th leg of the algebra cocone: the unique map F^n(⊥) → B.a. -/
noncomputable def algebraCoconeApp (B : Endofunctor.Algebra F) :
    (n : ℕ) → iterateObj F n ⟶ B.a
  | 0 => initial.to B.a
  | n + 1 => F.map (algebraCoconeApp B n) ≫ B.str

@[simp]
theorem algebraCoconeApp_zero (B : Endofunctor.Algebra F) :
    algebraCoconeApp F B 0 = initial.to B.a := rfl

@[simp]
theorem algebraCoconeApp_succ (B : Endofunctor.Algebra F) (n : ℕ) :
    algebraCoconeApp F B (n + 1) =
    F.map (algebraCoconeApp F B n) ≫ B.str := rfl

/-- The successor map of the chain composes with the next algebra cocone leg
    to give the current one: iterateMap k ≫ f_{k+1} = f_k. -/
theorem iterateMap_comp_algebraCoconeApp (B : Endofunctor.Algebra F) (k : ℕ) :
    iterateMap F k ≫ algebraCoconeApp F B (k + 1) = algebraCoconeApp F B k := by
  induction k with
  | zero => exact initial.hom_ext _ _
  | succ k ih =>
    -- Goal: F.map(iterateMap k) ≫ (F.map(f_{k+1}) ≫ B.str) = F.map(f_k) ≫ B.str
    show F.map (iterateMap F k) ≫ (F.map (algebraCoconeApp F B (k + 1)) ≫ B.str) =
      F.map (algebraCoconeApp F B k) ≫ B.str
    rw [← Category.assoc, ← F.map_comp, ih]

end AlgebraCoconeApp

section Initiality

variable {c : Cocone (initialChain F)} (hc : IsColimit c)
variable [PreservesColimit (initialChain F) F]

/-- Given an F-algebra (B, β), define the cocone over the initial chain with point B. -/
noncomputable def algebraCocone (B : Endofunctor.Algebra F) :
    Cocone (initialChain F) where
  pt := B.a
  ι :=
  { app := fun n => algebraCoconeApp F B n
    naturality := by
      intro m n α
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      have hle := leOfHom α
      rw [show (initialChain F).map α = (initialChain F).map (homOfLE hle) from
        congr_arg _ (Subsingleton.elim _ _)]
      induction hle with
      | refl =>
        rw [show (homOfLE (le_refl m) : (m : ℕ) ⟶ m) = 𝟙 _ from Subsingleton.elim _ _]
        rw [Functor.map_id, Category.id_comp]
      | @step k hle' ih =>
        rw [show (homOfLE (Nat.le.step hle') : (m : ℕ) ⟶ (k + 1)) =
          (homOfLE hle' : (m : ℕ) ⟶ k) ≫
          (homOfLE (Nat.le_add_right k 1) : (k : ℕ) ⟶ (k + 1)) from
          Subsingleton.elim _ _]
        rw [Functor.map_comp, Category.assoc,
          initialChain_map_succ F k,
          iterateMap_comp_algebraCoconeApp F B k,
          ih (homOfLE hle')] }

theorem algebraCocone_app (B : Endofunctor.Algebra F) (n : ℕ) :
    (algebraCocone F B).ι.app n = algebraCoconeApp F B n := rfl

/-- The unique algebra homomorphism from the Adamek algebra to any other algebra. -/
noncomputable def adamekAlgebraHom (B : Endofunctor.Algebra F) :
    adamekAlgebra F _ hc ⟶ B where
  f := hc.desc (algebraCocone F B)
  h := by
    apply (preservedColimit F hc).hom_ext
    intro n
    simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app]
    -- Both sides equal (algebraCocone F B).ι.app (n + 1)
    trans (algebraCocone F B).ι.app (n + 1)
    · -- LHS: F.map(ι_n) ≫ (F.map(desc) ≫ B.str) = f_{n+1}
      rw [← Category.assoc, ← F.map_comp, hc.fac (algebraCocone F B) n,
        algebraCocone_app, algebraCocone_app]; rfl
    · -- RHS: F.map(ι_n) ≫ (adamekStr ≫ desc) = f_{n+1}
      symm
      simp only [adamekAlgebra_str]
      rw [← Category.assoc, adamekStr_fac F hc n, hc.fac (algebraCocone F B) (n + 1)]

/-- Any algebra homomorphism from the Adamek algebra equals the canonical one. -/
theorem adamekAlgebraHom_unique (B : Endofunctor.Algebra F)
    (g : adamekAlgebra F _ hc ⟶ B) :
    g = adamekAlgebraHom F hc B := by
  ext
  apply hc.uniq (algebraCocone F B)
  intro n
  induction n with
  | zero => exact initial.hom_ext _ _
  | succ n ih =>
    rw [show c.ι.app (n + 1) = F.map (c.ι.app n) ≫ adamekStr F hc from
      (adamekStr_fac F hc n).symm]
    rw [Category.assoc,
      show adamekStr F hc ≫ g.f = F.map g.f ≫ B.str from g.h.symm,
      ← Category.assoc, ← F.map_comp, ih,
      algebraCocone_app, algebraCocone_app]; rfl

/-- Adamek's Initial Algebra Theorem: the colimit of the initial chain,
    equipped with the algebra structure from the preserved colimit,
    is an initial object in the category of F-algebras. -/
noncomputable def adamekIsInitial :
    IsInitial (adamekAlgebra F _ hc) :=
  IsInitial.ofUniqueHom
    (fun B => adamekAlgebraHom F hc B)
    (fun B g => adamekAlgebraHom_unique F hc B g)

end Initiality

end FixedPoint.Iteration
