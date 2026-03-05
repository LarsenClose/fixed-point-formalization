/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Initial-algebra induction and recursion principles.

The Adamek initial algebra theorem provides a fixed point D = colim F^n(bot).
This file names and packages the two elimination principles that come with it:

  - `adamek_induction`: to prove a property of D, it suffices to show the
    property is closed under the algebra operation (i.e., the target carries
    an F-algebra structure). The unique catamorphism witnesses the proof.

  - `adamek_rec`: to construct a morphism out of D, it suffices to give a
    compatible family of morphisms out of each F^n(bot). This is the colimit
    universal property, named as structural recursion over the chain.

STATUS: Tier 1 (0 sorry)
-/

import FixedPoint.Iteration.AdamekTheorem

open CategoryTheory CategoryTheory.Limits

namespace FixedPoint.Iteration

universe v u

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ C) [HasInitial C]

section Induction

variable {c : Cocone (initialChain F)} (hc : IsColimit c)
variable [PreservesColimit (initialChain F) F]

/-- **Initial-algebra induction.** To define a morphism out of the Adamek fixed
    point D, it suffices to give an F-algebra structure on the target. The unique
    algebra homomorphism (catamorphism) is the result, and it factors through the
    chain: at each level n, the catamorphism restricted to F^n(bot) equals the
    level-wise algebra cocone map `algebraCoconeApp F B n`.

    This is the elimination principle for the initial algebra: any property that
    is closed under the algebra operation (expressed as an F-algebra on the
    "witness" object) holds at the fixed point. -/
theorem adamek_induction (B : Endofunctor.Algebra F) (n : ℕ) :
    c.ι.app n ≫ (adamekAlgebraHom F hc B).f = algebraCoconeApp F B n :=
  hc.fac (algebraCocone F B) n

/-- **Initial-algebra induction, uniqueness.** The catamorphism is the only
    algebra homomorphism from the initial algebra to any target. -/
theorem adamek_induction_unique (B : Endofunctor.Algebra F)
    (g : adamekAlgebra F _ hc ⟶ B) :
    g = adamekAlgebraHom F hc B :=
  adamekAlgebraHom_unique F hc B g

end Induction

section Recursion

variable {c : Cocone (initialChain F)} (hc : IsColimit c)

/-- **Recursion on the initial chain.** To construct a morphism out of the
    colimit D = colim F^n(bot), it suffices to give a compatible cocone over
    the initial chain with the desired target. That is:

    - For each n, a morphism `f n : F^n(bot) -> X`
    - Compatibility: for each n, `iterateMap F n >> f (n+1) = f n`

    The result is the unique morphism `D -> X` whose restriction to each
    chain level equals the given family.

    This is the colimit universal property, named as structural recursion
    to emphasize its role as the recursion principle dual to induction. -/
noncomputable def adamek_rec {X : C}
    (f : (n : ℕ) → iterateObj F n ⟶ X)
    (hf : ∀ n, iterateMap F n ≫ f (n + 1) = f n) :
    c.pt ⟶ X :=
  hc.desc
    { pt := X
      ι :=
      { app := f
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
            rw [Functor.map_comp, Category.assoc, initialChain_map_succ, hf k,
              ih (homOfLE hle')] } }

/-- The recursion morphism restricts to the given family at each chain level. -/
theorem adamek_rec_fac {X : C}
    (f : (n : ℕ) → iterateObj F n ⟶ X)
    (hf : ∀ n, iterateMap F n ≫ f (n + 1) = f n) (n : ℕ) :
    c.ι.app n ≫ adamek_rec F hc f hf = f n :=
  hc.fac _ n

/-- The recursion morphism is unique: any morphism out of D that restricts
    correctly at each chain level must equal the one produced by `adamek_rec`. -/
theorem adamek_rec_unique {X : C}
    (f : (n : ℕ) → iterateObj F n ⟶ X)
    (hf : ∀ n, iterateMap F n ≫ f (n + 1) = f n)
    (g : c.pt ⟶ X) (hg : ∀ n, c.ι.app n ≫ g = f n) :
    g = adamek_rec F hc f hf :=
  hc.uniq ⟨X, { app := f, naturality := _ }⟩ g hg

end Recursion

end FixedPoint.Iteration
