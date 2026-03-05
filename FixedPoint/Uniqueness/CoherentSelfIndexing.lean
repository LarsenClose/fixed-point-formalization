/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Coherent Self-Indexing Structure.

The bare `SelfIndexedFixedPoint` provides a set-level bijection
`(𝟙_ C ⟶ D) ≃ (D ⟶ D)` but lacks categorical structure: it says nothing
about how the self-indexing interacts with composition or evaluation.

A `CoherentSelfIndexedFixedPoint` enriches this with:
1. An evaluation map `eval : D ⊗ D ⟶ D` making D into a magma object.
2. Naming-eval compatibility (the "apply" law): evaluating a named
   function against an argument recovers the function.
3. Identity coherence: the name of the identity is a right unit for eval.

These conditions bridge `SelfIndexedFixedPoint` (arbitrary F) back to the
`ReflexiveObject` / `SelfIndexedComputation` framework (specific to ihom).
The key point: when F = ihom(D) and D satisfies the reflexive domain
equation D ≅ [D, D], the selfApp morphism provides eval, and the
curryEquiv at X = 𝟙_ C provides the coherent self-indexing.

## What is proved

- `CoherentSelfIndexedFixedPoint` : structure with eval + coherence (Tier 1, 0 sorry)
- `eval_id_from_compat` : eval_id is derivable from eval_compat (Tier 1, 0 sorry)
- `reflexiveEval` : eval map from a reflexive object (Tier 1, 0 sorry)
- `coherentFromReflexive` : bridge from reflexive objects (Tier 1, 0 sorry)

STATUS: Tier 1 definitions + Tier 1 bridge (0 sorry).
-/

import FixedPoint.Uniqueness.SelfIndexedTerminalProperty

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open MonoidalCategory

namespace FixedPoint.Uniqueness

universe v u

/-! ### CoherentSelfIndexedFixedPoint -/

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A coherent self-indexed fixed point enriches `SelfIndexedFixedPoint` with
    an evaluation map and compatibility conditions. The evaluation makes the
    carrier D into a magma object in (C, ⊗, 𝟙), and the self-indexing is
    compatible with evaluation in the sense that "running a named program"
    via eval recovers the named endomorphism.

    **Tensor convention:** `selfApp` (and hence `eval`) decodes the RIGHT
    tensor factor as a function via `φ⁻¹` and evaluates at the LEFT tensor
    factor (the argument). Therefore, the name of a function goes in the
    RIGHT tensor position via whiskerLeft (`◁`).

    **Condition (eval_compat):** For every endomorphism `f : D ⟶ D`, the
    global section `selfIndexing⁻¹(f)` that names `f` satisfies
      `(D ◁ selfIndexing⁻¹(f)) ≫ eval = (ρ_ D).hom ≫ f`
    That is, whiskering the name of `f` into the code slot (right tensor
    factor) and evaluating gives the same result as applying `f` after
    the right unitor.

    **Condition (eval_id):** The name of the identity is a right unit
    for eval: `(D ◁ selfIndexing⁻¹(id)) ≫ eval = (ρ_ D).hom`.
    This is a specialization of eval_compat at `f = id`. -/
structure CoherentSelfIndexedFixedPoint (F : C ⥤ C)
    extends SelfIndexedFixedPoint F where
  /-- The evaluation map: D ⊗ D ⟶ D. -/
  eval : adamek.carrier ⊗ adamek.carrier ⟶ adamek.carrier
  /-- Naming-eval compatibility: evaluating a named function recovers it. -/
  eval_compat : ∀ (f : adamek.carrier ⟶ adamek.carrier),
    (adamek.carrier ◁ selfIndexing.symm f) ≫ eval =
    (ρ_ adamek.carrier).hom ≫ f
  /-- Identity coherence: the name of id is a right unit for eval. -/
  eval_id : (adamek.carrier ◁ selfIndexing.symm (𝟙 adamek.carrier)) ≫ eval =
    (ρ_ adamek.carrier).hom

/-- eval_id follows from eval_compat at f = id. This shows eval_id is
    redundant but included in the structure for convenience. -/
theorem eval_id_from_compat {F : C ⥤ C}
    (sif : SelfIndexedFixedPoint F)
    (ev : sif.adamek.carrier ⊗ sif.adamek.carrier ⟶ sif.adamek.carrier)
    (h : ∀ (f : sif.adamek.carrier ⟶ sif.adamek.carrier),
      (sif.adamek.carrier ◁ sif.selfIndexing.symm f) ≫ ev =
      (ρ_ sif.adamek.carrier).hom ≫ f) :
    (sif.adamek.carrier ◁ sif.selfIndexing.symm (𝟙 sif.adamek.carrier)) ≫ ev =
    (ρ_ sif.adamek.carrier).hom := by
  rw [h, Category.comp_id]

/-! ### Construction from a reflexive object with A = D

When the reflexive object has parameter A equal to its carrier D
(the reflexive domain equation D ≅ [D, D]), the selfApp morphism
provides a coherent evaluation map. -/

section FromReflexive

variable [FixedPoint.SubstrateCategory C] [HasInitial C]

/-- Build the evaluation map from a reflexive object: compose the carrier
    isomorphism with selfApp.

    Given `hrefl : fp.carrier ≅ D`, the eval map is:
      fp.carrier ⊗ fp.carrier --(hrefl.hom ▷ carrier)--> D ⊗ fp.carrier --selfApp--> fp.carrier

    selfApp decodes the RIGHT tensor factor via φ⁻¹ and evaluates at the
    LEFT factor (which serves as the argument after mapping through hrefl). -/
noncomputable def reflexiveEval
    {D : C} [Closed D]
    (fp : FixedPointSpec D) (hrefl : fp.carrier ≅ D) :
    fp.carrier ⊗ fp.carrier ⟶ fp.carrier :=
  let r := Reflexive.ReflexiveObject.fromSpec fp
  (hrefl.hom ▷ fp.carrier) ≫ r.selfApp

/-- A reflexive object with A = carrier provides a coherent self-indexed
    fixed point for ihom(A).

    The eval map is selfApp composed with the carrier iso. The eval_compat
    condition holds because the name goes in the RIGHT tensor factor (code
    slot), which is decoded by φ⁻¹. The round-trip `φ.hom ≫ φ⁻¹ = id`
    cancels, and `uncurry(curry(h)) = h` recovers the original morphism.

    The proof uses: `whiskerLeft_comp`, `whisker_exchange` (twice),
    `Iso.hom_inv_id`, `whiskerLeft_curry_ihom_ev_app`, and
    `rightUnitor_naturality`. -/
noncomputable def coherentFromReflexive
    (D : C) [Closed D]
    (fp : FixedPointSpec D) (hrefl : fp.carrier ≅ D) :
    CoherentSelfIndexedFixedPoint (ihom D) where
  toSelfIndexedFixedPoint := ihom_selfIndexedFixedPoint D fp hrefl
  eval := reflexiveEval fp hrefl
  eval_compat := by
    intro f
    change (fp.carrier ◁ (MonoidalClosed.curry ((ρ_ D).hom ≫ hrefl.inv ≫ f) ≫
      fp.fixedPointIso.hom)) ≫ (hrefl.hom ▷ fp.carrier ≫ D ◁ fp.fixedPointIso.inv ≫
      (ihom.ev D).app fp.carrier) = (ρ_ fp.carrier).hom ≫ f
    -- Expand L ◁ (curry(h) ≫ φ.hom) and right-associate
    rw [whiskerLeft_comp]
    simp only [Category.assoc]
    -- Exchange L ◁ φ.hom ≫ hrefl.hom ▷ L → hrefl.hom ▷ [D,L] ≫ D ◁ φ.hom
    rw [whisker_exchange_assoc]
    -- Cancel D ◁ φ.hom ≫ D ◁ φ.inv → D ◁ (φ.hom ≫ φ.inv) → D ◁ id → id
    rw [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
    -- Exchange L ◁ curry(h) ≫ hrefl.hom ▷ [D, L]
    rw [whisker_exchange_assoc]
    -- D ◁ curry(h) ≫ ev = h (whiskerLeft_curry_ihom_ev_app)
    erw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    -- hrefl.hom ▷ (𝟙_ C) ≫ (ρ_ D).hom = (ρ_ L).hom ≫ hrefl.hom (naturality)
    rw [← Category.assoc, rightUnitor_naturality]
    -- Cancel hrefl.hom ≫ hrefl.inv = id
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  eval_id := by
    change (fp.carrier ◁ (MonoidalClosed.curry ((ρ_ D).hom ≫ hrefl.inv ≫ 𝟙 fp.carrier) ≫
      fp.fixedPointIso.hom)) ≫ (hrefl.hom ▷ fp.carrier ≫ D ◁ fp.fixedPointIso.inv ≫
      (ihom.ev D).app fp.carrier) = (ρ_ fp.carrier).hom
    rw [whiskerLeft_comp]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc]
    rw [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
    rw [whisker_exchange_assoc]
    erw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    rw [← Category.assoc, rightUnitor_naturality]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FromReflexive

end FixedPoint.Uniqueness
