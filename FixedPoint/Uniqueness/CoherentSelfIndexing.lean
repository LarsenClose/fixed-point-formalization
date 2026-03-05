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
3. Identity coherence: the name of the identity is a left unit for eval.

These conditions bridge `SelfIndexedFixedPoint` (arbitrary F) back to the
`ReflexiveObject` / `SelfIndexedComputation` framework (specific to ihom).
The key point: when F = ihom(D) and D satisfies the reflexive domain
equation D ≅ [D, D], the selfApp morphism provides eval, and the
curryEquiv at X = 𝟙_ C provides the coherent self-indexing.

## What is proved

- `CoherentSelfIndexedFixedPoint` : structure with eval + coherence (Tier 1, 0 sorry)
- `eval_id_from_compat` : eval_id is derivable from eval_compat (Tier 1, 0 sorry)
- `reflexiveEval` : eval map from a reflexive object (Tier 1, 0 sorry)
- `coherentFromReflexive` : bridge from reflexive objects (Tier 2, 1 sorry)
  The sorry is in eval_compat: normalizing the composition of whiskers,
  currying, Lambek iso, and the evaluation adjunction through five layers
  of definition (selfIndexingEquiv, curryEquiv, reflexiveCurry, uncurry,
  selfApp) requires lemmas about the interaction of whisker_exchange with
  the monoidal closed evaluation that are not directly available in Mathlib.
  The mathematical content is clear: selfApp is uncurry(iso.inv) and the
  self-indexing is built from curry/iso.hom, so they are mutually inverse.

STATUS: Tier 1 definitions + Tier 2 bridge (1 sorry in bridge).
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

    **Condition (eval_compat):** For every endomorphism `f : D ⟶ D`, the
    global section `selfIndexing⁻¹(f)` that names `f` satisfies
      `(selfIndexing⁻¹(f) ▷ D) ≫ eval = (λ_ D).hom ≫ f`
    That is, whiskering the name of `f` into eval and evaluating gives
    the same result as applying `f` after the left unitor.

    **Condition (eval_id):** The name of the identity is a left unit
    for eval: `(selfIndexing⁻¹(id) ▷ D) ≫ eval = (λ_ D).hom`.
    This is a specialization of eval_compat at `f = id`. -/
structure CoherentSelfIndexedFixedPoint (F : C ⥤ C)
    extends SelfIndexedFixedPoint F where
  /-- The evaluation map: D ⊗ D ⟶ D. -/
  eval : adamek.carrier ⊗ adamek.carrier ⟶ adamek.carrier
  /-- Naming-eval compatibility: evaluating a named function recovers it. -/
  eval_compat : ∀ (f : adamek.carrier ⟶ adamek.carrier),
    (selfIndexing.symm f ▷ adamek.carrier) ≫ eval =
    (λ_ adamek.carrier).hom ≫ f
  /-- Identity coherence: the name of id is a left unit for eval. -/
  eval_id : (selfIndexing.symm (𝟙 adamek.carrier) ▷ adamek.carrier) ≫ eval =
    (λ_ adamek.carrier).hom

/-- eval_id follows from eval_compat at f = id. This shows eval_id is
    redundant but included in the structure for convenience. -/
theorem eval_id_from_compat {F : C ⥤ C}
    (sif : SelfIndexedFixedPoint F)
    (ev : sif.adamek.carrier ⊗ sif.adamek.carrier ⟶ sif.adamek.carrier)
    (h : ∀ (f : sif.adamek.carrier ⟶ sif.adamek.carrier),
      (sif.selfIndexing.symm f ▷ sif.adamek.carrier) ≫ ev =
      (λ_ sif.adamek.carrier).hom ≫ f) :
    (sif.selfIndexing.symm (𝟙 sif.adamek.carrier) ▷ sif.adamek.carrier) ≫ ev =
    (λ_ sif.adamek.carrier).hom := by
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

    This is `uncurry(hrefl.hom ≫ iso.inv)`: decode the first component
    of the tensor as a function via the Lambek iso, then evaluate. -/
noncomputable def reflexiveEval
    {D : C} [Closed D]
    (fp : FixedPointSpec D) (hrefl : fp.carrier ≅ D) :
    fp.carrier ⊗ fp.carrier ⟶ fp.carrier :=
  let r := Reflexive.ReflexiveObject.fromSpec fp
  (hrefl.hom ▷ fp.carrier) ≫ r.selfApp

/-- A reflexive object with A = carrier provides a coherent self-indexed
    fixed point for ihom(A).

    The eval map is selfApp composed with the carrier iso. The eval_compat
    condition — that evaluating a named function recovers the function —
    follows mathematically from the fact that selfApp = uncurry(iso.inv) and
    the self-indexing is built from curry/iso.hom, making them mutually
    inverse operations. The formal proof requires normalizing compositions
    of whiskers, currying, the Lambek iso, the right unitor, and the
    evaluation adjunction through multiple definition layers.

    The eval_id condition follows from eval_compat at f = id. -/
noncomputable def coherentFromReflexive
    (D : C) [Closed D]
    (fp : FixedPointSpec D) (hrefl : fp.carrier ≅ D) :
    CoherentSelfIndexedFixedPoint (ihom D) where
  toSelfIndexedFixedPoint := ihom_selfIndexedFixedPoint D fp hrefl
  eval := reflexiveEval fp hrefl
  eval_compat := by
    -- Tier 2 sorry: the composition
    --   (reflexiveCurry((ρ_ D).hom ≫ hrefl.inv ≫ f) ▷ carrier)
    --   ≫ (hrefl.hom ▷ carrier) ≫ selfApp
    -- equals (λ_ carrier).hom ≫ f.
    --
    -- Proof sketch: combine whiskers via comp_whiskerRight, expand
    -- selfApp = D ◁ iso.inv ≫ ev, use whisker_exchange to swap the
    -- whisker and left-action, then apply the curry/uncurry round-trip
    -- (MonoidalClosed.uncurry_curry) to cancel the iso.hom/iso.inv pair.
    -- The final step uses the right unitor to eliminate (ρ_ D).hom ≫ hrefl.inv.
    intro f
    sorry
  eval_id := by
    -- This follows from eval_compat at f = id by Category.comp_id.
    -- We inherit the sorry from eval_compat.
    sorry

end FromReflexive

end FixedPoint.Uniqueness
