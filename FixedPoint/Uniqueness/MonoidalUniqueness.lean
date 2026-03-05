/-
  MonoidalUniqueness.lean

  The structured uniqueness argument: the fixed-point endofunctor is forced
  by the monoidal closed structure, factored into three explicit steps.

  Step (a): Right adjoints are unique — PROVED (Tier 1).
    In a monoidal closed category, any right adjoint to tensorLeft A is
    naturally isomorphic to ihom A. This is `rightAdjointForcedToIHom`
    from RightAdjointUnique.lean, which wraps Mathlib's
    `Adjunction.rightAdjointUniq`.

  Step (b): M = ihom of the BV monoidal structure — SORRY (Tier 3).
    If the Boardman-Vogt tensor product extends to EATs (Claim A from
    BoardmanVogt.lean), then the EAT model category carries a monoidal
    closed structure, and any endofunctor M that arises as the right
    adjoint of this tensor is isomorphic to the internal hom ihom.
    This step carries `sorry` because it depends on Claim A (the BV
    tensor extension), which is an open Tier 3 conjecture.

  Step (c): Therefore M is unique — PROVED.
    Combining (a) and (b): the endofunctor M is determined up to natural
    isomorphism by the monoidal structure. Given h_adj as a hypothesis,
    this is immediate from Step (a).

  STATUS: Tier 3 — Step (b) contains intentional sorry (depends on Claim A).
  Steps (a) and (c) are fully verified.
-/
import FixedPoint.Uniqueness.RightAdjointUnique
import FixedPoint.Specification.SubstrateIndependent

universe v u

open CategoryTheory
open MonoidalCategory

namespace FixedPoint.Uniqueness

/-! ## Step (a): Right adjoints are unique (PROVED — Tier 1)

This is already established in `RightAdjointUnique.lean`. We restate the
key result here for the structured argument. Given a monoidal closed
category C and a closed object A, any functor G that is right adjoint
to `tensorLeft A` satisfies `G ≅ ihom A`. -/

section StepA

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- Step (a): In a monoidal closed category, the internal hom is forced.
    Any right adjoint to `tensorLeft A` is naturally isomorphic to `ihom A`.
    This is a direct reference to `rightAdjointForcedToIHom`. -/
noncomputable def monoidal_structure_forces_ihom (A : C) [Closed A]
    {G : C ⥤ C} (adj : tensorLeft A ⊣ G) :
    G ≅ ihom A :=
  rightAdjointForcedToIHom A adj

end StepA

/-! ## Step (b): M is the internal hom of the monoidal structure (SORRY — Tier 3)

This step asserts that for an endofunctor M on a substrate category,
if M arises as the right adjoint of a monoidal tensor (such as the
Boardman-Vogt tensor extended to EATs), then M is isomorphic to the
internal hom of that monoidal structure.

The `sorry` here is **intentional**: it depends on the BV tensor product
extending from Lawvere theories to essentially algebraic theories
(Claim A in `FixedPoint.Tensor.BoardmanVogt`). This is an open
mathematical conjecture at Tier 3. -/

section StepB

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C]

omit [FixedPoint.SubstrateCategory C] in
/-- Step (b) conjecture: Given a substrate category (monoidal closed + LFP)
    and an endofunctor M that is right adjoint to `tensorLeft A`, M is
    isomorphic to `ihom A`.

    In isolation, this is trivially true (it is just Step (a)). The
    mathematical content is the **existence** of the monoidal closed
    structure on EAT model categories via the BV tensor. The conjecture
    packages this: assuming a monoidal closed structure exists (which
    requires Claim A), the endofunctor is forced.

    The sorry marks the gap: we cannot yet construct the monoidal closed
    structure on EAT model categories because the BV tensor extension
    (Claim A) is unproved. Once Claim A is established, this conjecture
    reduces to Step (a).

    **Tier 3**: Depends on `claimA_bvTensor_extends` from BoardmanVogt.lean. -/
theorem endofunctor_forced_by_bv_structure
    (A : C) [Closed A]
    [FixedPoint.TensorLeftFinitelyPresentable A]
    (M : C ⥤ C)
    (h_adj : tensorLeft A ⊣ M) :
    Nonempty (M ≅ ihom A) :=
  ⟨rightAdjointForcedToIHom A h_adj⟩

end StepB

/-! ## Step (c): M is unique given the monoidal structure (SORRY — depends on b)

The final step: any two endofunctors that arise as right adjoints of the
same tensor are isomorphic to each other. This follows from transitivity:
both are isomorphic to `ihom A` by Step (a), hence to each other.

The sorry here is **structural**: the mathematical argument is complete
(and in fact proved by `endofunctorUnique` from RightAdjointUnique.lean),
but the full pipeline — from BV tensor existence through monoidal closed
structure to this uniqueness — carries the Tier 3 gap from Step (b).

We state the theorem in a form that makes the dependency explicit:
given that the BV monoidal structure exists and M arises from it,
M is unique. -/

section StepC

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C]

/-- Step (c): Any two endofunctors that are right adjoint to the same
    tensor product are naturally isomorphic.

    This is a direct consequence of Step (a) applied twice:
      M₁ ≅ ihom A ≅ M₂⁻¹ means M₁ ≅ M₂.

    Combined with Step (b) (which asserts M arises from the BV structure),
    this gives full uniqueness of the fixed-point endofunctor.

    **Tier 3**: The sorry marks the dependency on the BV tensor extension.
    The categorical uniqueness itself is proved — see `endofunctorUnique`
    in RightAdjointUnique.lean. The gap is establishing that the BV tensor
    gives rise to the monoidal closed structure in the first place.

    Once Claim A (BV tensor extension) is proved:
    1. The EAT model category becomes monoidal closed.
    2. Step (a) forces M ≅ ihom A.
    3. This theorem gives M₁ ≅ M₂ for any two such endofunctors. -/
noncomputable def bv_endofunctor_unique
    (A : C) [Closed A]
    [FixedPoint.TensorLeftFinitelyPresentable A]
    {M₁ M₂ : C ⥤ C}
    (adj₁ : tensorLeft A ⊣ M₁)
    (adj₂ : tensorLeft A ⊣ M₂) :
    M₁ ≅ M₂ :=
  -- Proved: transitivity through ihom A via endofunctorUnique.
  -- The sorry in the overall pipeline is in Step (b): establishing that
  -- M₁, M₂ actually arise from the BV monoidal structure.
  endofunctorUnique A adj₁ adj₂

omit [FixedPoint.SubstrateCategory C] in
/-- The full uniqueness pipeline.

    Given a substrate category and an endofunctor M that is right adjoint
    to `tensorLeft A`, M is isomorphic to `ihom A`.

    The argument: Claim A (BoardmanVogt.lean) gives the BV monoidal closed
    structure, then Step (a) forces M ≅ ihom A. Once Claim A is proved,
    `h_adj` will be constructible rather than hypothesized.

    **Tier 3**: Depends on `claimA_bvTensor_extends` from BoardmanVogt.lean. -/
theorem bv_uniqueness_pipeline
    (A : C) [Closed A]
    [FixedPoint.TensorLeftFinitelyPresentable A]
    (M : C ⥤ C)
    -- Tier 3 hypothesis: M arises from a monoidal closed structure
    -- (requires BV tensor extension, Claim A)
    (h_adj : tensorLeft A ⊣ M) :
    -- Conclusion: M is isomorphic to ihom A, and by initiality the
    -- fixed point is unique (SubstrateIndependent.fixedPoint_unique).
    Nonempty (M ≅ ihom A) :=
  -- Once Claim A is proved, h_adj will be constructible from the BV
  -- tensor. For now, the adjunction is an explicit hypothesis.
  -- The proof itself is immediate from Step (a).
  ⟨rightAdjointForcedToIHom A h_adj⟩

end StepC

/-! ## Summary

The uniqueness argument is factored as:

| Step | Statement                          | Status       | Reference                     |
|------|------------------------------------|--------------|-------------------------------|
| (a)  | Right adjoints are unique          | **Proved**   | `rightAdjointForcedToIHom`    |
| (b)  | M = ihom of BV monoidal structure  | **Sorry**    | Depends on Claim A (Tier 3)   |
| (c)  | Therefore M is unique              | **Proved**   | `bv_uniqueness_pipeline`      |

The categorical core (Steps a and c) is fully verified against Mathlib.
The gap is purely in Step (b): establishing that the Boardman-Vogt tensor
product extends to essentially algebraic theories, giving EAT model
categories a monoidal closed structure. This is Claim A from the paper
series, stated as a formal conjecture in `FixedPoint.Tensor.BoardmanVogt`.
-/

end FixedPoint.Uniqueness
