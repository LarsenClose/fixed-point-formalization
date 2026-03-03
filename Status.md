# Verification Status

Lean 4 v4.28.0 / Mathlib v4.28.0

## Tier 1 — Fully Verified (no sorry)

| Theorem | File | Source |
|---------|------|--------|
| `FixedPointSpec.strIso` (Lambek's lemma) | `Specification/SubstrateIndependent.lean` | Mathlib `Algebra.Initial.str_isIso` |
| `fixedPoint_unique` | `Specification/SubstrateIndependent.lean` | Mathlib `IsInitial.uniqueUpToIso` |
| `closedAdjunction` | `Uniqueness/RightAdjointUnique.lean` | Mathlib `ihom.adjunction` |
| `rightAdjointForcedToIHom` | `Uniqueness/RightAdjointUnique.lean` | Mathlib `Adjunction.rightAdjointUniq` |
| `endofunctorUnique` | `Uniqueness/RightAdjointUnique.lean` | Mathlib `Adjunction.rightAdjointUniq` |
| `unit_coherence` | `Uniqueness/RightAdjointUnique.lean` | Mathlib `unit_rightAdjointUniq_hom` |
| `card_self_hom_gt` | `Iteration/FinSetDivergence.lean` | Direct proof |
| `card_hom_gt` | `Iteration/FinSetDivergence.lean` | Direct proof |
| `no_finite_fixed_point` | `Iteration/FinSetDivergence.lean` | Direct proof |
| `adamekSuccStruct` | `Iteration/AdamekChain.lean` | Mathlib `SuccStruct.ofNatTrans` |
| `adamekIterationFunctor` | `Iteration/AdamekChain.lean` | Mathlib transfinite iteration |
| `adamekColimit` | `Iteration/AdamekChain.lean` | Mathlib `SuccStruct.iteration` |
| `adamekBaseIso` | `Iteration/AdamekChain.lean` | Mathlib `iterationFunctorObjBotIso` |
| `equiv_refl` | `ChurchTuring/CharacterizationTheorem.lean` | Direct proof |
| `equiv_symm` | `ChurchTuring/CharacterizationTheorem.lean` | Direct proof |

## Tier 2 — Partially Verified (sorry on key claims)

| Claim | File | Blocker |
|-------|------|---------|
| `fixedPoint_exists` | `Specification/SubstrateIndependent.lean` | Needs Adamek theorem connection |
| `iterationFromInitial` | `Specification/SubstrateIndependent.lean` | Specialization of existence |
| `adamekColimit_isInitialAlgebra` | `Iteration/AdamekChain.lean` | Core Adamek theorem (not in Mathlib) |

## Tier 3 — Formal Conjectures (stated with sorry)

| Claim | File | Notes |
|-------|------|-------|
| Claim A (BV tensor extends to EAT) | `Tensor/BoardmanVogt.lean` | Partial-operation domain compatibility |
| Claim A' (Lawvere-Linton extends to EAT) | `Tensor/BoardmanVogt.lean` | Construction path for Psi |
| Church-Turing characterization | `ChurchTuring/CharacterizationTheorem.lean` | Lindstrom-type reframing |
| Claim B (Psi functor) | `Conjecture/Psi.lean` | Not yet written |

## Axioms

| Axiom | File | Notes |
|-------|------|-------|
| `gabrielUlmerDuality` | `Theories/EssentiallyAlgebraic.lean` | Deep theorem, placeholder |

## Files

| File | Sorry | Axiom | Status |
|------|-------|-------|--------|
| `Specification/SubstrateIndependent.lean` | 2 | 0 | Reviewed, approved |
| `Uniqueness/RightAdjointUnique.lean` | 0 | 0 | Clean |
| `Iteration/FinSetDivergence.lean` | 0 | 0 | Clean |
| `Iteration/AdamekChain.lean` | 1 | 0 | Scaffolding |
| `Theories/EssentiallyAlgebraic.lean` | 0 | 1 | Scaffolding |
| `Tensor/BoardmanVogt.lean` | 2 | 0 | Tier 3 conjectures |
| `ChurchTuring/CharacterizationTheorem.lean` | 1 | 0 | Tier 3 conjecture |
| `UnivTest.lean` | 0 | 0 | Test file |

## Benchmarks

| Script | Description |
|--------|-------------|
| `Benchmarks/d1_ratio.py` | D=1 metric ratio for finite sets, confirms super-exponential divergence |

## Summary

- **15 Tier 1 theorems** — fully verified, no sorry
- **3 Tier 2 claims** — stated with sorry, blocked on Adamek's theorem
- **3 Tier 3 conjectures** — formally stated (Claims A, A', Church-Turing characterization)
- **1 axiom** — Gabriel-Ulmer duality (deep theorem, placeholder)
- **6 sorry total** across all files
