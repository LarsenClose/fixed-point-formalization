# lean4-fixed-point

[![Lean Action CI](https://github.com/LarsenClose/lean4-fixed-point/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/LarsenClose/lean4-fixed-point/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/docs-GitHub%20Pages-blue)](https://larsenclose.github.io/lean4-fixed-point/)

Lean 4 formalization of fixed-point constructions in monoidal closed, locally
presentable categories, with connections to computability theory and categorical
dimension.

**30 files, 6157 lines of Lean. 0 sorry. 0 custom axioms.**

## Main results

### Fixed-point existence and uniqueness (no sorry, no custom axioms)

In any monoidal closed, locally finitely presentable category where the tensor
product preserves finite presentability, the internal hom endofunctor has a
fixed point that is unique up to isomorphism.

The proof combines Adamek's initial algebra theorem, Lambek's lemma,
Adamek-Rosicky Theorem 2.23, and the LFP route (accessibility at aleph_0).

### Reflexive object and categorical Y combinator (no sorry)

The fixed point L with Lambek iso `[A, L] ≅ L` is a reflexive object: it
encodes its own function space. From this structure:

- **Self-application** (`selfApp : A ⊗ L --> L`): decode an element of L as a
  function via the Lambek inverse, then evaluate.
- **Categorical Y combinator** (`omega f`): for every endomorphism `f : L --> L`,
  the fixed-point equation holds:
  ```
  A ◁ omega(f) >> selfApp = selfApp >> f
  ```
  This is the morphism-level Kleene recursion theorem — every transformation of
  the carrier has a semantic fixed point.

### Kleene bridge: from categories to computation (no sorry)

A three-layer architecture connecting the categorical Y combinator to classical
computability:

1. **Layer 1** (ReflexiveObject): categorical data — iso, selfApp, omega
2. **Layer 2** (SelfIndexedComputation): D indexes its own function space. The
   Lambek iso IS the naming function, CCC curry IS s-m-n, omega IS Kleene. No
   external enumeration needed.
3. **Layer 3** (KleeneDerivation): the N-bridge. A `ComputabilityStructure`
   typeclass adds enumerative data (countable programs, partial recursive
   evaluation). Kleene's recursion theorem is then derived from the general
   `CompModel` theory.

### Dimensional theory (no sorry)

The Adamek chain is an N-indexed filtration by dimension:

- **Truncation levels**: dimZero, dimSucc, dimOmega — a dimension for each
  chain iterate
- **F increments dimension by 1**: applying the endofunctor raises dimension
- **Stabilization at the fixed point**: at L where F(L) ≅ L, dimension is
  invariant under F. The fixed point cannot have any finite dimension — it lives
  at the omega level.
- **Graded filtration theorem**: assembles increment, stabilization, and
  injectivity into a single structure
- **Dimensional dissolution**: the Yoneda embedding preserves and reflects
  dimension — internal dimension in C equals embedded dimension in presheaves,
  via Mathlib's `Adjunction.compYonedaIso`
- **Divergence witnesses**: FinSet divergence (cardinalities grow
  super-exponentially) and thin category triviality (at most one morphism
  contradicts reflexive structure)
- **Convergence criterion**: forward (FixedPointSpec implies omega + fixed-point
  equation) and converse (no initial algebra implies no pipeline)
- **DimensionIncrement typeclass**: every endofunctor satisfies it (the
  dimension-increment property is intrinsic to the chain construction)

### Terminal characterization (no sorry)

`HasAdamekFixedPoint F` packages: carrier, Lambek iso, initiality. The
original conjecture — that any endofunctor with an Adamek fixed point must
be isomorphic to the internal hom — was investigated and found to be false.
Counterexamples: the powerset functor (Adamek FP but not right adjoint)
and the identity functor (right adjoint but left adjoint is not a tensor).
The precise result: `terminal_characterization_from_adjunction` proves that
if `tensorLeft A ⊣ F`, then `F ≅ ihom A`. The additional structure needed
is exactly the tensor-hom adjunction — uniqueness of right adjoints does
the rest.

### Computability theory (no sorry, no custom axioms)

- **Characterization theorem**: any two acceptable numberings compute the same
  class of partial recursive functions
- **Weak Rogers isomorphism**: computable translations in both directions
- **Kleene's recursion theorem**: every computable transformation of programs
  has a semantic fixed point
- **Effective Myhill Isomorphism Theorem**: computable injections in both
  directions plus computable padding yield a computable bijection. Full
  back-and-forth construction with computability proved via `Primrec` composition.
- **Strong Rogers isomorphism**: a computable bijection between any two
  CompModels, proved using the Effective Myhill theorem

## What is not proved

`BoardmanVogt.lean` contains formal placeholder statements for the BV tensor
extension and Lawvere-Linton correspondence extension conjectures. The theorem
types are weak (existential witnesses are trivially constructible); the real
mathematical content is described in docstrings, not in the types.

## Structure

See [Status.md](Status.md) for a detailed walkthrough of what is proved, what
is not, and why.

| Directory | What it contains |
|-----------|-----------------|
| `Iteration/` | Adamek's initial algebra theorem, chain construction (6 files) |
| `Specification/` | Substrate-independent fixed-point existence and uniqueness |
| `Uniqueness/` | Right adjoint uniqueness, monoidal uniqueness, terminal characterization (3 files) |
| `Accessibility/` | AR Theorem 2.23 |
| `ChurchTuring/` | CompModel, characterization, Myhill theorem, Rogers isomorphism |
| `Reflexive/` | Reflexive object, Y combinator, Kleene bridge and derivation (5 files) |
| `Dimension/` | Truncation levels, graded filtration, dissolution, divergence (9 files) |
| `Theories/` | Essentially algebraic theory definitions |
| `Tensor/` | Boardman-Vogt conjectures (isolated) |

## Verification

```bash
# Build the project and check for errors
lake build

# Run the full audit (build + sorry check + axiom inventory)
./scripts/verify.sh
```

## Requirements

- Lean 4 v4.28.0
- Mathlib v4.28.0

## License

See repository license.
