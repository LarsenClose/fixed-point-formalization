# lean4-fixed-point

Lean 4 formalization of fixed-point constructions in monoidal closed, locally
presentable categories, with connections to computability theory.

## What is proved

### Category theory (no sorry, no custom axioms)

In any monoidal closed, locally finitely presentable category where the tensor
product preserves finite presentability, the internal hom endofunctor has a
fixed point that is unique up to isomorphism.

The proof combines:
- **Adamek's initial algebra theorem** — the colimit of the iteration chain
  from the initial object is an initial algebra, hence a fixed point by
  Lambek's lemma
- **Adamek-Rosicky Theorem 2.23** — right adjoints between locally presentable
  categories are accessible
- **The LFP route** — in locally finitely presentable categories, accessibility
  at aleph_0 gives preservation of all filtered colimits, including the
  omega-chain needed by Adamek's theorem

### Computability theory (no sorry, one standard axiom)

- **Characterization theorem** — any two acceptable numberings (CompModels)
  compute the same class of partial recursive functions
- **Weak Rogers isomorphism** — computable translations in both directions
  preserving evaluation
- **Kleene's recursion theorem** — every computable transformation of programs
  has a semantic fixed point, derived from the CompModel axioms
- **Strong Rogers isomorphism** — a computable bijection between any two
  CompModels preserving evaluation, proved from the Myhill Isomorphism Theorem
  (1955), which is taken as an axiom (see below)

## What is not proved

`BoardmanVogt.lean` contains two sorry'd conjectures from the paper series:
that the Boardman-Vogt tensor product extends to essentially algebraic
theories, and that the Lawvere-Linton correspondence extends similarly. These
are novel mathematical claims that have not been proved anywhere. No other file
depends on them.

## The one axiom

`effective_myhill` (Myhill's Isomorphism Theorem, 1955): computable injections
in both directions plus padding yield a computable bijection. This is a
standard textbook result (Rogers 1967, Soare 1987, Cutland 1980). It is taken
as an axiom because proving it in Lean requires ~250 lines of `Primrec`
composition to encode the back-and-forth state machine. Only
`rogers_isomorphism` depends on it.

## Verification

```bash
# Build the project and check for errors
lake build

# Run the full audit (build + sorry check + axiom inventory)
./scripts/verify.sh
```

## Structure

See [Status.md](Status.md) for a detailed walkthrough of what is proved, what
is not, and why.

| Directory | What it contains |
|-----------|-----------------|
| `Iteration/` | Adamek's initial algebra theorem (4 files) |
| `Specification/` | Substrate-independent fixed-point existence and uniqueness |
| `Uniqueness/` | Right adjoint uniqueness |
| `Accessibility/` | AR Theorem 2.23 |
| `ChurchTuring/` | CompModel, characterization, Rogers isomorphism |
| `Theories/` | Essentially algebraic theory definitions |
| `Tensor/` | Boardman-Vogt conjectures (isolated) |

## Requirements

- Lean 4 v4.28.0
- Mathlib v4.28.0

## License

See repository license.
