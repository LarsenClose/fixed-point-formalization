# Fixed-Point Formalization

Lean 4 v4.28.0 / Mathlib v4.28.0. 42 files. 0 sorry. 0 custom axioms.

---

## Crystal

In any monoidal closed, locally finitely presentable category where the tensor
product preserves finite presentability, the internal hom endofunctor has a
fixed point L that is unique up to isomorphism. This fixed point supports
universal computation.

The proof is a single causal chain:

```
∅ → M(∅) → M²(∅) → ⋯ → L          Forced development (Adamek chain from initial object)
                          ↓
                    L ≅ [A, L]       Identity (Lambek iso: the fixed point IS its function space)
                          ↓
                   Closed container  Containerization (boundary persists under the generator)
                          ↓
                   Identity loop     Identity modulation (fold/unfold IS the computational core)
                          ↓
                   Lambda model      Universal computation (app + abs + β + η, no ℕ needed)
```

Every arrow is a Lean theorem. The key insight: the "computation gap" — whether
the structure forces countable enumeration of programs — was the wrong question.
The reflexive fixed point L ≅ [L, L] is already a model of the untyped lambda
calculus, which is Turing-complete. Computation is not added to the fixed point;
it IS the fixed point. The Lambek iso (fold/unfold, name/evaluate, reify/call) is
not a precondition for computation — it is computation.

Parallel to the categorical construction, the project proves the computability
theory side independently: the Church-Turing characterization theorem (any two
acceptable numberings compute the same class of functions), the Effective Myhill
Isomorphism Theorem (computable bijection from computable injections), and the
strong Rogers isomorphism (computable bijection between any two computation
models). These connect to the categorical side via the three-layer Kleene bridge.

The uniqueness statement is tower initiality: the Adamek chain from ∅ is initial
among all M-generated chains. Any process that generates structural levels by
iterating M receives a unique chain morphism from the canonical chain. This is
the load-bearing claim — the paper references only chain objects and the colimit,
so tower initiality suffices without global functor uniqueness.

---

## What is not proved

The Boardman-Vogt tensor extension and Lawvere-Linton correspondence extension
are novel conjectures stated as weak placeholders in `Tensor/BoardmanVogt.lean`.
No other file depends on them. The CT bridge targets (T13-T16) — deriving full
CompModel axioms from categorical structure in a specific category — are deferred
as research-level.

---

## Index

### Core construction

| File | Lines | What it proves |
|------|------:|----------------|
| `Specification/SubstrateIndependent.lean` | 207 | FixedPointSpec, SubstrateCategory, fixed point exists and is unique |
| `Iteration/InitialChain.lean` | 105 | Omega-chain from initial object |
| `Iteration/ChainShift.lean` | 104 | Chain shift isomorphism |
| `Iteration/AdamekTheorem.lean` | 191 | Adamek's initial algebra theorem |
| `Iteration/AdamekConnection.lean` | 68 | Connection to Mathlib iteration |
| `Iteration/AdamekChain.lean` | 73 | Chain scaffolding |
| `Iteration/FinSetDivergence.lean` | 59 | No finite fixed point exists |
| `Accessibility/RightAdjointAccessible.lean` | 416 | AR 2.23: right adjoints are accessible |

### Tower morphism framework and initiality

| File | Lines | What it proves |
|------|------:|----------------|
| `Iteration/TowerMorphism.lean` | 242 | GeneratedChain, collapseMap, collapse theorem |
| `Iteration/TowerMorphismInstances.lean` | 105 | FixedPointSpec instantiation (collapse = id for same chain) |
| `Iteration/TowerMorphismDistinct.lean` | 142 | Two-spec collapse = initiality iso |
| `Iteration/TowerInitiality.lean` | 127 | Adamek chain is initial among all M-generated chains |

### Reflexive object and computation

| File | Lines | What it proves |
|------|------:|----------------|
| `Reflexive/ReflexiveObject.lean` | 154 | Lambek iso, selfApp, curry/uncurry equivalence |
| `Reflexive/FixedPointCombinator.lean` | 208 | Categorical Y combinator (omega), fixed-point equation |
| `Reflexive/Containerization.lean` | 144 | Closed container: eval/name + β/η, self-reference, fixed points |
| `Reflexive/IdentityLoop.lean` | 93 | Identity modulation: fold/unfold IS the computational core |
| `Reflexive/LambdaModel.lean` | 178 | Untyped lambda calculus model (universal computation without ℕ) |
| `Reflexive/KleeneBridge.lean` | 194 | AbstractFixedPointProperty, categorical-Kleene parallel |
| `Reflexive/SelfIndexedComputation.lean` | 221 | Layer 2: D indexes its own function space |
| `Reflexive/KleeneDerivation.lean` | 217 | Layer 3: ℕ-bridge, ComputabilityStructure, Kleene derivation |

### Uniqueness and self-indexing

| File | Lines | What it proves |
|------|------:|----------------|
| `Uniqueness/RightAdjointUnique.lean` | 67 | ihom is the unique right adjoint of tensorLeft |
| `Uniqueness/MonoidalUniqueness.lean` | 199 | Factored uniqueness (all 3 steps proved) |
| `Uniqueness/TerminalCharacterization.lean` | 158 | If tensorLeft A ⊣ F then F ≅ ihom A |
| `Uniqueness/SelfIndexedTerminalProperty.lean` | 206 | Self-indexing: (𝟙 ⟶ D) ≃ (D ⟶ D) |
| `Uniqueness/CoherentSelfIndexing.lean` | 170 | Coherent self-indexing with eval + eval_compat |
| `Uniqueness/DensityPropagation.lean` | 247 | AR 1.46: filtered-colimit-preserving functors agreeing on f.p. are iso |

### Dimension theory

| File | Lines | What it proves |
|------|------:|----------------|
| `Dimension/TruncationLevel.lean` | 134 | TruncationLevel, chainDimension, HasDimension |
| `Dimension/IncrementDimension.lean` | 76 | F increments dimension by 1 |
| `Dimension/Stabilization.lean` | 114 | Dimension stabilizes at the fixed point |
| `Dimension/GradedFiltration.lean` | 121 | Master graded filtration theorem |
| `Dimension/DimensionIncrement.lean` | 99 | DimensionIncrement typeclass (universal) |
| `Dimension/DivergenceWitnesses.lean` | 182 | FinSet divergence + thin triviality |
| `Dimension/MethodResultConvergence.lean` | 180 | Method-result convergence |
| `Dimension/ConvergenceCriterion.lean` | 121 | Convergence criterion (forward + converse) |
| `Dimension/DimensionalDissolution.lean` | 183 | Yoneda preserves and reflects dimension |
| `Dimension/DimensionTowerChain.lean` | 91 | Adamek chain as GeneratedChain + dimension at each level |

### Computability theory

| File | Lines | What it proves |
|------|------:|----------------|
| `ChurchTuring/CharacterizationTheorem.lean` | 241 | CompModel, codeModel, characterization theorem |
| `ChurchTuring/Myhill.lean` | 1178 | Effective Myhill Isomorphism (full BFF construction) |
| `ChurchTuring/RogersIsomorphism.lean` | 713 | Weak + strong Rogers isomorphism, Kleene recursion |

### Configuration and conjectures

| File | Lines | What it proves |
|------|------:|----------------|
| `Triforce.lean` | 145 | Development + Identity + Forced + self-identity loop |
| `Theories/EssentiallyAlgebraic.lean` | 78 | EAT data definitions |
| `Tensor/BoardmanVogt.lean` | 92 | Conjectures (weak placeholders, trivially proved) |

---

## Verification

```bash
lake build FixedPoint        # Full build
./scripts/verify.sh          # Build + sorry audit + axiom inventory
```
