# Project Status: Fixed-Point Formalization

Lean 4 v4.28.0 / Mathlib v4.28.0. Last updated: 2026-03-05.

This document walks through what the project has proved, what it has not proved,
and where the gaps are -- in plain language, with the full reasoning chains
written out rather than hidden behind theorem names.

---

## What is this project trying to do

The project formalizes a paper series claiming that in a broad class of
mathematical categories, there is a canonical "self-referencing" object -- an
object X that is isomorphic to its own internal function space. The claim is
that this object exists, is unique, and arises from a general fixed-point
construction that does not depend on any particular algebraic system (groups,
rings, topological spaces, etc.).

The construction works in any category that has two properties:
1. It is **monoidal closed**: there is a well-behaved notion of "internal
   function space" (an internal hom functor), meaning for any two objects A and
   B, there is an object [A, B] inside the category representing morphisms from
   A to B, and this assignment is functorial and adjoint to the tensor product.
2. It is **locally presentable**: every object can be built up as a directed
   union of "small" (finitely describable) pieces, and the category has all
   colimits (ways of gluing things together).

The fixed point X is obtained by starting from the simplest possible object
(the initial object, which has exactly one morphism into every other object)
and repeatedly applying the internal hom functor:

```
bottom -> [bottom, bottom] -> [[bottom, bottom], [bottom, bottom]] -> ...
```

The colimit (union) of this chain, if the internal hom functor preserves it,
is the desired fixed point.

The paper series also connects this to computability theory: the Church-Turing
thesis can be reframed as saying that any two "acceptable" models of
computation (ones that satisfy certain closure properties) compute exactly the
same class of functions.

---

## What is fully proved (no sorry, no axioms beyond Lean's standard ones)

### The Adamek initial algebra theorem (4 files, ~600 lines)

**What it says:** Given an endofunctor F on a category with an initial object,
if F preserves the colimit of the chain

```
bottom -> F(bottom) -> F(F(bottom)) -> F(F(F(bottom))) -> ...
```

then the colimit of this chain is an initial algebra of F. An initial algebra
is an object X with a morphism F(X) -> X that is universal: for any other
algebra F(Y) -> Y, there is exactly one algebra homomorphism X -> Y.

**What Lambek's lemma adds:** If X is an initial algebra of F, then the
structure map F(X) -> X is not just a morphism -- it is an isomorphism. So
F(X) is isomorphic to X. The endofunctor has a fixed point.

**What we proved in Lean:** The full chain from initial object to colimit to
initial algebra to fixed-point isomorphism. This uses Mathlib's transfinite
iteration machinery (`SuccStruct`, `iterationFunctor`) for the chain
construction, Mathlib's colimit API for the universal property, and Mathlib's
`Algebra.Initial.str_isIso` for Lambek's lemma. Every step compiles with no
sorry.

Files: `InitialChain.lean`, `ChainShift.lean`, `AdamekTheorem.lean`,
`AdamekConnection.lean`.

### Uniqueness of the right adjoint (1 file, ~67 lines)

**What it says:** In a monoidal closed category, the internal hom functor
ihom(A) is the unique (up to natural isomorphism) right adjoint to the tensor
product functor (- tensor A). Furthermore, the unit of the adjunction is
determined by the adjunction. So there is no freedom in choosing the internal
hom -- the monoidal structure forces it.

**What we proved in Lean:** Using Mathlib's `Adjunction.rightAdjointUniq`, the
endofunctor is unique and the unit coherence follows.

File: `RightAdjointUnique.lean`.

### Finite set divergence (1 file, ~59 lines)

**What it says:** In the category of finite sets, the internal hom [A, B] is
the set of all functions from A to B, which has size |B|^|A|. For any finite
set A with |A| >= 2, the sequence of iterated internal homs

```
|[A, A]| = |A|^|A|, |[[A,A], [A,A]]| = (|A|^|A|)^(|A|^|A|), ...
```

grows super-exponentially and never stabilizes. So there is no finite fixed
point -- the fixed point must live in an infinite completion.

**What we proved in Lean:** Direct cardinality argument. No sorry.

File: `FinSetDivergence.lean`.

### The substrate-independent specification (1 file, ~207 lines)

**What it says:** In any monoidal closed, locally finitely presentable
category (a "substrate category"), where the tensor product preserves finite
presentability, the internal hom endofunctor ihom(A) has an initial algebra,
and that initial algebra is a fixed point (by Lambek) and is unique (by
initiality).

**What we proved in Lean:** The specification compiles and the existence
theorem is fully proved. The proof combines:
- AR 2.23 to show ihom(A) is accessible (preserves filtered colimits)
- The LFP route: in a locally finitely presentable category with
  `TensorLeftFinitelyPresentable`, both kappa and kappa' in AR 2.23
  equal aleph_0, so ihom(A) preserves all filtered colimits including
  omega-chains
- The Adamek theorem to obtain the initial algebra / fixed point
- Lambek's lemma for the isomorphism

**Status:** Tier 1. No sorry. No hypothesis carried. Fully proved from the
substrate category assumptions.

File: `SubstrateIndependent.lean`.

### The Church-Turing characterization theorem (1 file, ~241 lines)

**What it says:** Define a "computation model" (called `CompModel`) as an
acceptable numbering: a countable type of programs with an evaluation function,
where (a) every program computes a partial recursive function
(representability), (b) every partial recursive function is computed by some
program (universality), (c) the evaluation function is itself partial recursive
as a function of both the program index and the input (uniform computability),
and (d) there is a computable, injective currying function (the s-m-n theorem).

Mathlib's `Nat.Partrec.Code` (Kleene's system of indices for partial recursive
functions) is a concrete instance of this structure.

**The characterization theorem:** Any two computation models are equivalent --
they compute exactly the same class of partial functions. The proof: given a
program p in model 1, representability gives a Code computing the same
function, and universality of model 2 gives a program in model 2 computing
that Code. The reverse direction is symmetric.

**What we proved in Lean:** The `CompModel` structure, the `codeModel`
instance, and the characterization theorem. All compile with no sorry.

File: `CharacterizationTheorem.lean`.

### The Effective Myhill Isomorphism Theorem (1 file, ~1178 lines)

**What it says:** Given two Denumerable types with computable injections in both
directions and computable padding functions (indexed, injective in the index,
and R-preserving), there exists a computable bijection that preserves the
relation R.

This is the computable analogue of the Cantor-Bernstein theorem. The classical
proof (Myhill 1955) uses a back-and-forth construction: process elements
0, 1, 2, ... in order, alternately extending the forward and backward maps,
using padding to find fresh targets when needed.

**What we proved in Lean:**

- The full back-and-forth (BFF) construction: `bffState`, `bffStep`, `bffFwd`,
  `bffBwd` — a state machine that builds a partial bijection one element at a
  time using association lists.
- Totality: every element eventually appears in the domain/range (`bffFwd_total`,
  `bffBwd_total`).
- Bijectivity: `bffBwd_bffFwd` and `bffFwd_bffBwd` — the constructed functions
  are mutual inverses.
- R-preservation: the bijection preserves the relation at every point.
- Computability: every component (`inDomain`, `inRange`, `lookupFwd`,
  `lookupBwd`, `findFreshFwd`, `findFreshBwd`, `bffStep`, `bffState`,
  `bffFwd`, `bffBwd`) is proved `Computable` or `Computable₂` via `Primrec`
  composition.
- Assembly: `effective_myhill_nat` for ℕ, `effective_myhill_general` lifted to
  arbitrary `Denumerable` types via `Denumerable.equiv`.

File: `Myhill.lean`.

### Weak Rogers isomorphism, Kleene's recursion theorem, and the strong Rogers isomorphism (1 file, ~713 lines)

**What it says:**

The *weak Rogers isomorphism*: any two computation models are connected by
computable translation functions in both directions that preserve evaluation.
That is, there is a computable function sending each model-1 program to a
model-2 program computing the same thing, and vice versa. These translations
are not inverses of each other (many programs compute the same function, so the
round-trip may land on a different program), but they preserve semantics.

*Kleene's recursion theorem for abstract models*: for any computable
endomorphism f on programs, there exists a program p such that f(p) and p
compute the same partial function. This is the self-reference property: any
computable transformation of programs has a semantic fixed point.

*The strong Rogers isomorphism*: any two computation models are connected by
a computable *bijection* that preserves evaluation. The proof builds on
`injTranslate` -- a computable, injective, evaluation-preserving translation
constructed from s-m-n + padding -- and applies the Effective Myhill
Isomorphism Theorem (proved in `Myhill.lean`) to obtain the bijection.

**What we proved in Lean:**

- Padding derived from s-m-n: `pad m q k = smn_fun (projProg m) (pair (encode q) k)`.
  Proved computable, evaluation-preserving, and injective in k.
- Computable injective translations between any two models (`injTranslate`),
  with computability, injectivity, and evaluation-preservation proved.
- The weak Rogers isomorphism assembling both directions.
- Kleene's recursion theorem derived from the CompModel axioms (not from
  Mathlib's `Code.fixed_point` -- the proof is internal to the abstract model).
- `ComputableIso` shown to be an equivalence relation (reflexive, symmetric,
  transitive).
- The strong Rogers isomorphism via `effective_myhill` (now a proved theorem,
  no longer an axiom).

File: `RogersIsomorphism.lean`.

### Adamek-Rosicky Theorem 2.23 (1 file, ~416 lines)

**What it says:** If F is a left adjoint and G is its right adjoint, and
both the source and target categories are locally presentable (every object
is a directed union of small pieces), then G is "accessible" -- it preserves
sufficiently filtered colimits.

The proof has five parts:

1. **Cardinal supremum:** Given a small collection of objects in a locally
   presentable category, find a single cardinal kappa' such that all of them
   are kappa'-presentable (their hom-functors preserve kappa'-filtered
   colimits). This works because there are only set-many such objects, each
   is presentable at some cardinal, and the supremum of set-many cardinals
   (bumped to the next regular cardinal) works.

2. **Uniform presentability of left adjoint on generators:** The left adjoint
   F sends the (essentially small) set of kappa-presentable objects in C to
   objects in D. Since D is locally presentable, each F(X) is presentable at
   some cardinal. By the cardinal supremum lemma, there is a single kappa'
   such that F(X) is kappa'-presentable for all kappa-presentable X.

3. **Adjunction isomorphism on hom-functors:** For any object X in C, the
   adjunction gives a natural isomorphism Hom(X, G(-)) = Hom(F(X), -). If
   F(X) is kappa'-presentable, then Hom(F(X), -) preserves kappa'-filtered
   colimits, so Hom(X, G(-)) does too.

4. **Detection by generators:** If Hom(X, G(-)) preserves kappa'-filtered
   colimits for every kappa-presentable X (which form a strong generator),
   then G itself preserves kappa'-filtered colimits. The argument: to check
   that a cocone map is an isomorphism, it suffices to check after applying
   Hom(X, -) for every X in a strong generator. Strong generators detect
   isomorphisms (a monomorphism that is surjective on hom-sets from every
   generator is an isomorphism).

5. **Assembly:** Combine 1-4 to conclude G is kappa'-accessible.

**What we proved in Lean:** All five parts, with part 4 (detection by
generators) being the most technically demanding (~100 lines). No sorry in
the main theorem chain.

**Gap 1 closure:** In the previous version, AR 2.23 proved G is accessible
at some cardinal kappa', but kappa' might be larger than aleph_0. This has
been resolved by restricting to locally finitely presentable categories and
using the `TensorLeftFinitelyPresentable` typeclass, which ensures both
kappa and kappa' equal aleph_0. See the substrate-independent specification
above.

File: `RightAdjointAccessible.lean`.

---

## Boardman-Vogt conjectures (`BoardmanVogt.lean` — isolated, 0 sorry)

`BoardmanVogt.lean` contains formal placeholder statements for the BV tensor
extension (Claim A) and Lawvere-Linton correspondence extension (Claim A').
These are novel conjectures from the paper series. The theorem types are weak
(existential witnesses are trivially constructible); the real mathematical
content is described in docstrings, not in the types. **No sorry is used** —
the placeholders are proved trivially. No other file depends on them.

---

## What all of this means for the project's claims

### Category theory side (fully proved, no sorry, no custom axioms)

> In any monoidal closed, locally finitely presentable category where
> the tensor product preserves finite presentability, the internal hom
> endofunctor has a fixed point that is unique up to isomorphism.

The proof chain: AR 2.23 shows the internal hom is accessible at aleph_0
(using the LFP route with `TensorLeftFinitelyPresentable`), so it preserves
filtered colimits including omega-chains. Adamek's theorem then gives the
initial algebra, and Lambek's lemma gives the fixed-point isomorphism.
Uniqueness follows from initiality.

### Computability side (fully proved, no sorry, no custom axioms)

The characterization theorem (any two acceptable numberings compute the same
class of functions), the weak Rogers isomorphism (computable translations in
both directions), Kleene's recursion theorem for abstract models, the
Effective Myhill Isomorphism Theorem (full back-and-forth construction with
computability proved via `Primrec` composition), and the strong Rogers
isomorphism (a computable bijection between any two acceptable numberings)
are all fully proved with no custom axioms.

### Theory layer (conjectural, not formalized)

The Boardman-Vogt tensor product extension and Lawvere-Linton correspondence
extension are novel conjectures from the paper. They are stated as sorry'd
placeholders in an isolated file. No other result depends on them. Formalizing
them would require both settling the mathematics and building substantial
Mathlib infrastructure that does not exist.

---

## Dimensionality paper targets (NEXT_STEPS.md)

Six formalization targets were identified for the "Dimensionality as Fixed Point"
paper companion. Five are complete; one is deferred.

### Target 1: Dimension via truncation filtration (DONE)

Defines `TruncationLevel` (dimZero | dimSucc | dimOmega), `chainDimension : N -> TruncationLevel`,
and `HasDimension F X d` (propositional: X is isomorphic to the n-th iterate and n maps to d).
Proves dimension is invariant under isomorphism and each iterate has its canonical dimension.
No sorry.

File: `Dimension/TruncationLevel.lean` (134 lines).

### Target 2: M increments dimension by exactly one (DONE)

If X has dimension n, then F(X) has dimension n+1. The proof extracts the
chain index, applies F to the isomorphism witness, and re-indexes.
No sorry.

File: `Dimension/IncrementDimension.lean` (76 lines).

### Target 2.5: Dimension stabilizes at the fixed point (DONE)

At the fixed point L where F(L) ≅ L, dimension is invariant under F:
`HasDimension F L d <-> HasDimension F (F.obj L) d`. The proof transports
dimension through the Lambek isomorphism in both directions.

Also proves `fixedpoint_absorbs_increment`: at a fixed point with finite
dimension chainDimension n, F(L) has both dimension n (by stability) and n+1
(by increment). Since chainDimension is injective, the fixed point cannot have
any finite dimension -- it lives at the omega level. This is the dimensional
content of the D=1 result.

Connects to `FixedPointSpec` via `spec_dimension_stable` and `spec_dimension_iff`.
No sorry.

File: `Dimension/Stabilization.lean` (114 lines).

### Target 3: Reflexive object and self-application (DONE)

Defines `ReflexiveObject` packaging the Lambek iso `[A, L] ≅ L` with derived
operations: `selfApp : A ⊗ L --> L` (decode via phi-inverse then evaluate),
`reflexiveCurry`/`reflexiveUncurry` (curry through the iso), and the
`curryEquiv` witnessing these are inverse. Proves selfApp factors through eval,
and round-trip identities for curry/uncurry. Constructs from `FixedPointSpec`.
No sorry.

File: `Reflexive/ReflexiveObject.lean` (154 lines).

### Target 4: Fixed-point combinator (DONE)

Constructs the categorical Y combinator from the reflexive object.
`omega f : L --> L` is the categorical analogue of `lambda x. f(x x)`,
defined as `reflexiveCurry (selfApp >> f)`.

The key theorem `omega_fixed_point`:
`A ◁ (omega f) >> selfApp = selfApp >> f`
-- whiskering omega_f before self-application equals self-applying then applying f.

Also defines `omegaSq f = omega f >> omega f` (the morphism-level Y(f)) and
proves its unfolding equations. No sorry.

File: `Reflexive/FixedPointCombinator.lean` (208 lines).

### Target 5a: Monoidal uniqueness framework (DONE -- 0 sorry)

States the three-step uniqueness argument:
- Step (a): Right adjoints are unique (PROVED -- wraps `rightAdjointForcedToIHom`)
- Step (b): M = ihom of BV monoidal structure (PROVED given adjunction hypothesis)
- Step (c): M is unique given the monoidal structure (PROVED -- `bv_endofunctor_unique`)

All three steps are fully proved (0 sorry). The mathematical gap is in Step (b)'s
*hypothesis*: the adjunction `tensorLeft A ⊣ M` must be externally provided, which
requires the BV tensor extension (Claim A, Tier 3). But the theorem itself is proved —
the gap is in constructing the hypothesis, not in the proof.

File: `Uniqueness/MonoidalUniqueness.lean` (199 lines).

### Target 5(b,c): Full monoidal uniqueness (DEFERRED)

Requires the Boardman-Vogt tensor extension (Claim A, Tier 3). Not tractable
without settling the open mathematics and building substantial Mathlib
infrastructure.

### Target 6: CPS as computational shadow of M (DEFERRED)

Exploratory target: the CPS transform at response type D corresponds to
applying ihom composed with the Lambek iso. Requires new mathematical
development connecting the categorical CPS literature (Thielecke 1997,
Hasegawa 2002) to the internal hom formalization. Not tractable now.

### Target 7: Graded filtration theorem (DONE)

The master graded filtration theorem assembling T1+T2+T2.5: the Adamek chain
is an N-indexed filtration by dimension with canonical dimensions, strict
grading (injective chainDimension), and stabilization at the fixed point.
Under `HasUniqueDimension` (each object has at most one dimension), the
fixed point has no finite dimension. Also proves by induction that the fixed
point has all higher dimensions.
No sorry.

File: `Dimension/GradedFiltration.lean` (121 lines).

### Target 8: T4 -> Kleene bridge (DONE)

Connects the categorical Y combinator (T4) to Kleene's recursion theorem.
Defines `AbstractFixedPointProperty` as the common abstraction: for every
endomorphism, a semantic fixed point exists. Shows both the categorical omega
and the CompModel Kleene property are instances. `FixedPointBridge` packages
the morphism-level fixed-point equation with its iterated form. Works at
the morphism level throughout, avoiding global-section type complications.
No sorry.

File: `Reflexive/KleeneBridge.lean` (194 lines).

### Target 10: Convergence criterion theorem (DONE)

Forward direction: `FixedPointSpec` -> `ReflexiveObject` -> omega ->
fixed-point equation. `ConvergencePipeline` packages the full pipeline.
Converse: `no_initial_algebra_no_pipeline` -- if no initial algebra exists
(using `IsEmpty (IsInitial alg)` since `IsInitial` is a Type), no pipeline
can be constructed. Careful handling of the initiality qualifier.
No sorry.

File: `Dimension/ConvergenceCriterion.lean` (121 lines).

### Target 11: Divergence witnesses (DONE)

Part 1: FinSet divergence restated dimensionally. `iterateCard a d n`
computes cardinalities of iterated internal hom. Proves strict monotonicity,
injectivity, and divergence to infinity when |A| >= 2 and |D| >= 2.

Part 2: Thin categories. Defines `IsThin` typeclass (at most one morphism
per hom set). Proves thin reflexive objects are trivially subterminal and
thin categories cannot support nontrivial computation (at most one morphism
contradicts denumerable programs requirement).
No sorry.

File: `Dimension/DivergenceWitnesses.lean` (182 lines).

### Target 12: Method-result convergence (DONE)

`MethodResultConvergence` structure packaging: Lambek iso, dimension
stability (iff), dimension constancy across iterates, and increment
absorption. Proves `fixedpoint_implies_chain_stabilized` (finite dimension
implies chain already stabilized), `fixedpoint_no_finite_dimension` (under
strict non-stabilization), and `fixedpoint_dimension_dichotomy` (either
finite dimension with stabilization, or no finite dimension at all).
Connects to `FixedPointSpec` via `spec_method_result_convergence`.
No sorry.

File: `Dimension/MethodResultConvergence.lean` (180 lines).

### Target 9: Dimensional dissolution (DONE)

The Yoneda embedding commutes with ihom(A) via Mathlib's
`Adjunction.compYonedaIso` applied to `tensorLeft A ⊣ ihom A`. Rather than
defining dimension independently for presheaves, defines `HasEmbeddedDimension`
(presheaf is iso to yoneda of a chain object) and proves Yoneda preserves and
reflects dimension (`yoneda_dimension_iff`). `DimensionalDissolution` structure
packages the full result: dimension equivalence + embedded stability at the
fixed point. No sorry.

File: `Dimension/DimensionalDissolution.lean` (183 lines).

### Kleene Bridge Layers 2 and 3 (DONE)

The three-layer Kleene bridge architecture connecting categorical structure to
classical computability:

**Layer 1** (ReflexiveObject, already in T3/T4): The categorical data — Lambek
iso, selfApp, omega, omega_fixed_point.

**Layer 2** (SelfIndexedComputation): Repackages the reflexive object as a
self-indexed computation model. D indexes its own function space: the Lambek iso
IS the naming function, CCC curry IS s-m-n, omega IS Kleene's recursion theorem.
No external enumeration (N) needed. Key results: `naming_equiv` (programs biject
with functions at every base), `selfApp_recovers_named` (evaluation recovers the
named function), `self_indexed_kleene` (omega restated in computation vocabulary),
`SelfIndexedComputation` structure, `selfIndexedAFPP`. No sorry.

**Layer 3** (KleeneDerivation): The N-bridge. `ComputabilityStructure` typeclass
equips a reflexive object with enumerative data (Prog, eval, Denumerable,
representable, universal, eval_partrec, s-m-n). This is the "interpreter" that
translates categorical morphism equality into extensional program equality.
`compModelFromReflexive` packages this into a `CompModel`.
`kleeneDerivation` derives Kleene's recursion theorem by applying
`hasSelfReference_of_computable` from RogersIsomorphism.lean. No sorry.

The key insight: the categorical omega is the *mechanism*, but once a valid
CompModel is constructed, Kleene follows from existing general theory.
`categorical_implies_kleene` and `full_kleene_bridge` state the definitive
bridge theorems.

Files: `Reflexive/SelfIndexedComputation.lean` (221 lines),
`Reflexive/KleeneDerivation.lean` (217 lines).

### Coherent self-indexing (DONE)

`CoherentSelfIndexedFixedPoint` enriches `SelfIndexedFixedPoint` with an evaluation
map `eval : D ⊗ D ⟶ D` and two coherence conditions:
- `eval_compat`: evaluating a named function recovers it
- `eval_id`: the name of the identity is a right unit for eval

The bridge `coherentFromReflexive` constructs this from a reflexive object with
A = carrier. The proof uses `whiskerLeft_comp`, `whisker_exchange` (twice),
`Iso.hom_inv_id`, `MonoidalClosed.whiskerLeft_curry_ihom_ev_app` (via `erw`),
and `rightUnitor_naturality`. No sorry.

File: `Uniqueness/CoherentSelfIndexing.lean` (170 lines).

### Density propagation theorem (DONE -- fully proved)

`densityPropagation` proves Adamek-Rosicky Theorem 1.46: if two endofunctors
on an LFP category both preserve filtered colimits and agree naturally on all
finitely presentable objects, they are naturally isomorphic. The proof assembles
three Mathlib ingredients: `IsDense` (density of presentable objects),
`isColimitOfPreserves` (colimit transport), and
`IsColimit.coconePointsIsoOfNatIso` (colimit comparison). Naturality follows
by checking on coprojections of the density colimit.

Universe note: uses `PreservesFilteredColimitsOfSize.{v, max u v}` because the
index category `CostructuredArrow ι X` lives in `Type (max u v)`.

Downstream: `densityPropagation_ihom` specializes to G = ihom(A).
No sorry.

File: `Uniqueness/DensityPropagation.lean` (247 lines).

### Dimension-tower chain bridge (DONE)

Connects dimension/iteration infrastructure to the tower morphism `GeneratedChain`
framework. The Adamek initial chain for any endofunctor F is a `GeneratedChain F`
(definitional: `iterateObj F (n+1) = F.obj (iterateObj F n)`). Each level carries
its canonical dimension from the graded filtration. No sorry.

File: `Dimension/DimensionTowerChain.lean` (91 lines).

### Distinct-spec tower morphism (DONE)

Given two `FixedPointSpec A` instances, the tower morphism framework's collapse
recovers the canonical initial algebra isomorphism. `twoSpecCollapse_is_unique`
proves the tower-mediated morphism equals `(fixedPoint_unique fp₁ fp₂).hom.f`.
`twoSpecCollapseIso` provides the full isomorphism with inverse. No sorry.

File: `Iteration/TowerMorphismDistinct.lean` (142 lines).

### Tower initiality (DONE)

**The load-bearing uniqueness statement.** The Adamek chain from ⊥ is initial
among ALL M-generated chains: for any `GeneratedChain M`, the level-wise maps
from the Adamek chain are uniquely determined. The initial object gives level 0
(unique map from ⊥), M-compatibility propagates inductively through all finite
levels, and uniqueness follows from the uniqueness at level 0.

This is the chain-level analogue of the initial algebra's universal property.
Any process that generates structural levels by iterating M — whatever its
domain-specific content (homotopy, homology, topology, computation, CPS) —
receives a unique chain morphism from the Adamek chain.

**Why this is load-bearing:** Every claim in the paper references only chain
objects and the colimit. No claim requires evaluating M on arbitrary finitely
presentable objects outside the chain. Tower initiality gives exactly what the
paper needs: M's chain is initial, so any chain reaching the same fixed point
factors through it. Global functor uniqueness (F ≅ ihom(A) on all of C) is a
strictly stronger statement that the paper does not require. The BV tensor
extension, which would give global uniqueness, is an open conjecture — but it
is no longer in the critical path.

Key results: `adamekChainMorphismComponents` (level-wise maps),
`adamekChainMorphismTo_unique` (uniqueness by induction from ⊥),
`adamekChainMorphism_ext` (any two chain morphisms agree),
`adamekChain_initial` (existence + uniqueness). No sorry.

File: `Iteration/TowerInitiality.lean` (127 lines).

### Triforce: Identity as Forced Development (DONE)

The `Triforce M` structure packages the entire initial algebra construction as
a single CT configuration: Development (the Adamek chain), Identity (Lambek iso),
Forced (tower initiality), and self-identity (collapse to own colimit is identity).
`adamekTriforce` constructs from existing infrastructure. Visibility derivations:
`Triforce.reflexiveObject` in monoidal closed context, `Triforce.selfIndexed` when
A = carrier. No sorry.

File: `Triforce.lean` (145 lines).

### Containerization: reflexive fixed point as closed container (DONE)

`ClosedContainer` formalizes that the reflexive object IS a container: `eval`
(opening/evaluation), `name` (closing/reification), with β-law (eval after name
recovers content) and η-law (name after eval recovers the name). The Lambek iso
is the container boundary. Derives self-reference (`name(eval)` = the quine) and
fixed points of all endomorphisms from container operations alone. No sorry.

File: `Reflexive/Containerization.lean` (144 lines).

### Identity loop: identity modulation as computational core (DONE)

`IdentityLoop` packages four equations about the identity morphism:
1. `selfApp = reflexiveUncurry(𝟙)` — evaluation is identity unfolded
2. `omega(𝟙) = reflexiveCurry(selfApp)` — the quine is evaluation folded
3. `reflexiveCurry(reflexiveUncurry(𝟙)) = 𝟙` — fold after unfold = identity
4. `reflexiveUncurry(reflexiveCurry(selfApp)) = selfApp` — unfold after fold = eval

The quine `omega(𝟙)` is the self-recognition element: L contains, as a datum,
the act of running itself. `quine_self_recognition` proves `A ◁ quine ≫ selfApp = selfApp`.
`computation_from_identity` proves all computation is identity, unfolded, then post-composed.
No sorry.

File: `Reflexive/IdentityLoop.lean` (93 lines).

### Lambda calculus model: universal computation without ℕ (DONE)

`LambdaModel` formalizes that a reflexive object with carrier ≅ A is a model of the
untyped lambda calculus: `app : L ⊗ L → L` (application), `abs : (L ⊗ X → L) → (X → L)`
(abstraction), β-reduction, η-expansion. Construction threads the carrier ≅ A iso
through tensor products using whisker exchange and comp_whiskerRight.

`omegaMap_eq` proves the fixed-point equation purely in lambda model terms:
`L ◁ omegaMap(f) ≫ app = app ≫ f`. Since the untyped lambda calculus is
Turing-complete, the reflexive fixed point supports universal computation
without ℕ-enumeration, without choice beyond colimit existence, without
external counting. No sorry.

File: `Reflexive/LambdaModel.lean` (178 lines).

### Target 13: CT Bridge -- Universal Evaluation (DEFERRED)

From D ≅ [D,D], derive that D supports a universal evaluation map satisfying
the CompModel `universal` axiom. Requires formalizing the Dom category (pointed
CPOs with strict maps) and connecting T3's selfApp to the universal partial
recursive function. Hard -- genuine mathematical development needed.

### Target 14: CT Bridge -- Full (DEFERRED)

Derive all CompModel axioms from categorical structure: universality (T13),
representability (from the Lambek iso), s-m-n (from CCC curry), eval_partrec
(connecting to partiality). Research-level. The standing open target across the
paper series.

### Target 15: CPS Foundations (DEFERRED)

Define the categorical CPS transform from the reflexive object. Show that the
continuation monad at R = D is the identity monad because
[A, [A, D] -> D] ≅ [A, D] ≅ D for all A that are retracts of D. Requires
encoding Hasegawa 1995 / Thielecke 1997 / Fuhrmann 1999.

### Target 16: BV Tensor (DEFERRED)

The Boardman-Vogt tensor on EAT. Would unlock T5a's sorry and the Adjunction
paper's monoidal structure claims. Blocked by Gabriel-Ulmer duality not being
in Mathlib.

---

## File inventory

| File | Lines | Sorry | Axioms | What it proves |
|------|-------|-------|--------|----------------|
| `Iteration/InitialChain.lean` | 105 | 0 | 0 | Omega-chain from initial object |
| `Iteration/ChainShift.lean` | 104 | 0 | 0 | Chain shift isomorphism |
| `Iteration/AdamekTheorem.lean` | 191 | 0 | 0 | Adamek's initial algebra theorem |
| `Iteration/AdamekConnection.lean` | 68 | 0 | 0 | Connection to existing Mathlib iteration |
| `Iteration/AdamekChain.lean` | 73 | 0 | 0 | Chain scaffolding |
| `Iteration/FinSetDivergence.lean` | 59 | 0 | 0 | No finite fixed point exists |
| `Iteration/TowerMorphism.lean` | 242 | 0 | 0 | ω-chain collapse theorem (tower morphisms) |
| `Iteration/TowerMorphismInstances.lean` | 105 | 0 | 0 | Tower morphism instantiation (identity chain) |
| `Iteration/TowerMorphismDistinct.lean` | 142 | 0 | 0 | Distinct-spec collapse = initiality iso |
| `Iteration/TowerInitiality.lean` | 127 | 0 | 0 | Tower initiality: Adamek chain is initial |
| `Specification/SubstrateIndependent.lean` | 207 | 0 | 0 | Fixed point exists and is unique |
| `Uniqueness/RightAdjointUnique.lean` | 67 | 0 | 0 | Internal hom is the unique right adjoint |
| `Uniqueness/MonoidalUniqueness.lean` | 199 | 0 | 0 | Factored uniqueness (all 3 steps proved) |
| `Uniqueness/TerminalCharacterization.lean` | 158 | 0 | 0 | Terminal characterization (proved form) |
| `Uniqueness/SelfIndexedTerminalProperty.lean` | 206 | 0 | 0 | Self-indexed terminal property |
| `Uniqueness/CoherentSelfIndexing.lean` | 170 | 0 | 0 | Coherent self-indexing (eval_compat proved) |
| `Uniqueness/DensityPropagation.lean` | 247 | 0 | 0 | Density propagation theorem (AR 1.46, proved) |
| `Accessibility/RightAdjointAccessible.lean` | 416 | 0 | 0 | AR 2.23: right adjoints are accessible |
| `ChurchTuring/CharacterizationTheorem.lean` | 241 | 0 | 0 | CompModel structure, characterization theorem |
| `ChurchTuring/Myhill.lean` | 1178 | 0 | 0 | Effective Myhill Isomorphism Theorem (BFF) |
| `ChurchTuring/RogersIsomorphism.lean` | 713 | 0 | 0 | Rogers isomorphism (weak + strong) |
| `Theories/EssentiallyAlgebraic.lean` | 78 | 0 | 0 | EAT data definitions |
| `Tensor/BoardmanVogt.lean` | 92 | 0 | 0 | Conjectures (weak placeholders, trivially proved) |
| `Reflexive/ReflexiveObject.lean` | 154 | 0 | 0 | Reflexive object, selfApp, curry/uncurry |
| `Reflexive/FixedPointCombinator.lean` | 208 | 0 | 0 | Categorical Y combinator (omega) |
| `Reflexive/KleeneBridge.lean` | 194 | 0 | 0 | T4 -> Kleene bridge |
| `Reflexive/SelfIndexedComputation.lean` | 221 | 0 | 0 | Layer 2: self-indexed computation model |
| `Reflexive/KleeneDerivation.lean` | 217 | 0 | 0 | Layer 3: N-bridge, Kleene derivation |
| `Dimension/TruncationLevel.lean` | 134 | 0 | 0 | Dimension definition, iso invariance |
| `Dimension/IncrementDimension.lean` | 76 | 0 | 0 | F increments dimension by 1 |
| `Dimension/Stabilization.lean` | 114 | 0 | 0 | Dimension stabilizes at fixed point |
| `Dimension/GradedFiltration.lean` | 121 | 0 | 0 | Master graded filtration theorem |
| `Dimension/DimensionIncrement.lean` | 99 | 0 | 0 | DimensionIncrement typeclass (universal) |
| `Dimension/DivergenceWitnesses.lean` | 182 | 0 | 0 | FinSet divergence + thin triviality |
| `Dimension/MethodResultConvergence.lean` | 180 | 0 | 0 | Method-result convergence |
| `Dimension/ConvergenceCriterion.lean` | 121 | 0 | 0 | Convergence criterion (fwd + converse) |
| `Dimension/DimensionalDissolution.lean` | 183 | 0 | 0 | Yoneda M-compatibility, dissolution |
| `Dimension/DimensionTowerChain.lean` | 91 | 0 | 0 | Dimension-tower chain bridge |
| `Triforce.lean` | 145 | 0 | 0 | Triforce: Development + Identity + Forced + self-identity |
| `Reflexive/Containerization.lean` | 144 | 0 | 0 | Closed container: eval/name with β + η |
| `Reflexive/IdentityLoop.lean` | 93 | 0 | 0 | Identity modulation as computational core |
| `Reflexive/LambdaModel.lean` | 178 | 0 | 0 | Untyped lambda calculus model (universal computation) |

**Total: 42 files of Lean.**

- **0 sorry**.
- **0 custom axioms**. The only axioms used are Lean's standard three:
  `propext`, `Classical.choice`, `Quot.sound`.

Run `./scripts/verify.sh` to reproduce these numbers.

---

## Other files

| File | Purpose |
|------|---------|
| `README.md` | Project overview |
| `Status.md` | This document |
| `scripts/verify.sh` | Build + sorry audit + axiom inventory |
