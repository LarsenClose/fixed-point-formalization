# Project Status: Fixed-Point Formalization

Lean 4 v4.28.0 / Mathlib v4.28.0. Last updated: 2026-03-04.

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

### Weak Rogers isomorphism, Kleene's recursion theorem, and the strong Rogers isomorphism (1 file, ~724 lines)

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
Isomorphism Lemma to obtain the bijection.

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
- The strong Rogers isomorphism via `effective_myhill`.

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

## One axiom: the Myhill Isomorphism Theorem (`effective_myhill`)

**Where:** `RogersIsomorphism.lean`, line 524.

**What it says in plain language:**

Suppose you have two countable collections (like two different programming
languages) and computable one-to-one maps going each direction (a compiler
from language A to language B, and one from B to A). These compilers are
injective — different source programs produce different target programs — and
they preserve behavior (a compiled program computes the same function as the
original). Suppose also that each language has "padding": for any program and
any finite blacklist, you can always find another program that computes the
same function but isn't on the blacklist. (This is true for real programming
languages — you can always add a no-op to get a syntactically different but
semantically identical program.)

Then there exists a computable *bijection* between the two languages that
preserves behavior. Not just translations that might map multiple programs to
the same target, but a perfect one-to-one pairing.

**Is this mathematically controversial?** No. This is Myhill's Isomorphism
Theorem (1955). It appears in every recursion theory textbook: Rogers 1967
section 2.6, Soare 1987 section I.5, Cutland 1980 Ch. 7. The proof is a
standard "back-and-forth" construction: process elements 0, 1, 2, ... in
order, alternately extending the forward and backward maps, using padding to
find fresh targets when needed.

**Why is it an axiom instead of a proved theorem?** The mathematical proof is
clear, but translating it into Lean requires a specific kind of tedious work:
showing that a state machine built from list operations (looking up a key in a
list of pairs, checking if a value appears in a list, searching through
0, 1, 2, ... until you find one not in a list) composes into a single
primitive recursive function in Lean's `Primrec` type. This is ~250 lines of
mechanical API plumbing — composing `Primrec.list_find?`, `Primrec.list_mem`,
`Primrec.nat_rec`, etc. — with no mathematical content. It is engineering work
that we have not done.

**Why not use the existing Schroeder-Bernstein theorem from Mathlib?** Mathlib
has `Function.Embedding.schroeder_bernstein`, which proves that injections in
both directions give a bijection. But the bijection it constructs is defined
using `Set.piecewise` on a least-fixed-point set (computed by iterating a
set-theoretic operator) and `Function.invFun` (which picks preimages using
`Classical.choose`). This function is *genuinely not computable* — it relies
on deciding membership in a set that has no decidable characterization, and on
choosing preimages nonconstructively. The Myhill theorem requires building a
*different* function via the back-and-forth construction, which IS computable
but is not the same function as the Schroeder-Bernstein bijection.

**What depends on it:** Only `rogers_isomorphism` (the strong Rogers
isomorphism theorem). Everything else in the project — the characterization
theorem, weak Rogers isomorphism, Kleene's recursion theorem, Adamek's initial
algebra theorem, AR 2.23, the substrate-independent fixed point — is fully
proved with no custom axioms.

---

## Two sorry's: unpublished conjectures from the paper (`BoardmanVogt.lean`)

**Where:** `BoardmanVogt.lean`, lines 64 and 83.

These are not failed proofs or formalization gaps. They are *placeholders for
conjectures that the paper series proposes but that have never been proved in
any form* — not in Lean, not on paper, not anywhere. No other file in the
project depends on them.

### Sorry 1: Claim A (line 64) — the Boardman-Vogt tensor extends to partial operations

The Boardman-Vogt tensor product is a known construction for combining two
algebraic theories (like "groups" and "rings") into a theory whose models are
pairs of structures where the operations commute (like "rings" = groups +
monoids with distributivity). This is established for theories where all
operations are total (Lawvere theories).

The paper conjectures that this extends to *essentially algebraic theories*
(EATs), where operations can be partially defined (like division, which is
only defined when the denominator is nonzero). The extension is the novel
mathematical content of the paper. Nobody has proved it.

### Sorry 2: Claim A' (line 83) — the Lawvere-Linton correspondence extends

The Lawvere-Linton correspondence is a known equivalence between algebraic
theories and finitary monads on the category of sets. The paper conjectures
that this extends to EATs (yielding a correspondence with accessible monads on
locally presentable categories). Again, this is novel mathematics that has not
been proved.

### Why these cannot be formalized even if the math were settled

Mathlib has no definition of Lawvere theory, no category of Lawvere theories,
no Boardman-Vogt tensor product, no Gabriel-Ulmer duality, and no model
category infrastructure for EATs. The project's `EATheory` is a data structure
(lists of sorts and operations), not a categorical object. Stating these claims
precisely in Lean would require building model categories, term algebras,
interpretations, and satisfaction — a major infrastructure project that goes
well beyond this formalization.

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

### Computability side (fully proved except one standard axiom)

The characterization theorem (any two acceptable numberings compute the same
class of functions), the weak Rogers isomorphism (computable translations in
both directions), and Kleene's recursion theorem for abstract models are all
fully proved with no axioms.

The strong Rogers isomorphism (a computable *bijection* between any two
acceptable numberings) is proved modulo the Myhill Isomorphism Theorem, which
is taken as an axiom. The axiom is a standard, well-established result from
1955. Proving it in Lean requires ~250 lines of primitive recursive function
composition that we have not written.

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

### Target 5a: Monoidal uniqueness framework (DONE -- scaffold)

States the three-step uniqueness argument:
- Step (a): Right adjoints are unique (PROVED -- wraps `rightAdjointForcedToIHom`)
- Step (b): M = ihom of BV monoidal structure (1 sorry -- Tier 3, depends on Claim A)
- Step (c): M is unique given the monoidal structure (proved given adjunction hypothesis,
  sorry in the full pipeline due to Step b)

The categorical core (Steps a and c) is fully verified. The gap is in Step (b):
establishing that the BV tensor extends to EATs. This is the same Tier 3 gap as
`BoardmanVogt.lean`.

File: `Uniqueness/MonoidalUniqueness.lean` (204 lines).

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
| `Specification/SubstrateIndependent.lean` | 207 | 0 | 0 | Fixed point exists and is unique |
| `Uniqueness/RightAdjointUnique.lean` | 67 | 0 | 0 | Internal hom is the unique right adjoint |
| `Uniqueness/MonoidalUniqueness.lean` | 204 | 1 | 0 | Factored uniqueness (Tier 3 gap in step b) |
| `Accessibility/RightAdjointAccessible.lean` | 416 | 0 | 0 | AR 2.23: right adjoints are accessible |
| `ChurchTuring/CharacterizationTheorem.lean` | 241 | 0 | 0 | CompModel structure, characterization theorem |
| `ChurchTuring/RogersIsomorphism.lean` | 724 | 0 | 1 | Rogers isomorphism (uses Myhill axiom) |
| `Theories/EssentiallyAlgebraic.lean` | 78 | 0 | 0 | EAT data definitions |
| `Tensor/BoardmanVogt.lean` | 85 | 2 | 0 | Unpublished conjectures (placeholders) |
| `Reflexive/ReflexiveObject.lean` | 154 | 0 | 0 | Reflexive object, selfApp, curry/uncurry |
| `Reflexive/FixedPointCombinator.lean` | 208 | 0 | 0 | Categorical Y combinator (omega) |
| `Dimension/TruncationLevel.lean` | 134 | 0 | 0 | Dimension definition, iso invariance |
| `Dimension/IncrementDimension.lean` | 76 | 0 | 0 | F increments dimension by 1 |
| `Dimension/Stabilization.lean` | 114 | 0 | 0 | Dimension stabilizes at fixed point |
| `Dimension/GradedFiltration.lean` | 121 | 0 | 0 | Master graded filtration theorem |
| `Dimension/DivergenceWitnesses.lean` | 182 | 0 | 0 | FinSet divergence + thin triviality |
| `Dimension/MethodResultConvergence.lean` | 180 | 0 | 0 | Method-result convergence |
| `Dimension/ConvergenceCriterion.lean` | 121 | 0 | 0 | Convergence criterion (fwd + converse) |
| `Reflexive/KleeneBridge.lean` | 194 | 0 | 0 | T4 -> Kleene bridge |
| `Reflexive/SelfIndexedComputation.lean` | 221 | 0 | 0 | Layer 2: self-indexed computation model |
| `Reflexive/KleeneDerivation.lean` | 217 | 0 | 0 | Layer 3: N-bridge, Kleene derivation |
| `Dimension/DimensionalDissolution.lean` | 183 | 0 | 0 | Yoneda M-compatibility, dissolution |

**Total: 4730 lines of Lean across 27 files.**

- **3 sorry**: 2 in `BoardmanVogt.lean` (unpublished conjectures, Tier 3), 1 in
  `MonoidalUniqueness.lean` (Tier 3, depends on BV tensor extension). No other
  file depends on any sorry.
- **1 axiom** (`effective_myhill`): Myhill's Isomorphism Theorem (1955), a
  standard textbook result. Taken as axiom because the Lean proof requires ~250
  lines of `Primrec` composition we haven't written. Only `rogers_isomorphism`
  depends on it.

Run `./scripts/verify.sh` to reproduce these numbers.

---

## Other files

| File | Purpose |
|------|---------|
| `README.md` | Project overview |
| `Status.md` | This document |
| `scripts/verify.sh` | Build + sorry audit + axiom inventory |
