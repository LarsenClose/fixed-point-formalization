# Project Status: Fixed-Point Formalization

Lean 4 v4.28.0 / Mathlib v4.28.0. Last updated: 2026-03-03.

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

### Uniqueness of the right adjoint (1 file, ~120 lines)

**What it says:** In a monoidal closed category, the internal hom functor
ihom(A) is the unique (up to natural isomorphism) right adjoint to the tensor
product functor (- tensor A). Furthermore, the unit of the adjunction is
determined by the adjunction. So there is no freedom in choosing the internal
hom -- the monoidal structure forces it.

**What we proved in Lean:** Using Mathlib's `Adjunction.rightAdjointUniq`, the
endofunctor is unique and the unit coherence follows.

File: `RightAdjointUnique.lean`.

### Finite set divergence (1 file, ~80 lines)

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

### The substrate-independent specification (1 file, ~180 lines)

**What it says:** In any monoidal closed, locally presentable category (a
"substrate category"), the internal hom endofunctor ihom(A) has an initial
algebra, and that initial algebra is a fixed point (by Lambek) and is unique
(by initiality).

**What we proved in Lean:** The specification compiles and the existence
theorem is stated. The existence proof calls the Adamek theorem proved above.
Uniqueness is fully proved.

**The catch:** The existence theorem carries an explicit hypothesis:
`[PreservesColimit (initialChain (ihom A)) (ihom A)]`. This says the internal
hom functor preserves the colimit of the specific chain we constructed.
Everything downstream of this hypothesis is proved. The hypothesis itself is
not discharged from the substrate category assumptions alone. See "Gap 1"
below for why.

File: `SubstrateIndependent.lean`.

### The Church-Turing characterization theorem (1 file, ~230 lines)

**What it says:** Define a "computation model" (called `CompModel`) as an
acceptable numbering: a countable type of programs with an evaluation function,
where (a) every program computes a partial recursive function
(representability), (b) every partial recursive function is computed by some
program (universality), (c) the evaluation function is itself partial recursive
as a function of both the program index and the input (uniform computability),
and (d) there is a computable currying function (the s-m-n theorem).

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

### Weak Rogers isomorphism and Kleene's recursion theorem (1 file, ~500 lines)

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

**What we proved in Lean:**

- Computable translations between any two models (`compTranslate`), with
  computability and evaluation-preservation proved. The construction: use
  `eval_partrec` to get a Code computing model 1's evaluation, use model 2's
  `universal` to get a program in model 2 simulating that Code, then use
  model 2's `smn` to curry.
- The weak Rogers isomorphism assembling both directions.
- Kleene's recursion theorem derived from the CompModel axioms (not from
  Mathlib's `Code.fixed_point` -- the proof is internal to the abstract model).
- `ComputableIso` shown to be an equivalence relation (reflexive, symmetric,
  transitive).

File: `RogersIsomorphism.lean`.

### Adamek-Rosicky Theorem 2.23 (1 file, ~400 lines)

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

**The catch:** See Gap 1 below -- this theorem proves G is accessible at
*some* cardinal kappa', but kappa' might be larger than aleph_0, and the
Adamek initial algebra theorem we proved uses omega-indexed (= aleph_0) chains.

File: `RightAdjointAccessible.lean`.

---

## What is NOT proved (sorry'd)

### Gap 1: The bridge from "accessible at kappa'" to "preserves omega-chains"

**Where:** `RightAdjointAccessible.lean`, line 381.
`ihom_preservesColimitsOfShape_nat` is sorry'd.

**The problem in plain language:**

We proved that the internal hom functor ihom(A) is accessible -- it preserves
kappa'-filtered colimits for some regular cardinal kappa'. But kappa' might be
bigger than aleph_0 (countable infinity). The natural numbers, viewed as a
directed system, are only aleph_0-filtered. A diagram indexed by the natural
numbers is NOT kappa'-filtered when kappa' > aleph_0, because the natural
numbers have subsets of size aleph_0 with no upper bound (the whole thing),
and kappa'-filtered means every subset of size less than kappa' has an upper
bound. When kappa' > aleph_0, this condition is vacuously satisfied for finite
subsets but FAILS for the countably infinite subset {0, 1, 2, ...}.

So "preserves kappa'-filtered colimits" does NOT imply "preserves the colimit
of the omega-chain" unless kappa' = aleph_0.

**Why it matters:** The Adamek initial algebra theorem we proved uses the
omega-chain (natural-number-indexed). The colimit of that chain is the fixed
point. If ihom(A) does not preserve that specific colimit, the Adamek theorem
does not apply.

**How it could be closed:**

(a) **Assume locally finitely presentable** (kappa = aleph_0). Then if
    the left adjoint (tensorLeft A) sends finitely presentable objects to
    finitely presentable objects, the right adjoint would be
    aleph_0-accessible, which would give preservation of all filtered colimits,
    including omega-chains. However, "tensorLeft A preserves finite
    presentability" is itself a non-trivial property that would need proof.

(b) **Generalize to transfinite Adamek.** Instead of iterating along the
    natural numbers, iterate along ordinal kappa' (or a suitable well-ordered
    type of cardinality kappa'). The colimit of a kappa'-length chain IS
    kappa'-filtered, so the kappa'-accessible functor preserves it. Mathlib
    has the transfinite iteration infrastructure (`SuccStruct` works for any
    well-ordered type), but connecting kappa'-indexed chains to
    kappa'-filteredness requires showing that the ordinal kappa' (as a
    category) is kappa'-filtered. This is true but not in Mathlib.

(c) **Keep the explicit hypothesis.** This is the current approach. The
    hypothesis `[PreservesColimit (initialChain (ihom A)) (ihom A)]` in
    `SubstrateIndependent.lean` is the honest statement: we need this
    property and cannot derive it from the substrate category assumptions
    alone. Everything else is proved.

**Bottom line:** AR 2.23 is proved but does not plug the hole it was designed
for. The gap is between general accessibility (at some possibly large
cardinal) and the specific preservation property the Adamek theorem needs
(preservation of one specific omega-chain colimit). Closing this gap requires
either restricting to locally finitely presentable categories (approach a),
generalizing the Adamek theorem to transfinite chains (approach b), or
accepting the explicit hypothesis (approach c, current status).

### Gap 2: The strong Rogers isomorphism

**Where:** `RogersIsomorphism.lean`, line 363.
`rogers_isomorphism` is sorry'd.

**The problem in plain language:**

The weak Rogers isomorphism gives computable translations in both directions
between any two computation models. But these translations are not bijections.
Many different programs compute the same partial function, and the translation
might map program p to program q, but the reverse translation might map q to
some program r different from p (even though r computes the same function as
p).

The strong Rogers isomorphism says there exists a computable *bijection*
between the program types that preserves evaluation. Not just translations
that are surjective on equivalence classes, but an actual one-to-one
correspondence.

The classical proof (Rogers 1967) uses a back-and-forth construction:
process natural numbers 0, 1, 2, ... in order. At even stages, extend the
forward map; at odd stages, extend the backward map. At each stage, use the
"padding lemma" (every partial function has infinitely many programs computing
it) to find a fresh target that is extensionally equivalent. The construction
is made computable by using Kleene's recursion theorem to handle the
self-reference (the function being built needs to query its own prior outputs).

**Why it cannot be closed right now:**

1. The CompModel axioms do not guarantee that every partial function has
   infinitely many programs computing it (the "padding" or "infinite fibers"
   property). For Mathlib's Code type this is true (you can syntactically pad
   any Code to get infinitely many distinct Codes computing the same function),
   but the abstract CompModel axioms (universal, representable, smn,
   eval_partrec) do not imply it. The current smn function gives programs
   computing *different* functions (with different curried arguments), not
   multiple programs for the *same* function.

2. Even with padding, the back-and-forth construction requires encoding finite
   partial bijections as natural numbers and showing the resulting stage
   function is partial recursive. This is technically feasible (lists of pairs
   are encodable in Mathlib) but involves several hundred lines of encoding
   work.

**What would be needed:** Either add an explicit "padding" axiom to CompModel
(every function has infinitely many programs, computably enumerable), or prove
that the existing axioms imply it (which they likely do not in full
generality). Then implement the back-and-forth construction (~500 lines).

### Gap 3: The Boardman-Vogt tensor product on essentially algebraic theories

**Where:** `BoardmanVogt.lean`, lines 64 and 83. Two sorry'd claims.

**The problem in plain language:**

The paper series claims that the category of essentially algebraic theories
(EATs) carries a monoidal closed structure via the Boardman-Vogt tensor
product. This tensor product, for two theories T1 and T2, produces a theory
whose models are pairs (M1, M2) where M1 is a T1-model and M2 is a T2-model,
and the two structures "commute" in an appropriate sense.

For ordinary (total) algebraic theories (= Lawvere theories), this is a known
result due to Boardman-Vogt (1968) and Nishizawa-Power (2009). The paper claims
it extends to EATs, which allow partially defined operations.

**Why it cannot be formalized:**

1. **No Lawvere theories in Mathlib.** Mathlib has no definition of Lawvere
   theory, no category of Lawvere theories, no tensor product on them.

2. **No Gabriel-Ulmer duality in Mathlib.** The theorem that categories of
   models of EATs are exactly the locally finitely presentable categories is
   not in Mathlib, not close to being in Mathlib, and there are no open PRs
   targeting it.

3. **The EAT definition in the project is a data structure, not a categorical
   object.** `EATheory` is defined as lists of sorts, operations, and domain
   conditions. There is no notion of "model of an EAT," no model category, and
   hence no way to even state the Boardman-Vogt claims precisely in Lean.
   Making them precise requires defining term algebras, interpretations,
   satisfaction, and the category of models -- a major undertaking.

4. **The claims are mathematically conjectural.** Even in the paper, these are
   presented as claims to be established, not as known theorems with citations.
   The extension from Lawvere theories to EATs is the novel mathematical
   content.

**Bottom line:** These sorries are intentional. They represent the frontier of
the mathematical work, not formalization gaps. They are isolated in a single
file that nothing else depends on.

---

## What the gaps mean for the project's claims

The project's verified core is:

> In any monoidal closed, locally presentable category, **given that the
> internal hom functor preserves the colimit of the initial chain**, the
> internal hom endofunctor has a fixed point that is unique up to isomorphism.

The "given that" clause is the Gap 1 hypothesis. Without it, the statement is
conditional. The mathematical community knows the condition holds (it follows
from accessibility plus either locally-finite-presentability or transfinite
generalization), but the Lean formalization does not derive it from first
principles.

The Church-Turing side is in better shape. The characterization theorem and
weak Rogers isomorphism are fully proved. The strong Rogers isomorphism
(actual computable bijection) requires either new axioms on CompModel or ~500
lines of new proof.

The EAT / Boardman-Vogt layer is nowhere near being formalized and depends on
infrastructure that does not exist in Mathlib and has no near-term prospect of
being added.

---

## File inventory

| File | Lines | Sorry | Status |
|------|-------|-------|--------|
| `Iteration/InitialChain.lean` | ~120 | 0 | Clean |
| `Iteration/ChainShift.lean` | ~100 | 0 | Clean |
| `Iteration/AdamekTheorem.lean` | ~200 | 0 | Clean |
| `Iteration/AdamekConnection.lean` | ~80 | 0 | Clean |
| `Iteration/AdamekChain.lean` | ~100 | 0 | Clean |
| `Iteration/FinSetDivergence.lean` | ~80 | 0 | Clean |
| `Specification/SubstrateIndependent.lean` | ~180 | 0 | Clean (hypothesis carried) |
| `Uniqueness/RightAdjointUnique.lean` | ~120 | 0 | Clean |
| `Accessibility/RightAdjointAccessible.lean` | ~400 | 1 | Gap 1 |
| `ChurchTuring/CharacterizationTheorem.lean` | ~230 | 0 | Clean |
| `ChurchTuring/RogersIsomorphism.lean` | ~500 | 1 | Gap 2 |
| `Theories/EssentiallyAlgebraic.lean` | ~80 | 0 | Clean (data definitions only) |
| `Tensor/BoardmanVogt.lean` | ~90 | 2 | Gap 3 (intentional) |
| `Basic.lean` | 1 | 0 | Placeholder |
| `UnivTest.lean` | ~40 | 0 | Test file |

**Total: ~2400 lines of Lean. 4 sorry. 0 axioms.**

---

## Docs inventory

| File | Purpose | Current? |
|------|---------|----------|
| `docs/AR_THEOREM_PLAN.md` | Proof plan for AR 2.23 | Yes (plan completed, theorem proved) |
| `docs/lean-mcp-tools.md` | MCP tool reference for Lean development | Yes |
| `docs/alternative-approaches-computability.md` | Analysis of CompModel design choices | Yes (approach d was adopted) |
| `docs/alternative-approaches-ct.md` | Analysis of Gap 1/2/3 approaches | Yes |
| `MATHLIB_PR_PLAN.md` | Plan for upstreaming Adamek theorem to Mathlib | Yes |
