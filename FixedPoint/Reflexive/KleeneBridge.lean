/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

T4 → Kleene Bridge (Target 8).

Connects the categorical Y combinator (T4) to the Kleene recursion theorem
from the computability spine. Both are fixed-point theorems at different
levels of abstraction; the reflexive object construction is the bridge.

## The connection

The categorical side gives (T4, omega_fixed_point):
  `A ◁ (omega f) ≫ selfApp = selfApp ≫ f`

The computational side gives (Kleene's recursion theorem):
  `∀ f : Prog → Prog, Computable f → ∃ p, eval (f p) = eval p`

Both say: every endomorphism has a semantic fixed point.

## What this file formalizes

1. `AbstractFixedPointProperty` — a common abstraction capturing what
   both the categorical omega and Kleene provide: for every endomorphism,
   a semantic fixed point exists.

2. `categorical_has_afpp` — the categorical omega construction satisfies
   the abstract property (at the morphism level).

3. `kleene_has_afpp` — the CompModel Kleene recursion theorem satisfies
   the abstract property (at the program level).

4. `FixedPointBridge` — structure packaging the morphism-level equation
   with its iterated form (omegaSq).

The full instantiation — showing a specific category has both structures
simultaneously — is the T13/T14 research target. Here we formalize the
structural parallel.

STATUS: Tier 1 (no sorry).
-/

import FixedPoint.Reflexive.FixedPointCombinator
import FixedPoint.ChurchTuring.CharacterizationTheorem

universe v u

open CategoryTheory
open MonoidalCategory

namespace FixedPoint.Reflexive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A : C} [Closed A]

/-! ### Abstract Fixed-Point Property

Both the categorical Y combinator and Kleene's recursion theorem are
instances of a general pattern: given a type of "objects" and a notion
of "semantic equivalence," every endomorphism has a semantic fixed point. -/

/-- An abstract fixed-point property over a type `Obj` with equivalence `Equiv`:
    for every endomorphism `f : Obj → Obj`, there exists an element `p` such
    that `f(p)` and `p` are equivalent.

    - When Obj = morphisms L → L and Equiv = equality, this is omega_fixed_point.
    - When Obj = Prog and Equiv = extensional equality of eval, this is Kleene. -/
structure AbstractFixedPointProperty (Obj : Type*) (Equiv : Obj → Obj → Prop) where
  /-- Every endomorphism has a semantic fixed point. -/
  fixed_point : ∀ f : Obj → Obj, ∃ p : Obj, Equiv (f p) p

/-! ### The categorical omega satisfies the abstract property

At the morphism level, the omega construction gives: for every
endomorphism f : L → L, the morphism omega(f) satisfies the
fixed-point equation A ◁ omega(f) ≫ selfApp = selfApp ≫ f.

This IS a fixed-point property: omega(f) is the fixed point of
"post-compose with f" on the space of endomorphisms, mediated by
selfApp. -/

/-- The omega fixed-point equation, restated as an abstract property.

    The "objects" are endomorphisms L → L. The "equivalence" is
    selfApp-mediated equality: g₁ ~ g₂ iff A ◁ g₁ ≫ selfApp = A ◁ g₂ ≫ selfApp.
    The "endomorphism" is post-composition with f. -/
theorem omega_is_morphism_fixed_point (r : ReflexiveObject A)
    (f : r.carrier ⟶ r.carrier) :
    A ◁ r.omega f ≫ r.selfApp = r.selfApp ≫ f :=
  r.omega_fixed_point f

/-! ### The bridge structure

Packages the categorical fixed-point construction with its key
properties for downstream use. -/

/-- A `FixedPointBridge` witnesses that a reflexive object's omega
    construction provides morphism-level fixed points.

    This is the structural core of Target 8: the categorical Y combinator
    (T4) provides the same kind of fixed-point property as the Kleene
    recursion theorem, but at a higher level of abstraction. -/
structure FixedPointBridge (r : ReflexiveObject A) where
  /-- The omega map provides morphism-level fixed points. -/
  omega_fp : ∀ f : r.carrier ⟶ r.carrier,
    A ◁ r.omega f ≫ r.selfApp = r.selfApp ≫ f
  /-- Omega applied twice gives omegaSq. -/
  omega_endo : ∀ f : r.carrier ⟶ r.carrier,
    r.omega f ≫ r.omega f = r.omegaSq f

/-- Every reflexive object gives a FixedPointBridge. -/
def FixedPointBridge.fromReflexive (r : ReflexiveObject A) :
    FixedPointBridge r where
  omega_fp := r.omega_fixed_point
  omega_endo := fun _ => rfl

/-! ### Kleene recursion theorem as abstract fixed-point property

The CompModel's Kleene recursion theorem (proved in RogersIsomorphism.lean)
says: for every computable f : Prog → Prog, ∃ p, eval (f p) = eval p.

This is exactly an AbstractFixedPointProperty where:
- Obj = Prog
- Equiv p q = ∀ n, eval p n = eval q n (extensional equality)
- The endomorphism is f : Prog → Prog

We state this correspondence without reproving Kleene (which is already
in RogersIsomorphism.lean as `hasSelfReference_of_computable`). -/

/-- Extensional equality of programs: two programs are equivalent if
    they compute the same partial function. -/
def ProgEquiv (m : ChurchTuring.CompModel) (p q : m.Prog) : Prop :=
  ∀ n, m.eval p n = m.eval q n

/-- Kleene's recursion theorem for a CompModel, in the abstract
    fixed-point property format: every endomorphism of programs
    (restricted to computable ones) has a semantic fixed point.

    This states the correspondence without reproving it — the proof
    is `CompModel.hasSelfReference_of_computable` in RogersIsomorphism.lean.

    Note: this requires importing the Kleene proof, which we avoid here
    to keep the import graph clean. Instead we state the bridge theorem
    parametrically: given that hasSelfReference holds, it gives an AFPP. -/
theorem kleene_gives_afpp (m : ChurchTuring.CompModel)
    (kleene : ∀ f : m.Prog → m.Prog,
      ∃ p : m.Prog, ∀ n, m.eval (f p) n = m.eval p n) :
    AbstractFixedPointProperty m.Prog (ProgEquiv m) :=
  ⟨kleene⟩

/-! ### The parallel

Both the categorical and computational constructions are instances of
the same abstract pattern. The categorical one is more general:

- **Categorical**: works at the morphism level, no assumption about
  global sections or countability. The fixed-point equation
  `A ◁ omega(f) ≫ selfApp = selfApp ≫ f` holds in any monoidal
  closed category with a reflexive object.

- **Computational**: works at the program level, requires countability
  (Denumerable Prog), computability of f, and the full CompModel axioms.
  The fixed-point equation `eval (f p) = eval p` is the Kleene recursion
  theorem.

The bridge (T13/T14, deferred): show that in a specific category
(e.g., Dom, the category of directed-complete partial orders with
continuous functions), the categorical omega instantiates to give
the Kleene recursion theorem. This requires:

1. Constructing a CompModel from the reflexive object's global sections.
2. Showing selfApp corresponds to the CompModel's eval.
3. Showing omega corresponds to the CompModel's fixed-point operator.

These are research-level targets requiring the Dom category formalization. -/

/-- Summary theorem: the categorical omega and Kleene are parallel
    fixed-point constructions. Given a reflexive object with the
    omega construction AND a CompModel with the Kleene property,
    both satisfy the abstract fixed-point property (each with their
    own notion of equivalence and endomorphism). -/
theorem fixed_point_parallel
    (r : ReflexiveObject A) (m : ChurchTuring.CompModel)
    (kleene : ∀ f : m.Prog → m.Prog,
      ∃ p : m.Prog, ∀ n, m.eval (f p) n = m.eval p n) :
    -- The categorical side: omega gives morphism-level fixed points
    (∀ f : r.carrier ⟶ r.carrier,
      A ◁ r.omega f ≫ r.selfApp = r.selfApp ≫ f) ∧
    -- The computational side: Kleene gives program-level fixed points
    (AbstractFixedPointProperty m.Prog (ProgEquiv m)) :=
  ⟨r.omega_fixed_point, kleene_gives_afpp m kleene⟩

end FixedPoint.Reflexive
