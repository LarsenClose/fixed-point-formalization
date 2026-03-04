/-
  FixedPointCombinator.lean

  Constructs the categorical fixed-point combinator (Y combinator) from a
  reflexive object and proves the fixed-point property at the morphism level.

  Given a reflexive object L with Lambek isomorphism phi : [A, L] ≅ L, the
  untyped-lambda-calculus Y combinator Y = lambda f. (lambda x. f(x x))(lambda x. f(x x))
  translates into categorical morphisms.

  ## Main results

  - `ReflexiveObject.omega f` -- the categorical analogue of (lambda x. f(x x)):
    given f : L --> L, curries `selfApp >> f : A tensor L --> L` through the
    reflexive iso to obtain `omega f : L --> L`.

  - `ReflexiveObject.omega_fixed_point` -- the categorical fixed-point equation:
      `A left-whisker (omega f) >> selfApp = selfApp >> f`
    This says: transforming the L-input by omega_f before self-application
    is the same as self-applying and then applying f. In lambda calculus
    notation: omega_f(x) = f(x(x)).

  - `ReflexiveObject.whiskerLeft_comp_selfApp` -- the bridge lemma:
      `A left-whisker g >> selfApp = reflexiveUncurry g`
    for any g : L --> L.

  The composition `omega f >> omega f` (the categorical analogue of
  omega_f(omega_f) = Y(f)) is also defined as `omegaSq`. While Y(f) as a
  global point of L would require a point of A, the morphism-level equation
  `omega_fixed_point` fully captures the fixed-point semantics.

  STATUS: Tier 1 (no sorry).
-/
import FixedPoint.Reflexive.ReflexiveObject

universe v u

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

namespace FixedPoint.Reflexive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A : C} [Closed A]

/-! ### The omega construction: lambda x. f(x x)

Given an endomorphism `f : L --> L` on the carrier of a reflexive object,
`omega f` is the categorical analogue of `lambda x. f(x x)` -- it curries
the composition `selfApp >> f : A tensor L --> L` through the reflexive
iso. -/

/-- The omega map: given `f : L --> L`, produce the categorical
    analogue of `lambda x. f(x x)` as a morphism `L --> L`.

    Construction: `selfApp >> f : A tensor L --> L` is curried via
    the reflexive iso to give `L --> L`. -/
noncomputable def ReflexiveObject.omega (r : ReflexiveObject A)
    (f : r.carrier ⟶ r.carrier) : r.carrier ⟶ r.carrier :=
  r.reflexiveCurry (r.selfApp ≫ f)

/-! ### Unfolding equations for omega -/

/-- Unfolding: applying `omega f` via reflexive uncurry recovers
    `selfApp >> f`. This is the key computational identity:
    the "meaning" of omega_f is self-apply-then-apply-f. -/
theorem ReflexiveObject.reflexiveUncurry_omega
    (r : ReflexiveObject A) (f : r.carrier ⟶ r.carrier) :
    r.reflexiveUncurry (r.omega f) = r.selfApp ≫ f := by
  simp only [omega, reflexiveUncurry_reflexiveCurry]

/-- `omega f` unfolds as the reflexive curry of `selfApp >> f`. -/
theorem ReflexiveObject.omega_eq (r : ReflexiveObject A)
    (f : r.carrier ⟶ r.carrier) :
    r.omega f = r.reflexiveCurry (r.selfApp ≫ f) :=
  rfl

/-- `omega` of the identity is the reflexive curry of `selfApp`. -/
theorem ReflexiveObject.omega_id (r : ReflexiveObject A) :
    r.omega (𝟙 r.carrier) = r.reflexiveCurry r.selfApp := by
  simp only [omega, Category.comp_id]

/-- `omega` respects composition in the second argument. -/
theorem ReflexiveObject.omega_comp (r : ReflexiveObject A)
    (f g : r.carrier ⟶ r.carrier) :
    r.omega (f ≫ g) =
      r.reflexiveCurry (r.selfApp ≫ f ≫ g) := by
  simp only [omega]

/-! ### Whisker-selfApp lemma

A general lemma: left-whiskering any morphism `g : L --> L` by A before
self-application is the same as reflexive uncurrying. This is the bridge
between the "external" composition `A left-whisker g >> selfApp` and the
"internal" reflexive uncurry operation. -/

/-- Whiskering `g : L --> L` before selfApp equals reflexive
    uncurrying g: `A left-whisker g >> selfApp = reflexiveUncurry g`.

    Proof: both sides expand to
    `A left-whisker (g >> iso.inv) >> ev`. -/
theorem ReflexiveObject.whiskerLeft_comp_selfApp
    (r : ReflexiveObject A) (g : r.carrier ⟶ r.carrier) :
    A ◁ g ≫ r.selfApp = r.reflexiveUncurry g := by
  simp only [selfApp, reflexiveUncurry, MonoidalClosed.uncurry_eq,
    ← Category.assoc, ← whiskerLeft_comp]

/-- `reflexiveUncurry` equals whiskering then selfApp. -/
theorem ReflexiveObject.reflexiveUncurry_eq_whiskerLeft_selfApp
    (r : ReflexiveObject A) (g : r.carrier ⟶ r.carrier) :
    r.reflexiveUncurry g = A ◁ g ≫ r.selfApp := by
  rw [whiskerLeft_comp_selfApp]

/-- `selfApp` is `reflexiveUncurry` of the identity. -/
theorem ReflexiveObject.selfApp_eq_reflexiveUncurry_id
    (r : ReflexiveObject A) :
    r.selfApp = r.reflexiveUncurry (𝟙 r.carrier) := by
  simp only [reflexiveUncurry_eq_whiskerLeft_selfApp,
    whiskerLeft_id, Category.id_comp]

/-! ### The categorical fixed-point equation

The main theorem of this file: for any endomorphism f of the carrier L,
whiskering omega_f before self-application recovers self-application
followed by f. This is the categorical incarnation of the lambda-calculus
identity omega_f(x) = f(x(x)). -/

/-- **Fixed-point equation (morphism level).**
    For any endomorphism `f : L --> L`:

      `A left-whisker (omega f) >> selfApp = selfApp >> f`

    Left side: transform the L-input by omega_f, then self-apply.
    Right side: self-apply, then apply f.

    This is the categorical Y combinator equation: it says that
    omega_f acts as a fixed point of "post-compose with f" on the
    self-application morphism. In lambda calculus notation:
    omega_f(x) = f(x(x)). -/
theorem ReflexiveObject.omega_fixed_point
    (r : ReflexiveObject A) (f : r.carrier ⟶ r.carrier) :
    A ◁ r.omega f ≫ r.selfApp = r.selfApp ≫ f := by
  rw [whiskerLeft_comp_selfApp, reflexiveUncurry_omega]

/-! ### Omega and the Lambek isomorphism -/

/-- Composing omega_f with the Lambek iso inverse recovers the
    standard curry of `selfApp >> f`. -/
theorem ReflexiveObject.omega_comp_iso_inv
    (r : ReflexiveObject A) (f : r.carrier ⟶ r.carrier) :
    r.omega f ≫ r.iso.inv =
      MonoidalClosed.curry (r.selfApp ≫ f) := by
  simp only [omega, reflexiveCurry, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-! ### Double omega (Y combinator at the morphism level)

The composition `omega f >> omega f : L --> L` is the categorical
analogue of `omega_f(omega_f)`, which in the lambda calculus equals
Y(f). While a global point `unit --> L` would require choosing a
point of A, the endomorphism `omegaSq f` captures the same
algebraic content. -/

/-- Double omega: `omega f >> omega f` is the categorical analogue
    of applying `lambda x. f(x x)` to itself, yielding the Y
    combinator Y(f) = omega_f(omega_f) at the morphism level. -/
noncomputable def ReflexiveObject.omegaSq (r : ReflexiveObject A)
    (f : r.carrier ⟶ r.carrier) : r.carrier ⟶ r.carrier :=
  r.omega f ≫ r.omega f

/-- Reflexive uncurry of `omegaSq f` equals `selfApp >> f >> f`.

    This is the categorical analogue of the unfolding:
    Y(f)(x) = omega_f(omega_f)(x) = f(omega_f(omega_f))(x)
            = f(f(...)) applied to the self-application of x. -/
theorem ReflexiveObject.reflexiveUncurry_omegaSq
    (r : ReflexiveObject A) (f : r.carrier ⟶ r.carrier) :
    r.reflexiveUncurry (r.omegaSq f) =
      r.selfApp ≫ f ≫ f := by
  rw [omegaSq]
  simp only [reflexiveUncurry_eq_whiskerLeft_selfApp,
    whiskerLeft_comp]
  rw [Category.assoc, omega_fixed_point,
    ← Category.assoc, omega_fixed_point, Category.assoc]

/-- `omegaSq f` is omega of `f >> f` at the uncurried level. That is,
    the reflexive uncurry of `omegaSq f` equals the reflexive uncurry
    of `omega (f >> f)`.

    This captures the recursive unfolding: Y(f) = f(Y(f)) means that
    applying Y to f at depth 2 is the same as omega applied to f^2. -/
theorem ReflexiveObject.reflexiveUncurry_omegaSq_eq
    (r : ReflexiveObject A) (f : r.carrier ⟶ r.carrier) :
    r.reflexiveUncurry (r.omegaSq f) =
      r.reflexiveUncurry (r.omega (f ≫ f)) := by
  rw [reflexiveUncurry_omegaSq, reflexiveUncurry_omega]

/-- For the identity, `omegaSq id` has the same reflexive uncurry
    as the identity itself (modulo selfApp). -/
theorem ReflexiveObject.reflexiveUncurry_omegaSq_id
    (r : ReflexiveObject A) :
    r.reflexiveUncurry (r.omegaSq (𝟙 r.carrier)) =
      r.selfApp := by
  rw [reflexiveUncurry_omegaSq, Category.comp_id,
    Category.comp_id]

end FixedPoint.Reflexive
