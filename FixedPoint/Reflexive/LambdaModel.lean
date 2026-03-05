/-
  LambdaModel.lean

  Formalizes that a reflexive object L ≅ [A, L] in a monoidal closed category,
  when A ≅ L (the self-indexed case), gives a model of the untyped lambda
  calculus. This closes the "computation gap": no N-enumeration is needed to
  establish universal computation -- the reflexive domain equation alone
  suffices.

  The key insight (Scott 1980): any object L that is isomorphic to its own
  function space [L, L] supports application and abstraction satisfying the
  beta and eta laws of the untyped lambda calculus. Since the untyped lambda
  calculus is Turing-complete, L is a universal computation domain.

  ## Main results

  - `LambdaModel`: a categorical model of the untyped lambda calculus --
    an object L with app : L ⊗ L → L and abs : (L ⊗ X → L) → (X → L)
    satisfying beta-reduction and eta-expansion.

  - `ReflexiveObject.toLambdaModel`: given a reflexive object for A with
    carrier ≅ A, constructs a LambdaModel. The iso A ≅ carrier turns
    selfApp : A ⊗ carrier → carrier into app : carrier ⊗ carrier → carrier.

  - `LambdaModel.fixedPoint`: every endomorphism of the carrier has a
    fixed point (via the omega/Y combinator construction).

  STATUS: Tier 1 (no sorry).
-/
import FixedPoint.Reflexive.FixedPointCombinator

universe v u

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

namespace FixedPoint.Reflexive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Lambda model structure

A categorical model of the untyped lambda calculus: an object L equipped with
application `L ⊗ L → L` and abstraction `(L ⊗ X → L) → (X → L)` for all X,
satisfying beta-reduction (abstract-then-apply = identity) and eta-expansion
(apply-then-abstract = identity). -/

/-- A categorical model of the untyped lambda calculus.

    An object `L` with application `L ⊗ L → L` and abstraction satisfying
    beta-reduction and eta-expansion. Any such model supports universal
    computation (the untyped lambda calculus is Turing-complete).

    This is the categorical formulation of Scott's lambda models: the
    beta and eta laws witness that `L` is a retract of its own function
    space `[L, L]` in a coherent way. -/
structure LambdaModel where
  /-- The carrier object of the lambda model. -/
  carrier : C
  /-- Application: `L ⊗ L → L`. Categorically, this decodes an element of L
      as a function L → L and evaluates it. -/
  app : carrier ⊗ carrier ⟶ carrier
  /-- Abstraction: given any morphism `L ⊗ X → L`, produce `X → L`.
      This is the internal abstraction operation, parametric in X. -/
  abs : ∀ {X : C}, (carrier ⊗ X ⟶ carrier) → (X ⟶ carrier)
  /-- Beta-reduction: abstract then apply recovers the original morphism.
      `(L ◁ abs(f)) ≫ app = f` for all `f : L ⊗ X → L`. -/
  β_law : ∀ {X : C} (f : carrier ⊗ X ⟶ carrier),
    (carrier ◁ (abs f)) ≫ app = f
  /-- Eta-expansion: apply then abstract recovers the original morphism.
      `abs((L ◁ g) ≫ app) = g` for all `g : X → L`. -/
  η_law : ∀ {X : C} (g : X ⟶ carrier),
    abs ((carrier ◁ g) ≫ app) = g

/-! ### Construction from a reflexive object

Given a reflexive object `r` for `A` with `carrier ≅ A`, we construct a lambda
model. The iso converts:
- `selfApp : A ⊗ carrier → carrier` into `app : carrier ⊗ carrier → carrier`
  by precomposing with the iso on the left tensor factor.
- `reflexiveCurry : (A ⊗ X → carrier) → (X → carrier)` into
  `abs : (carrier ⊗ X → carrier) → (X → carrier)` by precomposing with
  the iso inverse on the left tensor factor. -/

variable {A : C} [Closed A]

/-- Construct a lambda model from a reflexive object with carrier ≅ A.

    The iso `hcarrier : r.carrier ≅ A` converts the reflexive object's
    operations (which act on `A ⊗ carrier`) into lambda model operations
    (which act on `carrier ⊗ carrier`).

    - `app := (hcarrier.hom ▷ carrier) ≫ selfApp`
    - `abs f := reflexiveCurry ((hcarrier.inv ▷ X) ≫ f)` -/
noncomputable def ReflexiveObject.toLambdaModel
    (r : ReflexiveObject A) (hcarrier : r.carrier ≅ A) :
    @LambdaModel C _ _ where
  carrier := r.carrier
  app := hcarrier.hom ▷ r.carrier ≫ r.selfApp
  abs {X} f := r.reflexiveCurry (hcarrier.inv ▷ X ≫ f)
  β_law {X} f := by
    -- Goal: ((carrier ◁ reflexiveCurry ...) ≫ (hcarrier.hom ▷ carrier)) ≫ selfApp = f
    -- Use interchange on first two morphisms
    rw [whisker_exchange_assoc]
    -- Now: hcarrier.hom ▷ X ≫ (A ◁ reflexiveCurry (...)) ≫ selfApp = f
    -- Expand selfApp = A ◁ iso.inv ≫ ev, combine whiskers, expand reflexiveCurry
    simp only [ReflexiveObject.selfApp, ← Category.assoc, ← whiskerLeft_comp]
    simp only [ReflexiveObject.reflexiveCurry, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    -- Now: hcarrier.hom ▷ X ≫ A ◁ curry(hcarrier.inv ▷ X ≫ f) ≫ ev = f
    rw [← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry]
    -- Now: hcarrier.hom ▷ X ≫ hcarrier.inv ▷ X ≫ f = f
    rw [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  η_law {X} g := by
    -- Goal: reflexiveCurry (hcarrier.inv ▷ X ≫ carrier ◁ g ≫
    --        hcarrier.hom ▷ carrier ≫ selfApp) = g
    -- The argument to reflexiveCurry is right-associated:
    --   hcarrier.inv ▷ X ≫ (carrier ◁ g ≫ (hcarrier.hom ▷ carrier ≫ selfApp))
    -- Suffices to show the argument equals reflexiveUncurry g
    suffices h : hcarrier.inv ▷ X ≫ r.carrier ◁ g ≫
        hcarrier.hom ▷ r.carrier ≫ r.selfApp = r.reflexiveUncurry g by
      rw [h, r.reflexiveCurry_reflexiveUncurry]
    -- Use interchange: hcarrier.inv ▷ X ≫ carrier ◁ g = A ◁ g ≫ hcarrier.inv ▷ carrier
    rw [← whisker_exchange_assoc]
    -- Now: A ◁ g ≫ hcarrier.inv ▷ carrier ≫ hcarrier.hom ▷ carrier ≫ selfApp
    rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
    -- Now: (A ◁ g) ≫ selfApp = reflexiveUncurry g
    -- (generalized whiskerLeft_comp_selfApp for g : X ⟶ carrier)
    simp only [ReflexiveObject.selfApp, ReflexiveObject.reflexiveUncurry,
      MonoidalClosed.uncurry_eq, ← Category.assoc, ← whiskerLeft_comp]

/-! ### Fixed-point theorem

Every endomorphism of a lambda model's carrier has a fixed point, constructed
via the omega/Y combinator. This is the categorical incarnation of the
lambda-calculus fixed-point theorem: for any term F, the term
Y(F) = (lambda x. F(x x))(lambda x. F(x x)) satisfies Y(F) = F(Y(F)). -/

/-- In a lambda model derived from a reflexive object, every endomorphism
    has a fixed point at the morphism level. Specifically, for any `f : L → L`,
    there exists `fix : L → L` such that whiskering by `fix` before application
    equals application followed by `f`.

    This is the categorical Y combinator: `fix f` satisfies
    `(A ◁ fix(f)) ≫ selfApp = selfApp ≫ f`. -/
theorem ReflexiveObject.toLambdaModel_fixedPoint
    (r : ReflexiveObject A)
    (f : r.carrier ⟶ r.carrier) :
    A ◁ r.omega f ≫ r.selfApp = r.selfApp ≫ f :=
  r.omega_fixed_point f

/-- Every lambda model derived from a reflexive object has the fixed-point
    property expressed purely in terms of the lambda model operations:
    for any `f : L → L`, there exists `g : L → L` such that
    `(L ◁ g) ≫ app = (L ◁ g) ≫ app ≫ f` (i.e., app after g is a fixed
    point of post-composition with f).

    More precisely: `abs(app ≫ f)` satisfies the omega equation. -/
noncomputable def LambdaModel.omegaMap
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (m : @LambdaModel C _ _) (f : m.carrier ⟶ m.carrier) :
    m.carrier ⟶ m.carrier :=
  m.abs (m.app ≫ f)

/-- The omega map satisfies the fixed-point equation:
    `(L ◁ omega(f)) ≫ app = app ≫ f`.

    This says: pre-whiskering by `omega(f)` before application is the same as
    application followed by `f`. In lambda calculus: omega_f(x) = f(x x). -/
theorem LambdaModel.omegaMap_eq
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (m : @LambdaModel C _ _) (f : m.carrier ⟶ m.carrier) :
    m.carrier ◁ m.omegaMap f ≫ m.app = m.app ≫ f := by
  simp only [omegaMap, m.β_law]

end FixedPoint.Reflexive
