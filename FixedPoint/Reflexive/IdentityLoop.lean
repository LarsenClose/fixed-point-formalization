/-
  IdentityLoop.lean

  Packages the three identity equations of a reflexive object into a single
  structure, making explicit that identity modulation (fold/unfold via the
  Lambek iso) constitutes the computational core of the reflexive structure.

  In a reflexive object with L ≅ [A, L], three equations about the identity
  morphism form a closed loop:

  1. selfApp = reflexiveUncurry(𝟙_L)   -- evaluation IS the uncurrying of identity
  2. omega(𝟙_L) = reflexiveCurry(selfApp) -- the quine IS the currying of evaluation
  3. fold(unfold(id)) = id, unfold(fold(selfApp)) = selfApp -- round-trip coherence

  ## Main results

  - `IdentityLoop` -- structure packaging the four identity-modulation equations
  - `ReflexiveObject.identityLoop` -- canonical construction from any reflexive object
  - `IdentityLoop.quine` -- the self-recognition element omega(𝟙)
  - `IdentityLoop.quine_self_recognition` -- A ◁ quine ≫ selfApp = selfApp
  - `IdentityLoop.computation_from_identity` -- all omega(f) arise from identity modulation

  STATUS: Tier 1 (no sorry).
-/
import FixedPoint.Reflexive.FixedPointCombinator

universe v u

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

namespace FixedPoint.Reflexive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A : C} [Closed A]

/-- The identity loop of a reflexive object: four equations witnessing that
    identity modulation (fold/unfold via the Lambek iso) constitutes the
    computational core of the reflexive structure.

    - selfApp is identity unfolded (uncurried)
    - The quine (omega of id) is selfApp folded (curried)
    - These form a closed loop: fold(unfold(id)) = id, unfold(fold(selfApp)) = selfApp

    The quine omega(𝟙) is the self-recognition element: L contains, as a datum,
    the act of running itself. -/
structure IdentityLoop (r : ReflexiveObject A) where
  /-- Evaluation is identity unfolded. -/
  eval_is_unfold : r.selfApp = r.reflexiveUncurry (𝟙 r.carrier)
  /-- The quine is evaluation folded. -/
  quine_is_fold : r.omega (𝟙 r.carrier) = r.reflexiveCurry r.selfApp
  /-- Identity modulation: fold after unfold recovers identity.
      reflexiveCurry(reflexiveUncurry(𝟙)) = 𝟙 -/
  fold_unfold_id : r.reflexiveCurry (r.reflexiveUncurry (𝟙 r.carrier)) = 𝟙 r.carrier
  /-- Identity modulation: unfold after fold recovers selfApp.
      reflexiveUncurry(reflexiveCurry(selfApp)) = selfApp -/
  unfold_fold_eval : r.reflexiveUncurry (r.reflexiveCurry r.selfApp) = r.selfApp

/-- Every reflexive object has an identity loop. -/
noncomputable def ReflexiveObject.identityLoop (r : ReflexiveObject A) : IdentityLoop r where
  eval_is_unfold := r.selfApp_eq_reflexiveUncurry_id
  quine_is_fold := r.omega_id
  fold_unfold_id := r.reflexiveCurry_reflexiveUncurry (𝟙 r.carrier)
  unfold_fold_eval := r.reflexiveUncurry_reflexiveCurry r.selfApp

/-- The quine: the self-recognition element of L. This is omega(𝟙),
    which when run through selfApp, acts as selfApp itself.
    L contains, as a datum, the act of evaluating itself. -/
noncomputable def IdentityLoop.quine {r : ReflexiveObject A} (_ : IdentityLoop r) :
    r.carrier ⟶ r.carrier :=
  r.omega (𝟙 r.carrier)

/-- The quine's defining property: whiskering it before selfApp gives selfApp.
    The self-recognition element, when evaluated, evaluates everything the same
    way as direct evaluation. omega(𝟙) is a fixed point of identity under
    the selfApp-mediated equivalence. -/
theorem IdentityLoop.quine_self_recognition {r : ReflexiveObject A} (il : IdentityLoop r) :
    A ◁ il.quine ≫ r.selfApp = r.selfApp := by
  have h := r.omega_fixed_point (𝟙 r.carrier)
  simp only [Category.comp_id] at h
  exact h

/-- Every endomorphism's fixed point is generated from identity modulation.
    omega(f) = reflexiveCurry(selfApp ≫ f) = reflexiveCurry(reflexiveUncurry(𝟙) ≫ f).
    All computation (fixed points of arbitrary transformations) is identity,
    unfolded, then post-composed. -/
theorem IdentityLoop.computation_from_identity {r : ReflexiveObject A} (il : IdentityLoop r)
    (f : r.carrier ⟶ r.carrier) :
    r.omega f = r.reflexiveCurry (r.reflexiveUncurry (𝟙 r.carrier) ≫ f) := by
  rw [← il.eval_is_unfold]; rfl

end FixedPoint.Reflexive
