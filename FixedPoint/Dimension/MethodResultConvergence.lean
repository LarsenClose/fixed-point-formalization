/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Method-result convergence for the Adamek chain dimension.

The "method" of iterating F from the initial object produces objects with
strictly increasing dimension (by `chainDimension_injective`). The "result"
(the colimit/fixed point L with F(L) ≅ L) absorbs further applications of F
without changing dimension. This file proves that these two perspectives
converge: the chain dimension is eventually constant at the fixed point, and
the fixed point's dimension characterizes the colimit.

Key results:
  - `dimension_eventually_constant_at_fixedpoint` : at F(L) ≅ L, every
      F^n(L) has the same dimension as L
  - `chain_dimension_injective_ne` : distinct chain indices give distinct
      chain dimensions (strict monotonicity of chainDimension)
  - `method_result_convergence` : the main convergence theorem, packaging
      the dimensional stability and absorption properties
  - `fixedpoint_no_finite_dimension` : if the chain never stabilizes and
      L is a fixed point, L cannot have any finite dimension
  - `fixedpoint_dimension_dichotomy` : either L has finite dimension and
      the chain already stabilized, or L has no finite dimension at all
-/

import FixedPoint.Dimension.Stabilization

open CategoryTheory CategoryTheory.Limits
open FixedPoint.Iteration
open FixedPoint.Dimension.TruncationLevel

namespace FixedPoint.Dimension

universe v u

variable {C : Type u} [Category.{v} C] [HasInitial C]

/-! ### Iterated functor application preserves dimension at fixed points -/

/-- Iterate F n times on an object. -/
def iterateFunctor (F : C ⥤ C) : ℕ → C → C
  | 0 => id
  | n + 1 => fun X => F.obj (iterateFunctor F n X)

omit [HasInitial C] in
/-- If F(L) ≅ L, then F^n(L) ≅ L for all n. -/
noncomputable def iterateFunctor_iso_at_fixedpoint (F : C ⥤ C) {L : C}
    (lamb : F.obj L ≅ L) : (n : ℕ) → iterateFunctor F n L ≅ L
  | 0 => Iso.refl L
  | n + 1 => F.mapIso (iterateFunctor_iso_at_fixedpoint F lamb n) ≪≫ lamb

/-- Iterating F on an iso-fixed-point L preserves dimension.
    If F(L) ≅ L and L has dimension d, then F^n(L) also has dimension d. -/
theorem dimension_eventually_constant_at_fixedpoint {F : C ⥤ C} {L : C}
    {d : TruncationLevel} (lamb : F.obj L ≅ L) (hL : HasDimension F L d)
    (n : ℕ) : HasDimension F (iterateFunctor F n L) d :=
  dimension_iso_invariant hL (iterateFunctor_iso_at_fixedpoint F lamb n).symm

/-! ### Strict monotonicity of chain dimension -/

/-- Distinct chain indices give distinct chain dimensions.
    This is a direct restatement of injectivity in the ≠ form. -/
theorem chain_dimension_injective_ne {n m : ℕ} (h : n ≠ m) :
    chainDimension n ≠ chainDimension m :=
  fun heq => h (chainDimension_injective heq)

/-- chainDimension is strictly monotone in the sense that it is injective
    and maps the natural order to distinct levels. -/
theorem chain_dimension_ne_succ (n : ℕ) :
    chainDimension n ≠ chainDimension (n + 1) :=
  chain_dimension_injective_ne (Nat.ne_of_lt (Nat.lt_succ_of_le (le_refl n)))

/-! ### The fixed point cannot have finite dimension (under strict chain divergence) -/

/-- If L is a fixed point with L ≅ iterateObj F n (finite dimension n), then the
    chain stabilizes at n: iterateObj F n ≅ iterateObj F (n+1). -/
theorem fixedpoint_implies_chain_stabilized {F : C ⥤ C} {L : C} {n : ℕ}
    (lamb : F.obj L ≅ L)
    (hL : HasDimension F L (chainDimension n)) :
    Nonempty (iterateObj F n ≅ iterateObj F (n + 1)) := by
  obtain ⟨m, hm, ⟨isoLm⟩⟩ := hL
  have hmn : m = n := chainDimension_injective hm
  subst hmn
  -- L ≅ iterateObj F n (via isoLm)
  -- F(L) ≅ L (via lamb)
  -- iterateObj F (n+1) = F.obj (iterateObj F n)
  -- Build: iterateObj F n ≅ L ≅ F(L)⁻¹ ≅ F(iterateObj F n) = iterateObj F (n+1)
  exact ⟨isoLm.symm ≪≫ lamb.symm ≪≫ F.mapIso isoLm⟩

/-- Under strict chain non-stabilization, the fixed point cannot have any
    finite dimension. If consecutive chain objects are never isomorphic and
    L has dimension `chainDimension n`, then L ≅ iterateObj F n and the
    Lambek iso forces iterateObj F n ≅ iterateObj F (n+1), contradicting
    the strict divergence hypothesis. -/
theorem fixedpoint_no_finite_dimension {F : C ⥤ C} {L : C} {n : ℕ}
    (lamb : F.obj L ≅ L)
    (hL : HasDimension F L (chainDimension n))
    (chain_strict : IsEmpty (iterateObj F n ≅ iterateObj F (n + 1))) : False := by
  exact chain_strict.false (fixedpoint_implies_chain_stabilized lamb hL).some

/-- Under strict chain non-stabilization for all indices, no finite dimension
    is possible for the fixed point. -/
theorem colimit_no_finite_dimension {F : C ⥤ C} {L : C}
    (lamb : F.obj L ≅ L)
    (chain_strict : ∀ k, IsEmpty (iterateObj F k ≅ iterateObj F (k + 1)))
    (n : ℕ) : ¬ HasDimension F L (chainDimension n) :=
  fun hL => fixedpoint_no_finite_dimension lamb hL (chain_strict n)

/-! ### The method-result convergence structure -/

/-- The method-result convergence theorem, packaged as a structure.
    At a fixed point L of F (with F(L) ≅ L):
    1. Dimension is stable: L and F(L) have exactly the same dimensions (iff)
    2. All further iterates F^n(L) have the same dimension as L
    3. The Lambek isomorphism absorbs the dimensional increment -/
structure MethodResultConvergence (F : C ⥤ C) (L : C) where
  /-- The Lambek isomorphism: F(L) ≅ L -/
  lambek : F.obj L ≅ L
  /-- Dimension stability: L and F(L) have the same dimensions -/
  dim_stable : ∀ d, HasDimension F L d ↔ HasDimension F (F.obj L) d
  /-- All iterates have the same dimension as L -/
  dim_constant : ∀ d, HasDimension F L d → ∀ n, HasDimension F (iterateFunctor F n L) d
  /-- Both chainDimension n and chainDimension (n+1) are witnessed at F(L)
      if L has finite dimension (the increment is absorbed) -/
  absorbs : ∀ n, HasDimension F L (chainDimension n) →
    HasDimension F (F.obj L) (chainDimension n) ∧
    HasDimension F (F.obj L) (chainDimension (n + 1))

/-- Build a MethodResultConvergence from a Lambek isomorphism. -/
noncomputable def method_result_convergence {F : C ⥤ C} {L : C}
    (lamb : F.obj L ≅ L) : MethodResultConvergence F L where
  lambek := lamb
  dim_stable := fun _ => fixedpoint_dimension_iff lamb
  dim_constant := fun _ hL n => dimension_eventually_constant_at_fixedpoint lamb hL n
  absorbs := fun _ hL => fixedpoint_absorbs_increment lamb hL

/-! ### Dimension dichotomy -/

/-- Every fixed point satisfies exactly one of:
    1. L has some finite dimension `chainDimension n`, in which case the chain
       already stabilized at stage n (iterateObj F n ≅ iterateObj F (n+1))
    2. L has no finite dimension at all (it lives at the omega level) -/
theorem fixedpoint_dimension_dichotomy {F : C ⥤ C} {L : C}
    (lamb : F.obj L ≅ L) :
    (∃ n, HasDimension F L (chainDimension n) ∧
          Nonempty (iterateObj F n ≅ iterateObj F (n + 1))) ∨
    (∀ n, ¬ HasDimension F L (chainDimension n)) := by
  by_cases h : ∃ n, HasDimension F L (chainDimension n)
  · left
    obtain ⟨n, hL⟩ := h
    exact ⟨n, hL, fixedpoint_implies_chain_stabilized lamb hL⟩
  · right
    push_neg at h
    exact h

/-! ### Connection to FixedPointSpec -/

section Substrate

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [FixedPoint.SubstrateCategory C]
variable {A : C} [Closed A]

/-- The method-result convergence for the `FixedPointSpec` carrier. -/
noncomputable def spec_method_result_convergence (fp : FixedPointSpec A) :
    MethodResultConvergence (ihom A) fp.carrier :=
  method_result_convergence fp.fixedPointIso

/-- Under strict chain non-stabilization, the `FixedPointSpec` carrier
    has no finite dimension. -/
theorem spec_no_finite_dimension (fp : FixedPointSpec A)
    (chain_strict : ∀ k, IsEmpty (iterateObj (ihom A) k ≅ iterateObj (ihom A) (k + 1)))
    (n : ℕ) : ¬ HasDimension (ihom A) fp.carrier (chainDimension n) :=
  colimit_no_finite_dimension fp.fixedPointIso chain_strict n

end Substrate

end FixedPoint.Dimension
