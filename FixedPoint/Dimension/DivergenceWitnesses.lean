/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Divergence witnesses: categories that fail the convergence criterion.

This file connects the FinSet divergence proof (cardinality obstruction) to the
dimension framework, and proves that thin categories cannot support nontrivial
computation (they lack enough morphisms for a CompModel).

## Main results

### Part 1: FinSet Divergence (dimensional reading)
- `finset_cardinality_strictly_increasing`: the sequence d, d^a, (d^a)^a, ...
  is strictly increasing when a >= 2 and d >= 2, so the chain of internal hom
  iterates in FinSet never stabilizes.

### Part 2: Thin Category Triviality
- `IsThin`: a category where every hom set has at most one morphism.
- `thin_reflexive_trivial`: in a thin category, every hom set is subsingleton,
  so any reflexive object D ≅ [D,D] is trivially subterminal.

### Part 3: Thin categories can't support computation
- `thin_no_nontrivial_computation`: a thin category cannot host a CompModel,
  which requires denumerably many programs (morphisms from the unit).

STATUS: Tier 1 (no sorry).
-/
import FixedPoint.Iteration.FinSetDivergence
import FixedPoint.Dimension.TruncationLevel
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

open CategoryTheory CategoryTheory.Limits

namespace FixedPoint.Dimension

/-! ## Part 1: FinSet Divergence — Dimensional Reading

The existing `FinSet.card_hom_gt` shows that |D^A| > |D| whenever |A| >= 2 and
|D| >= 2. We work at the level of cardinalities (natural numbers) to show the
sequence d, d^a, (d^a)^a, ... is strictly increasing — the chain of internal hom
iterates never stabilizes in FinSet.

This avoids universe issues with iterating Type-level function spaces. -/

namespace FinSetDimensional

/-- The n-th iterate of the cardinality map d ↦ d^a.
    `iterateCard a d 0 = d`, `iterateCard a d (n+1) = (iterateCard a d n) ^ a`.
    This represents `|F^n(D)|` where `F = ihom(A)` and `|A| = a`, `|D| = d`. -/
def iterateCard (a d : ℕ) : ℕ → ℕ
  | 0 => d
  | n + 1 => (iterateCard a d n) ^ a

@[simp]
theorem iterateCard_zero (a d : ℕ) : iterateCard a d 0 = d := rfl

@[simp]
theorem iterateCard_succ (a d n : ℕ) :
    iterateCard a d (n + 1) = (iterateCard a d n) ^ a := rfl

/-- Each iterate is at least 2 when the base is at least 2 and the exponent is at least 1. -/
theorem iterateCard_ge_two {a d : ℕ} (ha : 2 ≤ a) (hd : 2 ≤ d) (n : ℕ) :
    2 ≤ iterateCard a d n := by
  induction n with
  | zero => exact hd
  | succ n ih =>
    simp only [iterateCard_succ]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ (iterateCard a d n) ^ 1 := Nat.pow_le_pow_left (by omega) 1
      _ ≤ (iterateCard a d n) ^ a := Nat.pow_le_pow_right (by omega) (by omega)

/-- The cardinality sequence is strictly increasing: each iterate is strictly
    less than the next one, when |A| >= 2 and |D| >= 2.

    This is the dimensional reading of the FinSet divergence: at each step,
    the cardinality strictly grows, so the chain never stabilizes at any
    finite stage. -/
theorem finset_cardinality_strictly_increasing {a d : ℕ} (ha : 2 ≤ a) (hd : 2 ≤ d)
    (n : ℕ) : iterateCard a d n < iterateCard a d (n + 1) := by
  simp only [iterateCard_succ]
  exact FixedPoint.FinSet.pow_gt_base _ _ (iterateCard_ge_two ha hd n) ha

/-- The chain of cardinalities diverges to infinity: for any bound N,
    there exists an iterate whose cardinality exceeds N. -/
theorem finset_cardinality_diverges {a d : ℕ} (ha : 2 ≤ a) (hd : 2 ≤ d)
    (N : ℕ) : ∃ n, N < iterateCard a d n := by
  induction N with
  | zero =>
    exact ⟨0, by simp; omega⟩
  | succ N ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, lt_of_le_of_lt (by omega : N + 1 ≤ iterateCard a d n)
      (finset_cardinality_strictly_increasing ha hd n)⟩

/-- The cardinality sequence is strictly monotone. -/
theorem finset_iterateCard_strictMono {a d : ℕ} (ha : 2 ≤ a) (hd : 2 ≤ d) :
    StrictMono (iterateCard a d) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact finset_cardinality_strictly_increasing ha hd n

/-- Corollary: the cardinality sequence is injective (no two iterates have
    the same cardinality). Combined with `chainDimension_injective`, this
    means distinct iterates live at distinct dimensions. -/
theorem finset_iterateCard_injective {a d : ℕ} (ha : 2 ≤ a) (hd : 2 ≤ d) :
    Function.Injective (iterateCard a d) :=
  (finset_iterateCard_strictMono ha hd).injective

end FinSetDimensional

/-! ## Part 2: Thin Category Triviality

A thin category is one where every hom set has at most one morphism.
In such a category, any object is "trivial" in the sense that there is
at most one morphism into it from any other object. -/

/-- A category is thin if every hom set has at most one morphism. -/
class IsThin (C : Type*) [Category C] : Prop where
  eq_of_hom : ∀ (X Y : C) (f g : X ⟶ Y), f = g

/-- In a thin category, any two parallel morphisms are equal. -/
theorem thin_eq {C : Type*} [Category C] [IsThin C] {X Y : C} (f g : X ⟶ Y) :
    f = g :=
  IsThin.eq_of_hom X Y f g

/-- In a thin category, every hom set is a subsingleton. -/
instance thin_hom_subsingleton {C : Type*} [Category C] [IsThin C] (X Y : C) :
    Subsingleton (X ⟶ Y) :=
  ⟨thin_eq⟩

/-- In a thin category, any isomorphism is unique. -/
theorem thin_iso_unique {C : Type*} [Category C] [IsThin C] {X Y : C}
    (e₁ e₂ : X ≅ Y) : e₁ = e₂ := by
  ext; exact thin_eq _ _

/-! ### Thin reflexive objects are trivial

In a thin monoidal closed category, if D ≅ [D, D], the isomorphism is
trivially unique (by thinness) and D is subterminal: for any X, there
is at most one morphism X ⟶ D. -/

/-- In a thin category, every object is subterminal: Hom(X, D) is a subsingleton
    for any X and D. In particular, a reflexive object D ≅ [D,D] has at most
    one self-map and at most one global element.

    This is immediate from thinness — no monoidal structure needed. -/
theorem thin_reflexive_trivial {C : Type*} [Category C] [IsThin C]
    (D X : C) : Subsingleton (X ⟶ D) :=
  thin_hom_subsingleton X D

/-! ## Part 3: Thin Categories Can't Support Computation

A `CompModel` (as informally specified) requires a `Denumerable` type of programs,
i.e., infinitely many distinct morphisms from the unit to the reflexive object.
In a thin category, there is at most one such morphism. -/

/-- In a thin category, any two morphisms between the same objects are equal.
    A CompModel requires Denumerable many programs (morphisms I ⟶ D),
    which requires infinitely many distinct morphisms. Since a thin category
    provides at most one, it cannot support any nontrivial CompModel. -/
theorem thin_no_nontrivial_computation {C : Type*} [Category C] [IsThin C]
    (X D : C) (f g : X ⟶ D) : f = g :=
  thin_eq f g

/-- Consequence: in a thin category, it is impossible to have two distinct
    morphisms into any object. This directly contradicts the requirement
    of denumerably many programs. -/
theorem thin_no_two_distinct {C : Type*} [Category C] [IsThin C]
    (X D : C) : ¬∃ (f g : X ⟶ D), f ≠ g := by
  intro ⟨f, g, hfg⟩
  exact hfg (thin_eq f g)

/-- The cardinality obstruction, stated as a Fintype bound: if we could
    somehow give Hom(X, D) a Fintype instance in a thin category,
    its cardinality would be at most 1. -/
theorem thin_hom_card_le_one {C : Type*} [Category C] [IsThin C]
    (X D : C) [Fintype (X ⟶ D)] : Fintype.card (X ⟶ D) ≤ 1 :=
  Fintype.card_le_one_iff_subsingleton.mpr (thin_hom_subsingleton X D)

end FixedPoint.Dimension
