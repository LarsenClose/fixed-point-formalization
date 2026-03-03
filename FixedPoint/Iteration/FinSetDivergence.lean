/-
  FinSetDivergence.lean

  Proof that the internal-hom endofunctor D ↦ D^A diverges in FinSet
  (finite sets) for |A| ≥ 2: the function type (A → D) has cardinality
  |D|^|A| > |D| whenever |D| ≥ 2 and |A| ≥ 2, so no finite set can be
  a fixed point.

  This is the negative result motivating the move to locally presentable
  categories (which include infinite objects) for the fixed-point construction.

  STATUS: Tier 1 target — pure combinatorics, should be fully provable.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace FixedPoint.FinSet

/-- n^n > n for n ≥ 2. Helper lemma for the cardinality argument. -/
theorem self_pow_gt (n : ℕ) (hn : 2 ≤ n) : n < n ^ n := by
  calc n = n ^ 1 := (Nat.pow_one n).symm
    _ < n ^ n := by
        apply Nat.pow_lt_pow_right
        · omega
        · omega

/-- For any finite type D with |D| ≥ 2, |D|^|D| > |D|.
    This is the core cardinality obstruction: the self-hom D^D
    is strictly larger than D in FinSet. -/
theorem card_self_hom_gt {D : Type*} [Fintype D] [DecidableEq D]
    (hD : 2 ≤ Fintype.card D) :
    Fintype.card D < Fintype.card (D → D) := by
  rw [Fintype.card_fun]
  exact self_pow_gt _ hD

/-- n^m > n when m ≥ 2 and n ≥ 2. -/
theorem pow_gt_base (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : n < n ^ m := by
  calc n = n ^ 1 := (Nat.pow_one n).symm
    _ < n ^ m := by
        apply Nat.pow_lt_pow_right
        · omega
        · omega

/-- More generally, for |A| ≥ 2 and |D| ≥ 2, |D^A| = |D|^|A| > |D|. -/
theorem card_hom_gt {A D : Type*} [Fintype A] [DecidableEq A] [Fintype D]
    (hA : 2 ≤ Fintype.card A) (hD : 2 ≤ Fintype.card D) :
    Fintype.card D < Fintype.card (A → D) := by
  rw [Fintype.card_fun]
  exact pow_gt_base _ _ hD hA

/-- Consequence: no finite set D with |D| ≥ 2 satisfies D^A ≅ D
    (as sets, i.e., equal cardinality) when |A| ≥ 2. -/
theorem no_finite_fixed_point {A D : Type*} [Fintype A] [DecidableEq A] [Fintype D]
    (hA : 2 ≤ Fintype.card A) (hD : 2 ≤ Fintype.card D) :
    Fintype.card (A → D) ≠ Fintype.card D :=
  Nat.ne_of_gt (card_hom_gt hA hD)

end FixedPoint.FinSet
