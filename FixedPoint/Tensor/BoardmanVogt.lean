/-
  BoardmanVogt.lean — ISOLATED MODULE (Tier 3 conjectures)

  This file is quarantined from the verified core. Claims A and A' contain
  `sorry` and must not be depended upon by any Tier 1/2 theorem. No other
  module in the project imports this file (it appears only in the root
  FixedPoint.lean import list for documentation completeness).

  Scaffolds Claims A and A' from the paper series as formal conjectures.

  Claim A: The Boardman-Vogt tensor product on Lawvere theories extends to
  essentially algebraic theories (EATs). The obstacle is partial-operation
  domain compatibility — tensoring two EATs requires the domain conditions
  of one theory to be respected by the operations of the other.

  Claim A': The Lawvere-Linton correspondence (between Lawvere theories and
  finitary monads on Set) extends to EATs (yielding a correspondence with
  accessible monads on locally presentable categories). This provides the
  construction path for the Psi functor in Claim B.

  Both claims are prerequisites for Claim B (the main Psi conjecture).

  STATUS: Tier 3 — structures and conjectures stated with sorry.
-/
import Mathlib.CategoryTheory.Monoidal.Category
import FixedPoint.Theories.EssentiallyAlgebraic

open CategoryTheory

namespace FixedPoint.Tensor

/-- A Lawvere theory: a category with finite products whose objects are
    natural-number powers of a single distinguished object.
    Placeholder pending full Mathlib formalization. -/
structure LawvereTheory where
  /-- The underlying EAT (every Lawvere theory is an EAT with all
      operations total). -/
  toEAT : Theories.EATheory
  /-- All operations are total. -/
  allTotal : toEAT.isAlgebraic

/-- The Boardman-Vogt tensor product of two Lawvere theories.
    For Lawvere theories L₁, L₂, the BV tensor L₁ ⊗_BV L₂ classifies
    pairs of an L₁-model and an L₂-model whose operations commute.
    Placeholder: produces an EAT (which is again Lawvere). -/
noncomputable def bvTensorLawvere
    (L₁ _L₂ : LawvereTheory) : LawvereTheory := by
  exact ⟨L₁.toEAT, L₁.allTotal⟩ -- placeholder

/-- **Claim A** (Boardman-Vogt tensor extension).

    The BV tensor product extends from Lawvere theories to EATs.
    Given two EATs T₁, T₂, there exists an EAT T₁ ⊗_BV T₂ such that:
    (1) models of T₁ ⊗_BV T₂ are pairs of commuting models, and
    (2) when T₁, T₂ are both Lawvere, it agrees with the classical BV tensor.

    Obstacle: the domain conditions of partial operations in T₁ must be
    compatible with the operations of T₂ in the commuting structure. -/
theorem claimA_bvTensor_extends :
    ∀ (T₁ T₂ : Theories.EATheory),
    ∃ (tensor : Theories.EATheory),
      -- The tensor of two algebraic theories is algebraic
      (T₁.isAlgebraic → T₂.isAlgebraic → tensor.isAlgebraic) := by
  sorry

/-- **Claim A'** (Lawvere-Linton correspondence extension).

    The classical Lawvere-Linton correspondence — between Lawvere theories
    and finitary monads on Set — extends to EATs. Specifically, there is an
    equivalence between:
    (a) EATs (up to Morita equivalence), and
    (b) accessible monads on locally presentable categories.

    This provides the construction path for the Psi functor: the monoidal
    structure on EATs (via Claim A) transfers along this correspondence to
    a monoidal structure on the domain side. -/
theorem claimA'_lawvereLinton_extends :
    ∀ (T : Theories.EATheory),
    ∃ (T' : Theories.EATheory),
      -- Round-trip: theory to monad and back recovers an equivalent theory.
      -- Full statement requires monad infrastructure; placeholder uses EAT.
      T'.sorts.length = T.sorts.length := by
  sorry

end FixedPoint.Tensor
