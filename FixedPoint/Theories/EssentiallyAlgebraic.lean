/-
  EssentiallyAlgebraic.lean

  Definitions for essentially algebraic theories (EATs).

  An EAT extends a many-sorted algebraic theory by allowing operations
  whose domains are defined by equations in previously introduced operations.
  Categories of models of EATs are precisely the locally presentable categories
  (Gabriel-Ulmer duality).

  This file provides the basic structure definitions needed for Claims A/A'
  (Boardman-Vogt tensor extension) and the instantiation of
  SubstrateIndependent.lean with EAT model categories.

  STATUS: Tier 2 — structures compile, key properties stated with sorry.
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Finset.Basic

namespace FixedPoint.Theories

/-- A sort in an essentially algebraic theory. -/
structure EATSort where
  name : String
  deriving DecidableEq, Repr

/-- An operation in an essentially algebraic theory. Operations may be total
    or partial; partial operations have their domain defined by equations
    in previously introduced operations. -/
structure EATOperation (sorts : List EATSort) where
  /-- Name of the operation. -/
  name : String
  /-- Input sort indices (into the sorts list). -/
  arity : List (Fin sorts.length)
  /-- Output sort index. -/
  target : Fin sorts.length
  /-- Whether this operation is total or partial.
      Partial operations have domains defined by equations. -/
  isTotal : Bool
  deriving Repr

/-- An equation constraining the domain of a partial operation.
    For a total operation, the domain condition list is empty. -/
structure DomainCondition (sorts : List EATSort) (ops : List (EATOperation sorts)) where
  /-- The partial operation whose domain this constrains. -/
  operation : Fin ops.length
  /-- Informal description of the equational condition.
      Full formalization of term algebra deferred to later work. -/
  description : String
  deriving Repr

/-- An essentially algebraic theory: a collection of sorts, operations
    (possibly partial), and domain conditions defining when partial
    operations are defined. -/
structure EATheory where
  /-- The sorts of the theory. -/
  sorts : List EATSort
  /-- The operations (total and partial). -/
  operations : List (EATOperation sorts)
  /-- Domain conditions for partial operations. -/
  conditions : List (DomainCondition sorts operations)
  deriving Repr

/-- A (total) algebraic theory is an EAT where all operations are total. -/
def EATheory.isAlgebraic (T : EATheory) : Prop :=
  ∀ op ∈ T.operations, op.isTotal = true

-- Gabriel-Ulmer duality: not axiomatized; the project uses the semantic
-- SubstrateCategory framework instead. See docs/alternative-approaches-ct.md.
--
-- The duality (models of an EAT in Set are locally finitely presentable,
-- and conversely) bridges the syntactic and semantic perspectives but is
-- not needed as a Lean axiom because SubstrateIndependent.lean encodes the
-- required categorical properties directly via typeclasses.

end FixedPoint.Theories
