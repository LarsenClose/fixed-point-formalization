-- Lean 4 formal verification for the fixed-point paper series.
-- See Status.md for full walkthrough of what is proved and what is not.

-- Substrate-independent specification
import FixedPoint.Specification.SubstrateIndependent

-- Uniqueness of the fixed-point endofunctor
import FixedPoint.Uniqueness.RightAdjointUnique

-- Iteration and divergence
import FixedPoint.Iteration.AdamekChain
import FixedPoint.Iteration.FinSetDivergence

-- Adamek's Initial Algebra Theorem
import FixedPoint.Iteration.InitialChain
import FixedPoint.Iteration.ChainShift
import FixedPoint.Iteration.AdamekTheorem
import FixedPoint.Iteration.AdamekConnection

-- Theory definitions
import FixedPoint.Theories.EssentiallyAlgebraic

-- Boardman-Vogt conjectures (isolated, nothing depends on this)
import FixedPoint.Tensor.BoardmanVogt

-- Accessibility (AR Theorem 2.23)
import FixedPoint.Accessibility.RightAdjointAccessible

-- Church-Turing characterization and Rogers isomorphism
import FixedPoint.ChurchTuring.CharacterizationTheorem
import FixedPoint.ChurchTuring.Myhill
import FixedPoint.ChurchTuring.RogersIsomorphism

-- Reflexive object and self-application (Target 3)
import FixedPoint.Reflexive.ReflexiveObject

-- Fixed-point combinator from reflexive object (Target 4)
import FixedPoint.Reflexive.FixedPointCombinator

-- Categorical dimension via truncation levels (Target 1)
import FixedPoint.Dimension.TruncationLevel

-- F increments dimension by 1 (Target 2)
import FixedPoint.Dimension.IncrementDimension

-- Dimension stabilizes at the fixed point (Target 2.5)
import FixedPoint.Dimension.Stabilization

-- Graded filtration theorem (Target 7)
import FixedPoint.Dimension.GradedFiltration

-- Divergence witnesses: FinSet + thin categories (Target 11)
import FixedPoint.Dimension.DivergenceWitnesses

-- Method-result convergence (Target 12)
import FixedPoint.Dimension.MethodResultConvergence

-- Convergence criterion theorem (Target 10)
import FixedPoint.Dimension.ConvergenceCriterion

-- T4 → Kleene bridge (Target 8)
import FixedPoint.Reflexive.KleeneBridge

-- Self-indexed computation model (Layer 2 of Kleene bridge)
import FixedPoint.Reflexive.SelfIndexedComputation

-- Kleene derivation from categorical Y combinator (Target 13)
import FixedPoint.Reflexive.KleeneDerivation

-- Dimensional dissolution via Yoneda (Target 9)
import FixedPoint.Dimension.DimensionalDissolution

-- Monoidal uniqueness framework (Target 5a)
import FixedPoint.Uniqueness.MonoidalUniqueness
