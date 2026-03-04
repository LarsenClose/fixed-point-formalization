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
import FixedPoint.ChurchTuring.RogersIsomorphism
