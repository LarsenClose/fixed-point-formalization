-- Lean 4 formal verification for the fixed-point paper series.
-- See Status.md for theorem verification status by tier.

-- Substrate-independent specification
import FixedPoint.Specification.SubstrateIndependent

-- Uniqueness of the fixed-point endofunctor
import FixedPoint.Uniqueness.RightAdjointUnique

-- Iteration and divergence
import FixedPoint.Iteration.AdamekChain
import FixedPoint.Iteration.FinSetDivergence

-- Theory definitions
import FixedPoint.Theories.EssentiallyAlgebraic

-- Tensor product conjectures (Claims A/A')
import FixedPoint.Tensor.BoardmanVogt

-- Church-Turing characterization
import FixedPoint.ChurchTuring.CharacterizationTheorem
