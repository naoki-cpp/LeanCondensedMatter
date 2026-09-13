import LeanCondensedMatter.Analysis.Operator.Unbounded
import LeanCondensedMatter.Analysis.Operator.Spectral
import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import LeanCondensedMatter.Analysis.Operator.L2MultiplicationRealLine
import LeanCondensedMatter.Analysis.Operator.L2MultiplicationRealLine.Linear
import LeanCondensedMatter.Analysis.Operator.SchwartzKinetic1D
import LeanCondensedMatter.Analysis.Operator.ZetaCommutator
import LeanCondensedMatter.Analysis.Operator.LinearCommutator
import LeanCondensedMatter.Analysis.Operator.OrbitalAngularMomentum
import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt
import LeanCondensedMatter.Analysis.Operator.Fredholm
import LeanCondensedMatter.Analysis.Operator.DiagonalExpectationFinite
import LeanCondensedMatter.Analysis.Operator.TraceClass

set_option linter.style.header false

/-!
# Operator analysis

Public routing module for the operator-theory endpoints exported by `LeanCondensedMatter.Analysis`.
Implementation modules should continue to import the narrow operator leaves they actually use.
-/
