import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreePartitionDeterminant
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.PolynomialOccupationWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannSummability
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.Completed.FreeGibbs

set_option linter.style.header false

/-!
# Free bosonic thermal theory

Convergent free partition functions and inverse-determinant identities, connected-cycle series,
polynomial occupation-weight summability, Gibbs expectations, ladder KMS identities and Wick
expansions, and completed Gibbs densities under explicit summability and positivity hypotheses.
Unbounded operator expectations retain their domain conditions.
-/
