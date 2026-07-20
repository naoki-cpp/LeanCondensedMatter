import LeanCondensedMatter.SecondQuantization.Bosonic.Occupation
import LeanCondensedMatter.SecondQuantization.Bosonic.FockSpace
import LeanCondensedMatter.SecondQuantization.Bosonic.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Bosonic.ParticleNumberCharge
import LeanCondensedMatter.SecondQuantization.Bosonic.CCR
import LeanCondensedMatter.SecondQuantization.Bosonic.ExchangeAlgebra
import LeanCondensedMatter.SecondQuantization.Bosonic.NumberOperator
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTimeOrdering
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Bosonic.FreeTwoPointCoefficient
import LeanCondensedMatter.SecondQuantization.Bosonic.BoltzmannWeightFactorization
import LeanCondensedMatter.SecondQuantization.Bosonic.BoltzmannWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.ParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.BlochDeDominicis.TwoPoint

set_option linter.style.header false

/-!
# Umbrella module for the bosonic line of `SecondQuantization/`

Importing this module brings in every file of the bosonic (`Occupation Mode := Mode →₀ ℕ`) line
at once, including its `BlochDeDominicis/` subdirectory.
-/
