import LeanCondensedMatter.SecondQuantization.Common.OneParticleSpace
import LeanCondensedMatter.SecondQuantization.Common.Statistics
import LeanCondensedMatter.SecondQuantization.Common.OccupationBasis
import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.ParticleNumberSelectionRule
import LeanCondensedMatter.SecondQuantization.Common.ExchangeCommutator
import LeanCondensedMatter.SecondQuantization.Common.ExchangeAlgebra
import LeanCondensedMatter.SecondQuantization.Common.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Common.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.NormalizedOperatorFunctional
import LeanCondensedMatter.SecondQuantization.Common.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.KMSRotation
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis

set_option linter.style.header false

/-!
# Umbrella module for the statistics-agnostic `SecondQuantization/Common` layer

Importing this module brings in every file of the shared (boson/fermion-agnostic) layer at once.
`QuantumLinkedCluster.lean` — which depends on `Fermionic/` — now lives at
`SecondQuantization/Fermionic/QuantumLinkedCluster.lean`, not here; see that file and
`notes/roadmaps/second-quantization.md`'s Phase 9 step 7 for its own scope and status.
-/
