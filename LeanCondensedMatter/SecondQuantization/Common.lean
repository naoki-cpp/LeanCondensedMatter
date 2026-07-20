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
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.FourPointReduction
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirst
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.ProdCompFamily
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelTermsIndexed
import LeanCondensedMatter.Combinatorics.EraseIdxOfFn

set_option linter.style.header false

/-!
# Umbrella module for the statistics-agnostic `SecondQuantization/Common` layer

Importing this module brings in every file of the shared (boson/fermion-agnostic) layer at once.
Deliberately **excluded**: `Common/QuantumLinkedCluster.lean`, which currently imports `Fermionic/`
(the known dependency-direction violation flagged as Phase 9 step 7 in
`notes/roadmaps/second-quantization.md`) — including it here would make this umbrella depend on
the fermionic line. It is imported separately at the project root until it is moved or
generalized.
-/
