import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.EnergyShift
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.KMSRotation
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.StableTimedEventOrder
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionImaginaryTimeOrder
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointImaginaryTimeOrder
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ImaginaryTimeOrderSignature
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder

set_option linter.style.header false

/-!
# Statistics-independent imaginary-time infrastructure

Statistics-aware pair time ordering, basis-diagonal free evolution, fixed energy-shift eigenoperators,
algebraic Heisenberg evolution, interaction-picture operators, KMS rotation identities, generic
quartic-interaction evolution, the arbitrary-external and two-point imaginary-time event/atomic-leg orderings,
with monotone slot transport and measurable finite order signatures.
These are ordering coordinates; fermionic exchange signs are supplied separately.
-/
