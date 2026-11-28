import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.EnergyShift
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.KMSRotation
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionImaginaryTimeOrder
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointImaginaryTimeOrder
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ImaginaryTimeOrderSignature
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder

set_option linter.style.header false

/-!
# Statistics-independent imaginary-time theory

Diagonal free and interaction-picture evolution, energy-shift and KMS identities,
statistics-indexed time ordering, and measurable two-point and arbitrary-external event and leg
orders. Exchange signs for the mixed leg orders are supplied by the statistics-specific layer.
-/
