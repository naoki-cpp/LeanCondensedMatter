import LeanCondensedMatter.Analysis.ConservationLaw.CurrentRepresentation
import LeanCondensedMatter.Analysis.ConservationLaw.CurrentEquivalence
import LeanCondensedMatter.Analysis.ConservationLaw.FluxBalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.BalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.BalanceLawAdapter
import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra
import LeanCondensedMatter.Analysis.ConservationLaw.CorrectedCurrentFlux

set_option linter.style.header false

/-!
# Conservation laws

Abstract conservation and balance-law theory: current representations and their equivalence,
intrinsic and represented balance laws, adapters between them, symmetric localization, and
corrected current-flux algebra.

The one-dimensional integration-by-parts kernel remains available separately via
`LeanCondensedMatter.Analysis.ConservationLaw.WeakConservation1D`.
-/
