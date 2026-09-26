import LeanCondensedMatter.Analysis.ConservationLaw.CurrentRepresentation
import LeanCondensedMatter.Analysis.ConservationLaw.CurrentEquivalence
import LeanCondensedMatter.Analysis.ConservationLaw.IntrinsicBalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.BalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.BalanceLawAdapter
import LeanCondensedMatter.Analysis.ConservationLaw.WeakConservation1D
import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra
import LeanCondensedMatter.Analysis.ConservationLaw.CorrectedCurrentFlux

set_option linter.style.header false

/-!
# Conservation laws

Public routing module for representation-independent and represented balance laws, current
representations, and generic weak conservation identities exported by `LeanCondensedMatter.Analysis`.
-/
