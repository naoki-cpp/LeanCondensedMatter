import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TwoPoint
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ExternalField
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedTimeOrdering

set_option linter.style.header false

/-!
# Fermionic imaginary-time theory

Free diagonal evolution, evolved creation and annihilation operators, the canonical fermionic
two-point operator, labelled external fields, and their operator realization in the shared
statistics-independent mixed-event order. The mixed event ordering, monotone slot embeddings,
order chambers, null comparison walls, and finite order signatures are owned by
`SecondQuantization.Common`; this namespace supplies the fermionic operator/sign specialization.
-/
