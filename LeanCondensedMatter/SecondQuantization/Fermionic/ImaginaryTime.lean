import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TwoPoint
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ExternalField
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedTimeOrdering
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedEventSlotEmbedding
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedOrderChamber
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedOrderWallMeasure
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedOrderSignature

set_option linter.style.header false

/-!
# Fermionic imaginary-time theory

Free diagonal evolution, evolved creation and annihilation operators, the canonical fermionic
two-point operator, labelled external fields, their time ordering together with even quartic
interaction vertices, the restriction of that mixed order along a monotone reindexing of the
interaction slots, mixed-event order chambers, their Lebesgue-null comparison walls and finite
Borel-measurable order signatures, the algebraic interaction picture, and its finite-basis
matrix-coefficient regularity results.
-/
