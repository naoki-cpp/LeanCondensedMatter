import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics
import LeanCondensedMatter.SecondQuantization.Common.Algebra.OccupationBasis
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.Algebra.SupportShift
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeCommutator
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-!
# Statistics-independent second-quantization algebra

Particle statistics, occupation-basis interfaces, algebraic Fock spaces, fixed support shifts, and
the common CAR/CCR exchange-algebra interface.

Mode labels are represented by an arbitrary type. The common algebra imposes no project-wide
finiteness or decidable-equality requirement on that type; such assumptions belong only on the
operations that need them.
-/
