import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSourceSign
import LeanCondensedMatter.Combinatorics.Cumulant.WeightedInversion
import Mathlib.RingTheory.PowerSeries.Basic

set_option linter.style.header false

/-!
# Finite fermionic external-source cumulants

The fermionic source sign specializes the general unit-top weighted
moment–cumulant inversion on finite subsets. The combinatorial inverse
is independent of Wick diagrams and Dyson amplitudes: identifying its
connected contribution with the physical diagram sum requires a separate
signed moment identity.
-/

namespace SecondQuantization
namespace Fermionic

open scoped BigOperators

variable {E : ℕ}

/-- Fermionic source cumulants, recursively reconstructed from the complete
subset moment function using the canonical fermionic partition signs.
The empty connected contribution is zero. -/
noncomputable def externalSubsetSourceCumulantSeries
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ) :
    Finset (Fin (2 * E)) → PowerSeries ℂ :=
  Finpartition.weightedCumulantFromMoment
    (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) M

@[simp]
theorem externalSubsetSourceCumulantSeries_empty
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ) :
    externalSubsetSourceCumulantSeries M ∅ = 0 := by
  exact Finpartition.weightedCumulantFromMoment_empty
    (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) M

end Fermionic
end SecondQuantization
