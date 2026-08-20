import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

set_option linter.style.header false

/-!
# Free Gibbs state on completed fermionic Fock space

The completed fermionic free Gibbs state is the generic pure-point Gibbs state specialized to the
occupation Hilbert basis and the free occupation energy `fermionEnergy ε`.  Boltzmann weights,
partition functions, normalized probabilities, summability, and the density operator itself are
owned by `QuantumTheory.Gibbs.PurePoint`; this module only records the completed-basis expectation
formula used by the fermionic KMS layer.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- Bounded-operator expectations in the completed free Gibbs state are the absolutely convergent
occupation-basis pure-point Gibbs series. -/
theorem completedFreeGibbsDensityOperator_expectation_eq_tsum
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).expectation A =
      ∑' n : Occupation Mode,
        (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
          inner ℂ (completedBasisState n) (A (completedBasisState n)) := by
  simpa using
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
      (fermionEnergy ε) β hsum).expectation_eq_tsum_diagonal
      A completedOccupationHilbertBasis (purePointGibbsProbability (fermionEnergy ε) β)
      (fun n => by
        simpa using
          purePointGibbsDensityOperator_apply_basis completedOccupationHilbertBasis
            (fermionEnergy ε) β hsum n)

end
end Fermionic
end SecondQuantization
