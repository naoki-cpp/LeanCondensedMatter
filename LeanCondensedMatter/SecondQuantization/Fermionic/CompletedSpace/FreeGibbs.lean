import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.DiagonalAnalytic
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula

set_option linter.style.header false

/-!
# Free Gibbs state on completed fermionic Fock space

This file begins C4 of the completed-space roadmap.  The free Gibbs state is constructed directly
from the occupation Hilbert basis and the real Boltzmann weights.  Absolute summability of those
weights is the explicit thermal hypothesis; no finite-mode assumption is used.

Bounded observables use the canonical `DensityOperator.expectation`.  Unbounded diagonal
observables are kept behind a separate weighted-integrability predicate instead of being coerced
into the bounded-observable API.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

/-- The canonical occupation Hilbert basis of the completed fermionic Fock space. -/
noncomputable def completedOccupationHilbertBasis :
    HilbertBasis (Occupation Mode) ℂ (CompletedFockSpace Mode) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (CompletedFockSpace Mode))

@[simp]
theorem completedOccupationHilbertBasis_apply (n : Occupation Mode) :
    completedOccupationHilbertBasis (Mode := Mode) n = completedBasisState n := by
  rfl

/-- The positive real free Boltzmann weight `exp (-β E(n))` on an occupation configuration. -/
noncomputable def completedFreeBoltzmannRealWeight (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) : ℝ :=
  Real.exp (-β * fermionEnergy ε n)

@[simp]
theorem completedFreeBoltzmannRealWeight_pos (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) :
    0 < completedFreeBoltzmannRealWeight ε β n := by
  simp [completedFreeBoltzmannRealWeight]

@[simp]
theorem completedFreeBoltzmannRealWeight_nonneg (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) :
    0 ≤ completedFreeBoltzmannRealWeight ε β n :=
  (completedFreeBoltzmannRealWeight_pos ε β n).le

/-- The completed real Boltzmann weight is the real scalar underlying the existing algebraic
complex Boltzmann weight. -/
theorem coe_completedFreeBoltzmannRealWeight (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) :
    (completedFreeBoltzmannRealWeight ε β n : ℂ) = freeBoltzmannWeight ε β n := by
  rw [freeBoltzmannWeight_eq_ofReal]
  simp [completedFreeBoltzmannRealWeight, fermionEnergy]

/-- Thermal summability hypothesis for the completed free Gibbs state.  This is absolute
summability in the form consumed by the generic diagonal trace-class construction. -/
def CompletedFreeGibbsSummable (ε : Mode → ℝ) (β : ℝ) : Prop :=
  Summable fun n : Occupation Mode => ‖completedFreeBoltzmannRealWeight ε β n‖

/-- The completed free partition function as an infinite occupation-basis sum. -/
noncomputable def completedFreePartitionFunction (ε : Mode → ℝ) (β : ℝ) : ℝ :=
  ∑' n : Occupation Mode, completedFreeBoltzmannRealWeight ε β n

/-- Absolute Boltzmann summability implies ordinary summability of the positive weights. -/
theorem completedFreeBoltzmannRealWeight_summable (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) :
    Summable (completedFreeBoltzmannRealWeight ε β) :=
  Summable.of_norm hsum

/-- Under the thermal summability hypothesis the completed partition function is strictly positive,
so normalization does not require a separate nonzero assumption. -/
theorem completedFreePartitionFunction_pos (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) :
    0 < completedFreePartitionFunction ε β := by
  rw [completedFreePartitionFunction]
  exact (completedFreeBoltzmannRealWeight_summable ε β hsum).tsum_pos
    (fun n => completedFreeBoltzmannRealWeight_nonneg ε β n) vacuum
    (completedFreeBoltzmannRealWeight_pos ε β vacuum)

/-- The normalized occupation probability of the completed free Gibbs state. -/
noncomputable def completedFreeGibbsProbability (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) : ℝ :=
  (completedFreePartitionFunction ε β)⁻¹ * completedFreeBoltzmannRealWeight ε β n

@[simp]
theorem completedFreeGibbsProbability_nonneg (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) (n : Occupation Mode) :
    0 ≤ completedFreeGibbsProbability ε β n := by
  exact mul_nonneg (inv_nonneg.mpr (completedFreePartitionFunction_pos ε β hsum).le)
    (completedFreeBoltzmannRealWeight_nonneg ε β n)

/-- The normalized Gibbs probabilities sum to one. -/
theorem hasSum_completedFreeGibbsProbability (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) :
    HasSum (completedFreeGibbsProbability ε β) 1 := by
  have hZ : 0 < completedFreePartitionFunction ε β :=
    completedFreePartitionFunction_pos ε β hsum
  have hweight := (completedFreeBoltzmannRealWeight_summable ε β hsum).hasSum
  have hscaled := hweight.mul_left (completedFreePartitionFunction ε β)⁻¹
  convert hscaled using 1
  · funext n
    rfl
  · rw [completedFreePartitionFunction]
    exact inv_mul_cancel₀ (ne_of_gt hZ)

/-- The completed free Gibbs density operator.  Its only analytic input is absolute summability of
the Boltzmann weights. -/
noncomputable def completedFreeGibbsDensityOperator (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) :
    DensityOperator (CompletedFockSpace Mode) :=
  diagonalDensityOperator completedOccupationHilbertBasis
    (completedFreeBoltzmannRealWeight ε β) hsum
    (completedFreeBoltzmannRealWeight_nonneg ε β)
    (by simpa [completedFreePartitionFunction] using
      completedFreePartitionFunction_pos ε β hsum)

/-- The completed free Gibbs density operator is diagonal in the occupation basis with the
normalized Boltzmann probability. -/
theorem completedFreeGibbsDensityOperator_apply_basis (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) (n : Occupation Mode) :
    (completedFreeGibbsDensityOperator ε β hsum).op (completedBasisState n) =
      (completedFreeGibbsProbability ε β n : ℂ) • completedBasisState n := by
  have hZ : 0 < ∑' n : Occupation Mode, completedFreeBoltzmannRealWeight ε β n := by
    simpa [completedFreePartitionFunction] using completedFreePartitionFunction_pos ε β hsum
  simpa [completedFreeGibbsDensityOperator, completedFreeGibbsProbability,
    completedFreePartitionFunction, normalizedDiagonalWeight] using
    diagonalDensityOperator_apply_basis completedOccupationHilbertBasis
      (completedFreeBoltzmannRealWeight ε β) hsum
      (completedFreeBoltzmannRealWeight_nonneg ε β) hZ n

/-- Bounded-operator expectations are the absolutely convergent occupation-basis Gibbs series. -/
theorem completedFreeGibbsDensityOperator_expectation_eq_tsum
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    (completedFreeGibbsDensityOperator ε β hsum).expectation A =
      ∑' n : Occupation Mode,
        (completedFreeGibbsProbability ε β n : ℂ) *
          inner ℂ (completedBasisState n) (A (completedBasisState n)) := by
  exact (completedFreeGibbsDensityOperator ε β hsum).expectation_eq_tsum_diagonal
    A completedOccupationHilbertBasis (completedFreeGibbsProbability ε β)
    (completedFreeGibbsDensityOperator_apply_basis ε β hsum)

/-- Separate integrability condition for an unbounded diagonal observable with real occupation
values.  Such observables are deliberately not passed to `DensityOperator.expectation`, whose
argument is bounded. -/
def CompletedFreeGibbsIntegrableDiagonal (ε : Mode → ℝ) (β : ℝ)
    (a : Occupation Mode → ℝ) : Prop :=
  Summable fun n : Occupation Mode => ‖completedFreeGibbsProbability ε β n * a n‖

end
end Fermionic
end SecondQuantization
