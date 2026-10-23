import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteCompletedGibbsCompatibility
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate

set_option linter.style.header false

/-!
# Finite-mode compatibility of completed fermionic grand-canonical Gibbs states

For finite fermionic mode types, the completed occupation Hilbert space is
canonically isometric to the finite Hilbert occupation realization. The common
grand-canonical density state on the completed side is intertwined with the
finite Gibbs density state evaluated at shifted one-mode energies `ε - μ`.

The finite density-state expectation then equals the common summable diagonal
trace ratio from the algebraic Fock theory. This does not identify arbitrary
bounded completed operators with algebraic-Fock endomorphisms in infinite modes.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- At finite mode number, the completed grand-canonical density operator and
the finite free-fermion Gibbs density operator at effective energy `ε - μ`
are intertwined by the canonical completed-to-finite Hilbert equivalence. -/
theorem completedGrandCanonicalGibbs_intertwines_finite
    (ε : Mode → ℝ) (β μ : ℝ) :
    (Common.completedFiniteHilbertEquiv (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ
        (eigenbasisGibbsSummable_of_finite
          (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)).op =
      (freeGibbsDensityOperator (fun i => ε i - μ) β).op.comp
        (Common.completedFiniteHilbertEquiv (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap := by
  have hE :
      Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ =
        fermionEnergy (fun i => ε i - μ) := by
    funext n
    exact Common.grandCanonicalEnergy_eq_shifted ε μ n
  simpa [Common.grandCanonicalGibbsDensityOperator,
    freeGibbsDensityOperator, hE] using
    (Common.completedFiniteHilbertEquiv_intertwines_eigenbasisGibbsDensity
      (Config := Occupation Mode)
      (fermionEnergy (fun i => ε i - μ)) β)

/-- The finite fermionic grand-canonical density-state expectation is the
summable diagonal trace ratio of #4074, with shifted one-mode energies.
Summability on the algebraic side is automatic only because the occupation
configuration type is finite. -/
theorem finiteGrandCanonicalGibbsExpectation_eq_diagonalTraceRatio
    (ε : Mode → ℝ) (β μ : ℝ)
    (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    (freeGibbsDensityOperator (fun i => ε i - μ) β).expectation
        (Common.finiteHilbertOperatorAlgEquiv A) =
      Common.summableDiagonalTraceRatioLinear
        (Common.diagonalEvolution
          (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) (-β))
        ⟨A, Summable.of_finite⟩ := by
  have hE :
      Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ =
        fermionEnergy (fun i => ε i - μ) := by
    funext n
    exact Common.grandCanonicalEnergy_eq_shifted ε μ n
  rw [hE]
  exact freeGibbsDensityOperator_expectation_eq_summableDiagonalTraceRatioLinear
    (fun i => ε i - μ) β A

end
end Fermionic
end SecondQuantization
