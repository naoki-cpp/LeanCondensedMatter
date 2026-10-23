import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
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

omit [LinearOrder Mode] in
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
  have hbasis : ∀ n : Occupation Mode,
      (Common.completedFiniteHilbertEquiv
        (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap
          (Common.completedHilbertBasis (Config := Occupation Mode) n) =
        Common.finiteHilbertBasis (Config := Occupation Mode) n := by
    intro n
    simpa only [Common.completedHilbertBasis_apply, Common.finiteHilbertBasis_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (Common.completedFiniteHilbertEquiv_basisState (Config := Occupation Mode) n)
  have htransport :=
    eigenbasisGibbsDensityOperator_intertwines
      (Common.completedHilbertBasis (Config := Occupation Mode))
      (Common.finiteHilbertBasis (Config := Occupation Mode))
      (fermionEnergy (fun i => ε i - μ)) β
      (eigenbasisGibbsSummable_of_finite
        (fermionEnergy (fun i => ε i - μ)) β)
      (Common.completedFiniteHilbertEquiv
        (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap
      hbasis
  simpa [Common.grandCanonicalGibbsDensityOperator,
    freeGibbsDensityOperator, hE] using htransport

omit [LinearOrder Mode] in
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
