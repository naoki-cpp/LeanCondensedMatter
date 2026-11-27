import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.Gibbs.EnergyExpectation

/-!
# Gibbs energy expectations in an energy eigenbasis

A pure-point Gibbs density state exists under summability of its Boltzmann weights. Potentially
unbounded energy data require the stronger weighted summability condition
`EigenbasisGibbsEnergyIntegrable`; their expectation is therefore represented directly as an
absolutely convergent real series rather than through a parallel generic diagonal-observable API. Common-basis bounded energy
expectations provide the bridge to density-operator expectations.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι : Type*}

/-- Thermal expectation of potentially unbounded pure-point energy data. -/
noncomputable def eigenbasisGibbsEnergyExpectation (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑' i, eigenbasisGibbsProbability E β i * E i

/-- Energy integrability gives the expected absolutely convergent spectral series. -/
theorem hasSum_eigenbasisGibbsEnergyExpectation
    (E : ι → ℝ) (β : ℝ) (hint : EigenbasisGibbsEnergyIntegrable E β) :
    HasSum (fun i => eigenbasisGibbsProbability E β i * E i)
      (eigenbasisGibbsEnergyExpectation E β) := by
  exact (Summable.of_norm hint).hasSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If `ρ` and `Hop` are diagonal in the same Hilbert basis, then
`energyExpValue ρ Hop = ∑' i, w i * E i`. The series is absolutely convergent through the generic
Hilbert–Schmidt diagonal-expectation theorem. -/
theorem energyExpValue_eq_tsum_common_eigenbasis (ρ : DensityOperator H) (Hop : Observable H)
    (b : HilbertBasis ι ℂ H) (w E : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i) :
    energyExpValue ρ Hop = ∑' i, w i * E i := by
  change ρ.observableExpectation Hop = ∑' i, w i * E i
  rw [ρ.observableExpectation_eq_tsum_diagonal Hop b w hρ]
  apply tsum_congr
  intro i
  have hdiag : diagonalExpectationValue Hop.1 Hop.2 (b i) = E i := by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, hE i, inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  rw [hdiag]

/-- If the same energy data are represented by a bounded observable, the spectral-series energy
expectation agrees with the density-operator energy expectation. -/
theorem eigenbasisGibbsEnergyExpectation_eq_energyExpValue [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) (Hop : Observable H)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i) :
    eigenbasisGibbsEnergyExpectation E β =
      energyExpValue (eigenbasisGibbsDensityOperator b E β hsum) Hop := by
  simpa only [eigenbasisGibbsEnergyExpectation] using
    (energyExpValue_eq_tsum_common_eigenbasis
      (eigenbasisGibbsDensityOperator b E β hsum) Hop b
      (eigenbasisGibbsProbability E β) E
      (eigenbasisGibbsDensityOperator_apply_basis b E β hsum) hE).symm

end QuantumTheory
