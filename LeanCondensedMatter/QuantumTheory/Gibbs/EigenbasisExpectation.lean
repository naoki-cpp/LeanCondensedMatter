import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis
import LeanCondensedMatter.QuantumTheory.Gibbs.DiagonalEnergy

/-!
# Gibbs energy expectations in an energy eigenbasis

A pure-point Gibbs density state exists under summability of its Boltzmann weights. Potentially
unbounded energy data require the stronger weighted summability condition
`EigenbasisGibbsEnergyIntegrable`; their expectation is therefore represented directly as an
absolutely convergent real series rather than through a parallel generic diagonal-observable API.
-/

noncomputable section

namespace QuantumTheory

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

/-- When the same energy data do come from a bounded observable, the generic bounded expectation
API gives the expected weighted pure-point energy series.  Genuinely unbounded energy data should
instead carry `EigenbasisGibbsEnergyIntegrable` explicitly. -/
theorem energyExpValue_eigenbasisGibbsDensityOperator_eq_tsum [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) (Hop : Observable H)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i) :
    energyExpValue (eigenbasisGibbsDensityOperator b E β hsum) Hop =
      ∑' i, eigenbasisGibbsProbability E β i * E i := by
  exact energyExpValue_eq_tsum_common_eigenbasis
    (eigenbasisGibbsDensityOperator b E β hsum) Hop b
    (eigenbasisGibbsProbability E β) E
    (eigenbasisGibbsDensityOperator_apply_basis b E β hsum) hE

/-- If the same energy data are represented by a bounded observable, the spectral-series energy
expectation agrees with the canonical density-state energy expectation. -/
theorem eigenbasisGibbsEnergyExpectation_eq_energyExpValue [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) (Hop : Observable H)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i) :
    eigenbasisGibbsEnergyExpectation E β =
      energyExpValue (eigenbasisGibbsDensityOperator b E β hsum) Hop := by
  rw [energyExpValue_eigenbasisGibbsDensityOperator_eq_tsum b E β hsum Hop hE]
  rfl

end QuantumTheory
