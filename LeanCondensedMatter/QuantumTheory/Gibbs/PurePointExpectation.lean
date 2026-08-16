import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

/-!
# Integrable pure-point Gibbs energy expectations

A pure-point Gibbs density state exists under summability of its Boltzmann weights. Potentially
unbounded energy data require the stronger weighted summability condition
`PurePointGibbsEnergyIntegrable`; their expectation is therefore represented directly as an
absolutely convergent real series rather than through a parallel generic diagonal-observable API.
-/

noncomputable section

namespace QuantumTheory

variable {ι : Type*}

/-- Thermal expectation of potentially unbounded pure-point energy data. -/
noncomputable def purePointGibbsEnergyExpectation (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑' i, purePointGibbsProbability E β i * E i

/-- Energy integrability gives the expected absolutely convergent spectral series. -/
theorem hasSum_purePointGibbsEnergyExpectation
    (E : ι → ℝ) (β : ℝ) (hint : PurePointGibbsEnergyIntegrable E β) :
    HasSum (fun i => purePointGibbsProbability E β i * E i)
      (purePointGibbsEnergyExpectation E β) := by
  exact (Summable.of_norm hint).hasSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If the same energy data are represented by a bounded observable, the spectral-series energy
expectation agrees with the canonical density-state energy expectation. -/
theorem purePointGibbsEnergyExpectation_eq_energyExpValue [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β) (Hop : Observable H)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i) :
    purePointGibbsEnergyExpectation E β =
      energyExpValue (purePointGibbsDensityOperator b E β hsum) Hop := by
  rw [energyExpValue_purePointGibbsDensityOperator_eq_tsum b E β hsum Hop hE]
  rfl

end QuantumTheory
