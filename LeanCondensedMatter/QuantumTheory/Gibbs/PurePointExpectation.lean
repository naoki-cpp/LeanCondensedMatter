import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

/-!
# Integrable pure-point Gibbs expectations

A pure-point Gibbs density state exists under summability of its Boltzmann weights.  Diagonal
observables described only by spectral data may nevertheless be unbounded, so their expectations
are represented separately as absolutely summable real series rather than being coerced into the
bounded `DensityOperator.expectation` API.
-/

noncomputable section

namespace QuantumTheory

variable {ι : Type*}

/-- Absolute Gibbs integrability of a real diagonal observable `aᵢ`.  This is intentionally
stronger than existence of the Gibbs state and is the domain condition for the series expectation
below. -/
def PurePointGibbsIntegrableDiagonal (E : ι → ℝ) (β : ℝ) (a : ι → ℝ) : Prop :=
  Summable fun i => ‖purePointGibbsProbability E β i * a i‖

/-- The pure-point Gibbs expectation of an integrable real diagonal observable, represented by its
spectral series. -/
noncomputable def purePointGibbsDiagonalExpectation
    (E : ι → ℝ) (β : ℝ) (a : ι → ℝ) : ℝ :=
  ∑' i, purePointGibbsProbability E β i * a i

/-- Gibbs integrability gives ordinary summability of the diagonal expectation series. -/
theorem purePointGibbsIntegrableDiagonal_summable
    (E : ι → ℝ) (β : ℝ) (a : ι → ℝ)
    (hint : PurePointGibbsIntegrableDiagonal E β a) :
    Summable fun i => purePointGibbsProbability E β i * a i :=
  Summable.of_norm hint

/-- An integrable real diagonal observable has the expected `HasSum`. -/
theorem hasSum_purePointGibbsDiagonalExpectation
    (E : ι → ℝ) (β : ℝ) (a : ι → ℝ)
    (hint : PurePointGibbsIntegrableDiagonal E β a) :
    HasSum (fun i => purePointGibbsProbability E β i * a i)
      (purePointGibbsDiagonalExpectation E β a) :=
  (purePointGibbsIntegrableDiagonal_summable E β a hint).hasSum

/-- The constant-one diagonal observable is Gibbs integrable whenever the Gibbs state exists. -/
theorem purePointGibbsIntegrableDiagonal_one [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable E β) :
    PurePointGibbsIntegrableDiagonal E β (fun _ => 1) := by
  unfold PurePointGibbsIntegrableDiagonal
  simpa using (hasSum_purePointGibbsProbability E β hsum).summable.norm

/-- The spectral-series expectation has the same normalization as the density-state API. -/
@[simp]
theorem purePointGibbsDiagonalExpectation_one [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable E β) :
    purePointGibbsDiagonalExpectation E β (fun _ => 1) = 1 := by
  unfold purePointGibbsDiagonalExpectation
  simpa using (hasSum_purePointGibbsProbability E β hsum).tsum_eq

/-- Integrability is stable under pointwise addition of real diagonal observables. -/
theorem purePointGibbsIntegrableDiagonal_add
    (E : ι → ℝ) (β : ℝ) (a b : ι → ℝ)
    (ha : PurePointGibbsIntegrableDiagonal E β a)
    (hb : PurePointGibbsIntegrableDiagonal E β b) :
    PurePointGibbsIntegrableDiagonal E β (fun i => a i + b i) := by
  have hsa := purePointGibbsIntegrableDiagonal_summable E β a ha
  have hsb := purePointGibbsIntegrableDiagonal_summable E β b hb
  apply Summable.norm
  simpa [mul_add] using hsa.add hsb

/-- Gibbs expectation is additive on integrable real diagonal observables. -/
theorem purePointGibbsDiagonalExpectation_add
    (E : ι → ℝ) (β : ℝ) (a b : ι → ℝ)
    (ha : PurePointGibbsIntegrableDiagonal E β a)
    (hb : PurePointGibbsIntegrableDiagonal E β b) :
    purePointGibbsDiagonalExpectation E β (fun i => a i + b i) =
      purePointGibbsDiagonalExpectation E β a +
        purePointGibbsDiagonalExpectation E β b := by
  unfold purePointGibbsDiagonalExpectation
  have hsa := purePointGibbsIntegrableDiagonal_summable E β a ha
  have hsb := purePointGibbsIntegrableDiagonal_summable E β b hb
  rw [← hsa.tsum_add hsb]
  apply tsum_congr
  intro i
  ring

/-- The existing pure-point energy-integrability predicate is exactly the generic diagonal
integrability condition specialized to the energy data themselves. -/
theorem purePointGibbsEnergyIntegrable_iff_integrableDiagonal
    (E : ι → ℝ) (β : ℝ) :
    PurePointGibbsEnergyIntegrable E β ↔ PurePointGibbsIntegrableDiagonal E β E :=
  Iff.rfl

/-- Thermal expectation of potentially unbounded pure-point energy data.  Its meaningful domain is
`PurePointGibbsSummable E β` together with `PurePointGibbsEnergyIntegrable E β`. -/
noncomputable def purePointGibbsEnergyExpectation (E : ι → ℝ) (β : ℝ) : ℝ :=
  purePointGibbsDiagonalExpectation E β E

/-- Under explicit state-existence and energy-integrability hypotheses, the pure-point energy
expectation is represented by an absolutely convergent spectral series. -/
theorem hasSum_purePointGibbsEnergyExpectation [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (_hsum : PurePointGibbsSummable E β)
    (hint : PurePointGibbsEnergyIntegrable E β) :
    HasSum (fun i => purePointGibbsProbability E β i * E i)
      (purePointGibbsEnergyExpectation E β) := by
  exact hasSum_purePointGibbsDiagonalExpectation E β E hint

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
