import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.Gibbs.DiagonalEnergy
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Countable pure-point Gibbs states

This module constructs a genuine infinite-dimensional Gibbs density state directly from pure-point
spectral data.  The Hamiltonian is represented only by a Hilbert basis and real energy values; it is
not coerced into a bounded continuous linear map.

The sole state-existence hypothesis is absolute summability of the Boltzmann weights.  Under a
nonempty spectral index this implies strict positivity of the partition function, so the canonical
`diagonalDensityOperator` constructor provides the normalized trace-class state.  Potentially
unbounded energy expectations and entropy are kept behind separate visible finiteness conditions.
-/

noncomputable section

namespace QuantumTheory

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The positive real Boltzmann weight `exp (-β Eᵢ)` attached to one pure-point energy level. -/
noncomputable def purePointBoltzmannWeight (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (-β * E i)

@[simp]
theorem purePointBoltzmannWeight_pos (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 < purePointBoltzmannWeight E β i := by
  simpa [purePointBoltzmannWeight] using Real.exp_pos (-β * E i)

@[simp]
theorem purePointBoltzmannWeight_nonneg (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 ≤ purePointBoltzmannWeight E β i :=
  (purePointBoltzmannWeight_pos E β i).le

/-- Absolute Boltzmann summability for a pure-point Gibbs state.  This is the explicit trace-class
hypothesis consumed by the generic diagonal density-state constructor. -/
def PurePointGibbsSummable (E : ι → ℝ) (β : ℝ) : Prop :=
  Summable fun i => ‖purePointBoltzmannWeight E β i‖

/-- The pure-point partition function `Z(β) = ∑ᵢ exp (-β Eᵢ)`. -/
noncomputable def purePointPartitionFunction (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑' i, purePointBoltzmannWeight E β i

/-- Absolute Boltzmann summability implies ordinary summability of the positive weights. -/
theorem purePointBoltzmannWeight_summable (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β) :
    Summable (purePointBoltzmannWeight E β) :=
  Summable.of_norm hsum

/-- For a nonempty pure-point spectrum, a summable family of strictly positive Boltzmann weights
has a strictly positive partition function. -/
theorem purePointPartitionFunction_pos [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β) :
    0 < purePointPartitionFunction E β := by
  classical
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  rw [purePointPartitionFunction]
  exact (purePointBoltzmannWeight_summable E β hsum).tsum_pos
    (fun j => purePointBoltzmannWeight_nonneg E β j) i
    (purePointBoltzmannWeight_pos E β i)

/-- The normalized Gibbs probability of one pure-point energy level. -/
noncomputable def purePointGibbsProbability (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  (purePointPartitionFunction E β)⁻¹ * purePointBoltzmannWeight E β i

@[simp]
theorem purePointGibbsProbability_nonneg [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β) (i : ι) :
    0 ≤ purePointGibbsProbability E β i := by
  exact mul_nonneg (inv_nonneg.mpr (purePointPartitionFunction_pos E β hsum).le)
    (purePointBoltzmannWeight_nonneg E β i)

/-- The normalized pure-point Gibbs probabilities sum to one. -/
theorem hasSum_purePointGibbsProbability [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β) :
    HasSum (purePointGibbsProbability E β) 1 := by
  have hZ : 0 < purePointPartitionFunction E β :=
    purePointPartitionFunction_pos E β hsum
  change HasSum
    (fun i => (purePointPartitionFunction E β)⁻¹ * purePointBoltzmannWeight E β i) 1
  have hscaled :=
    (purePointBoltzmannWeight_summable E β hsum).hasSum.mul_left
      (purePointPartitionFunction E β)⁻¹
  change HasSum
    (fun i => (purePointPartitionFunction E β)⁻¹ * purePointBoltzmannWeight E β i)
      ((purePointPartitionFunction E β)⁻¹ * purePointPartitionFunction E β) at hscaled
  rw [inv_mul_cancel₀ (ne_of_gt hZ)] at hscaled
  exact hscaled

/-- The canonical pure-point Gibbs density operator.  No bounded Hamiltonian is introduced: the
state is built directly from the spectral Boltzmann weights. -/
noncomputable def purePointGibbsDensityOperator [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β) : DensityOperator H :=
  diagonalDensityOperator b (purePointBoltzmannWeight E β) hsum
    (purePointBoltzmannWeight_nonneg E β)
    (by simpa [purePointPartitionFunction] using purePointPartitionFunction_pos E β hsum)

/-- The pure-point Gibbs density operator acts diagonally with the normalized Boltzmann
probabilities. -/
@[simp]
theorem purePointGibbsDensityOperator_apply_basis [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β) (i : ι) :
    (purePointGibbsDensityOperator b E β hsum).op (b i) =
      (purePointGibbsProbability E β i : ℂ) • b i := by
  have hZ : 0 < ∑' j, purePointBoltzmannWeight E β j := by
    simpa [purePointPartitionFunction] using purePointPartitionFunction_pos E β hsum
  simpa [purePointGibbsDensityOperator, purePointGibbsProbability,
    purePointPartitionFunction, normalizedDiagonalWeight] using
    diagonalDensityOperator_apply_basis b (purePointBoltzmannWeight E β) hsum
      (purePointBoltzmannWeight_nonneg E β) hZ i

/-- Finiteness condition for the mean energy when the pure-point energy data are not represented by
a bounded `Observable`.  State existence alone does not imply this stronger weighted summability. -/
def PurePointGibbsEnergyIntegrable (E : ι → ℝ) (β : ℝ) : Prop :=
  Summable fun i => ‖purePointGibbsProbability E β i * E i‖

/-- When the same energy data do come from a bounded observable, the generic bounded expectation
API gives the expected weighted pure-point energy series.  Genuinely unbounded energy data should
instead carry `PurePointGibbsEnergyIntegrable` explicitly. -/
theorem energyExpValue_purePointGibbsDensityOperator_eq_tsum [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β) (Hop : Observable H)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i) :
    energyExpValue (purePointGibbsDensityOperator b E β hsum) Hop =
      ∑' i, purePointGibbsProbability E β i * E i := by
  exact energyExpValue_eq_tsum_common_eigenbasis
    (purePointGibbsDensityOperator b E β hsum) Hop b
    (purePointGibbsProbability E β) E
    (purePointGibbsDensityOperator_apply_basis b E β hsum) hE

/-- On a finite spectral index, the Boltzmann summability hypothesis is automatic. -/
theorem purePointGibbsSummable_of_finite [Finite ι] (E : ι → ℝ) (β : ℝ) :
    PurePointGibbsSummable E β := by
  exact Summable.of_finite

/-- Finite pure-point Gibbs states are direct specializations of the same dimension-independent
constructor; no separate finite-state implementation is needed. -/
noncomputable def finitePurePointGibbsDensityOperator [Finite ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ) : DensityOperator H :=
  purePointGibbsDensityOperator b E β (purePointGibbsSummable_of_finite E β)

@[simp]
theorem finitePurePointGibbsDensityOperator_apply_basis [Finite ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ) (i : ι) :
    (finitePurePointGibbsDensityOperator b E β).op (b i) =
      (purePointGibbsProbability E β i : ℂ) • b i := by
  exact purePointGibbsDensityOperator_apply_basis b E β (purePointGibbsSummable_of_finite E β) i

end QuantumTheory
