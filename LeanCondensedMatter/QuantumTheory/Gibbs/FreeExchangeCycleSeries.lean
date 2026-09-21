import LeanCondensedMatter.Analysis.PowerSeries.LogAlgebra
import LeanCondensedMatter.Permutation.TraceLog
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeBoltzmannKernel

set_option linter.style.header false

/-!
# Free thermal exchange-cycle and grand-partition series

The one-particle Boltzmann kernel is independent of second quantization, and the permutation
connected-cycle backend is already formulated for arbitrary exchange weight `ζ`. This file records
the corresponding Gibbs-level specialization once.

The formal grand-partition product is shared only across the physical Bose/Fermi exchange weights
`ζ = +1` and `ζ = -1`. The explicit hypothesis on `freeExchangeGrandPartitionSeries` prevents the
product formula from being read as an arbitrary-complex-exchange construction.

Everything here is formal. No evaluation of the power-series variable at `t = 1` is used.
-/

namespace QuantumTheory

variable {Mode : Type*} [Fintype Mode]

/-- Formal finite-mode free grand-partition series for Bose/Fermi exchange weight `ζ`.

For `ζ = +1` this is the bosonic product `∏ᵢ (1 - qᵢ t)⁻¹`. For `ζ = -1` it is the
fermionic product `∏ᵢ (1 + qᵢ t)`, where `qᵢ = exp(-β εᵢ)`. The proof argument deliberately
restricts this product construction to those two exchange weights. -/
noncomputable def freeExchangeGrandPartitionSeries
    (ζ : ℂ) (_hζ : ζ = 1 ∨ ζ = -1) (ε : Mode → ℝ) (β : ℝ) : PowerSeries ℂ :=
  if ζ = 1 then
    ∏ i : Mode,
      (1 + (-ζ * Complex.exp (-(β : ℂ) * (ε i : ℂ))) • PowerSeries.X)⁻¹
  else
    ∏ i : Mode,
      (1 + (-ζ * Complex.exp (-(β : ℂ) * (ε i : ℂ))) • PowerSeries.X)

/-- The shared Bose/Fermi free grand product has unit constant coefficient. -/
@[simp]
theorem constantCoeff_freeExchangeGrandPartitionSeries
    (ζ : ℂ) (hζ : ζ = 1 ∨ ζ = -1) (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.constantCoeff (freeExchangeGrandPartitionSeries ζ hζ ε β) = 1 := by
  classical
  rcases hζ with hζ | hζ
  · subst ζ
    simp [freeExchangeGrandPartitionSeries]
  · subst ζ
    simp [freeExchangeGrandPartitionSeries]

/-- The formal logarithm of the shared Bose/Fermi free grand product is the exchange-weighted
modewise trace-log. -/
theorem logOf_freeExchangeGrandPartitionSeries_eq_sum_log
    (ζ : ℂ) (hζ : ζ = 1 ∨ ζ = -1) (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf (freeExchangeGrandPartitionSeries ζ hζ ε β) =
      (-ζ⁻¹) • ∑ i : Mode,
        PowerSeries.rescale
          (-ζ * Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  rcases hζ with hζ | hζ
  · subst ζ
    simp only [freeExchangeGrandPartitionSeries]
    calc
      PowerSeries.logOf
          (∏ i : Mode,
            (1 + (-(1 : ℂ) * Complex.exp (-(β : ℂ) * (ε i : ℂ))) •
              PowerSeries.X)⁻¹) =
          ∑ i : Mode,
            PowerSeries.logOf
              ((1 + (-(1 : ℂ) * Complex.exp (-(β : ℂ) * (ε i : ℂ))) •
                PowerSeries.X)⁻¹) := by
        simpa using
          PowerSeries.logOf_finset_prod (Finset.univ : Finset Mode) _
            (fun i => by simp)
      _ = ∑ i : Mode,
          -PowerSeries.rescale
            (-(1 : ℂ) * Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
        apply Fintype.sum_congr
        intro i
        rw [PowerSeries.logOf_inv (by simp), PowerSeries.logOf_one_add_smul_X]
      _ = -∑ i : Mode,
          PowerSeries.rescale
            (-(1 : ℂ) * Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
        rw [Finset.sum_neg_distrib]
      _ = (-((1 : ℂ)⁻¹)) • ∑ i : Mode,
          PowerSeries.rescale
            (-(1 : ℂ) * Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
        simp
  · subst ζ
    have hne : (-1 : ℂ) ≠ 1 := by norm_num
    simp only [freeExchangeGrandPartitionSeries, if_neg hne]
    rw [PowerSeries.logOf_finset_prod (Finset.univ : Finset Mode)
      (fun i =>
        1 + (-(-1 : ℂ) * Complex.exp (-(β : ℂ) * (ε i : ℂ))) • PowerSeries.X)
      (fun i => by simp)]
    simp_rw [PowerSeries.logOf_one_add_smul_X]
    simp

/-- For the diagonal free Boltzmann kernel and nonzero exchange weight `ζ`, the connected-cycle
series is the modewise formal trace-log

`-(1/ζ) Σᵢ log(1 - ζ qᵢ t)`, where `qᵢ = exp(-β εᵢ)`. -/
theorem permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
    (ζ : ℂ) (hζ : ζ ≠ 0) (ε : Mode → ℝ) (β : ℝ) :
    Combinatorics.permutationConnectedCycleSeries ζ (freeBoltzmannModeKernel ε β) =
      (-ζ⁻¹) • ∑ i : Mode,
        PowerSeries.rescale
          (-ζ * Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  classical
  rw [freeBoltzmannModeKernel_eq_diagonal]
  simpa using
    (Combinatorics.permutationConnectedCycleSeries_diagonal_eq_neg_inv_smul_sum_log
      ζ (fun i : Mode => Complex.exp (-(β : ℂ) * (ε i : ℂ))) hζ)

/-- For either physical exchange weight, the logarithm of the shared free grand product equals the
connected-cycle series of the free Boltzmann kernel. -/
theorem logOf_freeExchangeGrandPartitionSeries_eq_permutationConnectedCycleSeries
    (ζ : ℂ) (hζ : ζ = 1 ∨ ζ = -1) (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf (freeExchangeGrandPartitionSeries ζ hζ ε β) =
      Combinatorics.permutationConnectedCycleSeries ζ (freeBoltzmannModeKernel ε β) := by
  have hζ0 : ζ ≠ 0 := by
    rcases hζ with hζ | hζ
    · rw [hζ]
      norm_num
    · rw [hζ]
      norm_num
  rw [logOf_freeExchangeGrandPartitionSeries_eq_sum_log ζ hζ ε β]
  exact
    (permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
      ζ hζ0 ε β).symm

end QuantumTheory
