import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.CauchyCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ConnectedSeries

set_option linter.style.header false

/-!
# Power-series form of the two-point linked-cluster theorem

The coefficientwise identity from `CauchyCoefficient` is already the Cauchy product of the connected
two-point coefficients with the normalized Dyson partition coefficients.  This file identifies that
second factor with `normalizeByConstantCoeff (dysonPartitionSeries ...)`, lifts the coefficientwise
identity to an equality of formal power series, and cancels the vacuum series from the existing
vacuum-normalized two-point series.

No diagrammatic decomposition is introduced here: this is only the formal power-series algebra after
the canonical external-slot fiber proof.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- The coefficients of the normalized Dyson partition series are exactly the normalized Dyson
partition coefficients used by the fiber Cauchy theorem. -/
theorem coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) =
      normalizedDysonPartitionCoeff ε β V n := by
  simp [PowerSeries.coeff_normalizeByConstantCoeff,
    constantCoeff_dysonPartitionSeries, coeff_dysonPartitionSeries,
    normalizedDysonPartitionCoeff, div_eq_mul_inv, mul_comm]

private theorem sum_antidiagonal_eq_sum_range_succ
    {R : Type*} [AddCommMonoid R] (f : ℕ → ℕ → R) (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n, f p.1 p.2) =
      ∑ m ∈ Finset.range (n + 1), f m (n - m) := by
  let e : ℕ ↪ ℕ × ℕ :=
    ⟨fun m => (m, n - m), by
      intro a b h
      exact congrArg Prod.fst h⟩
  have hanti : Finset.antidiagonal n = (Finset.range (n + 1)).map e := by
    ext p
    constructor
    · intro hp
      have hpadd : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
      have hp_le : p.1 ≤ n := by omega
      apply Finset.mem_map.2
      refine ⟨p.1, Finset.mem_range.2 (by omega), ?_⟩
      apply Prod.ext
      · rfl
      · dsimp [e]
        omega
    · intro hp
      obtain ⟨m, hm, rfl⟩ := Finset.mem_map.1 hp
      apply Finset.mem_antidiagonal.2
      dsimp [e]
      have hm_le : m ≤ n := by
        have := Finset.mem_range.1 hm
        omega
      omega
  rw [hanti, Finset.sum_map]
  rfl

/-- **Formal Cauchy product for the two-point Dyson series.** The complete two-point series equals
the connected two-point series times the normalized vacuum partition series. -/
theorem twoPointDysonSeries_eq_connectedTwoPointDysonSeries_mul_normalizeByConstantCoeff
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    twoPointDysonSeries ε β g i j τ τ' =
      connectedTwoPointDysonSeries ε β g i j τ τ' *
        PowerSeries.normalizeByConstantCoeff
          (dysonPartitionSeries ε β (quarticInteraction g)) := by
  ext n
  rw [coeff_twoPointDysonSeries, PowerSeries.coeff_mul]
  rw [sum_antidiagonal_eq_sum_range_succ
    (f := fun a b =>
      PowerSeries.coeff a (connectedTwoPointDysonSeries ε β g i j τ τ') *
        PowerSeries.coeff b
          (PowerSeries.normalizeByConstantCoeff
            (dysonPartitionSeries ε β (quarticInteraction g))))]
  simp only [coeff_connectedTwoPointDysonSeries,
    coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]
  exact twoPointDysonCoefficient_eq_sum_connected_mul_normalizedDysonPartitionCoeff
    ε β hβ g i j τ τ' n

/-- **Finite-mode fermionic two-point linked-cluster theorem.** For the imaginary-time Dyson series
built from free Gibbs expectations and a quartic interaction, with the repository's canonical
time-order/equal-time convention, vacuum normalization leaves exactly the sum of externally
connected two-point diagrams. -/
theorem vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    vacuumNormalizedTwoPointDysonSeries ε β g i j τ τ' =
      connectedTwoPointDysonSeries ε β g i j τ τ' := by
  let Z := PowerSeries.normalizeByConstantCoeff
    (dysonPartitionSeries ε β (quarticInteraction g))
  have hZ : Z ≠ 0 := by
    intro hz
    have hcoeff := congrArg PowerSeries.constantCoeff hz
    simpa [Z, constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries] using hcoeff
  apply mul_right_cancel₀ hZ
  rw [vacuumNormalizedTwoPointDysonSeries_mul_normalizeByConstantCoeff]
  exact twoPointDysonSeries_eq_connectedTwoPointDysonSeries_mul_normalizeByConstantCoeff
    ε β hβ g i j τ τ'

end Fermionic
end SecondQuantization
