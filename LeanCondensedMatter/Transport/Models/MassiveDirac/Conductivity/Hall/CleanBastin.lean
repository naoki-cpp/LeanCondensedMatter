import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.CleanLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.Conductivity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Clean Bastin Hall conductivity for the massive Dirac benchmark

The Bastin analysis upstream produces an occupation-weighted clean pair integral without attaching
physical conductivity units. This file restores the Bastin trace prefactor `ℏ/(2π)`, the angular
factor `2π`, and the physical-momentum measure `d²p/(2πℏ)²`.

The resulting finite-cutoff quantity agrees with the independently normalized intrinsic Hall
conductivity, and its ultraviolet limit gives the clean metallic massive-Dirac benchmark.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Scalar prefactor that converts the canonical traced Bastin energy kernel to the static Hall
response before the momentum measure is applied. Because the current vertices already contain the
charge `-e`, this factor carries no additional charge power. -/
def bastinTraceHallPrefactor (hbar : ℝ) : ℝ :=
  hbar / (2 * Real.pi)

/-- Finite-cutoff Hall response obtained from the canonical occupation-weighted clean Bastin-pair
radial integral, the Bastin trace normalization, the angular integral, and the physical-momentum
measure. -/
def bastinCleanHallConductivityCutoff
    (e hbar m εF Λ : ℝ) : ℝ :=
  bastinTraceHallPrefactor hbar *
    (2 * Real.pi * momentumMeasurePrefactor hbar) *
      zeroTemperatureOccupiedCleanInterbandBastinPairCutoff e m εF Λ

/-- The canonical clean radial Bastin-pair integral has exactly the same finite-cutoff normalization
as the canonical occupation-derived intrinsic Hall conductivity. -/
theorem bastinCleanHallConductivityCutoff_eq_intrinsicHallConductivityCutoff
    (e hbar m εF Λ : ℝ) :
    bastinCleanHallConductivityCutoff e hbar m εF Λ =
      intrinsicHallConductivityCutoff e hbar m εF Λ := by
  unfold bastinCleanHallConductivityCutoff
  rw [zeroTemperatureOccupiedCleanInterbandBastinPairCutoff_eq]
  unfold bastinTraceHallPrefactor intrinsicHallConductivityCutoff
    intrinsicHallPrefactorFromMomentumMeasure
  field_simp [Real.pi_ne_zero]

/-- Removing the finite radial UV cutoff from the integrated occupation-weighted clean Bastin-pair
profile reproduces the clean metallic intrinsic Hall conductivity. This uses the already-proved
cutoff limit; it is not a finite-broadening/momentum limit interchange. -/
theorem tendsto_bastinCleanHallConductivityCutoff_atTop
    (e hbar m εF : ℝ) (hmF : |m| ≤ εF) :
    Tendsto (bastinCleanHallConductivityCutoff e hbar m εF) atTop
      (nhds (intrinsicHallConductivity e hbar m εF)) := by
  refine (tendsto_intrinsicHallConductivityCutoff_atTop e hbar m εF hmF).congr' ?_
  filter_upwards with Λ
  exact (bastinCleanHallConductivityCutoff_eq_intrinsicHallConductivityCutoff
    e hbar m εF Λ).symm

/-- Closed massive-Dirac benchmark reached by the integrated clean Bastin-pair profile,
`σxy = -(e²/2h) (m/εF)`, including the massless endpoint. -/
theorem tendsto_bastinCleanHallConductivityCutoff_atTop_massiveDirac
    (e hbar m εF : ℝ) (hmF : |m| ≤ εF) :
    Tendsto (bastinCleanHallConductivityCutoff e hbar m εF) atTop
      (nhds (-(e ^ 2 / (2 * planckFromReduced hbar)) * (m / εF))) := by
  rw [← intrinsicHallConductivity_eq_massiveDirac e hbar m εF]
  exact tendsto_bastinCleanHallConductivityCutoff_atTop e hbar m εF hmF

end

end AnomalousHall.MassiveDirac
