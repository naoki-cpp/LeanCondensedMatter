import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PairBerry
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Kinematics
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial domination data for the massive-Dirac Bastin limit

Interchanging the positive-zero-broadening limit with the finite radial momentum integral uses a
model-specific momentum-independent lower bound on the interband gap when the Dirac mass is
positive.

On the radial axis `pᵧ = 0`, the interband current trace is also purely imaginary. This file records
those two inputs in a form adapted to uniform spectator and dominated-convergence bounds.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- The absolute interband gap is bounded below by `2m`, uniformly in momentum. -/
theorem two_mul_mass_le_abs_interbandEnergyGap
    (band : Band) (v m px py : ℝ) :
    2 * m ≤ |interbandEnergyGap band v m px py| := by
  rw [interbandEnergyGap_eq]
  have hE := energy_nonneg v m px py
  have hmE := mass_le_energy v m px py
  cases band <;> simp [bandSign, abs_of_nonneg hE] <;> linarith

/-- A pole window narrower than the mass gap is valid simultaneously at every momentum. -/
theorem radius_lt_abs_interbandEnergyGap_of_lt_two_mul_mass
    (band : Band) (v m px py radius : ℝ) (_hm : 0 < m)
    (hradius : radius < 2 * m) :
    radius < |interbandEnergyGap band v m px py| := by
  exact lt_of_lt_of_le hradius
    (two_mul_mass_le_abs_interbandEnergyGap band v m px py)

/-- On the radial axis the gauge-independent Hall interband force numerator is purely imaginary.
Its imaginary coefficient is the one already used by the Berry-curvature bridge. -/
theorem forceMatrixTraceNumerator_radial
    (band : Band) (v m p : ℝ) (hE : energy v m p 0 ≠ 0) :
    forceMatrixTraceNumerator .x .y band v m p 0 =
      (((-(bandSign band * m * v ^ 2 / energy v m p 0) : ℝ) : ℂ)) * Complex.I := by
  have hEc : (((energy v m p 0 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  cases band <;>
    simp [forceMatrixTraceNumerator, oppositeBand, bandProjector, Matrix.trace,
      Matrix.mul_apply, velocity, directionPauli, hamiltonian, sigmaX, sigmaY, sigmaZ] <;>
    field_simp [hEc] <;>
    ring_nf

/-- The physical Hall interband current trace on the radial axis is therefore purely imaginary. -/
theorem interbandCurrentTrace_radial
    (band : Band) (e v m p : ℝ) (hE : energy v m p 0 ≠ 0) :
    interbandCurrentTrace .x .y band e v m p 0 =
      (((e ^ 2 : ℝ) : ℂ)) *
        (((-(bandSign band * m * v ^ 2 / energy v m p 0) : ℝ) : ℂ)) * Complex.I := by
  rw [interbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator .x .y,
    forceMatrixTraceNumerator_radial band v m p hE]
  ring

/-- The natural radial `x-y` Bastin block at a target-band pole is the opposite-band current trace,
now in explicit purely-imaginary form. -/
theorem bastinXYBandBlockTrace_opposite_source_radial
    (band : Band) (e v m p : ℝ) (hE : energy v m p 0 ≠ 0) :
    bastinBandBlockTrace .x .y (oppositeBand band) band e v m p 0 =
      (((e ^ 2 : ℝ) : ℂ)) *
        (((bandSign band * m * v ^ 2 / energy v m p 0 : ℝ) : ℂ)) * Complex.I := by
  rw [bastinXYBandBlockTrace_opposite_source,
    interbandCurrentTrace_radial (oppositeBand band) e v m p hE]
  cases band <;> simp [oppositeBand, bandSign]
  all_goals ring

/-- The radial `y-x` block has the opposite imaginary sign. -/
theorem bastinYXBandBlockTrace_opposite_source_radial
    (band : Band) (e v m p : ℝ) (hE : energy v m p 0 ≠ 0) :
    bastinBandBlockTrace .y .x (oppositeBand band) band e v m p 0 =
      -((((e ^ 2 : ℝ) : ℂ)) *
        (((bandSign band * m * v ^ 2 / energy v m p 0 : ℝ) : ℂ)) * Complex.I) := by
  rw [bastinYXBandBlockTrace_opposite_source,
    interbandCurrentTrace_radial band e v m p hE]
  push_cast
  ring

end

end AnomalousHall.MassiveDirac
