import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSurfaceRadialPole
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial massive-Dirac Středa surface kernel

The clean metallic Fermi-surface shell is radial.  On the radial axis the same-band Hall block
vanishes, so the full regularized Středa surface primitive reduces to the two interband ordered
pairs isolated upstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- General ordered current block transported back to the concrete `2 × 2` matrix trace. -/
theorem currentBandBlockTrace_eq_matrixTrace
    (source target : Band) (e v m px py : ℝ) :
    currentBandBlockTrace source target e v m px py =
      Matrix.trace
        (bandProjector target v m px py * currentX e v *
          bandProjector source v m px py * currentY e v) := by
  unfold currentBandBlockTrace
  simpa [bandProjectorOperator, currentXOperator, currentYOperator, matrixOperator] using
    finiteDimensionalOperatorTrace_matrixOperator
      (bandProjector target v m px py * currentX e v *
        bandProjector source v m px py * currentY e v)

/-- On the radial axis the same-band `x-y` Hall current block vanishes. -/
theorem currentBandBlockTrace_same_radial
    (band : Band) (e v m p : ℝ) (hE : energy v m p 0 ≠ 0) :
    currentBandBlockTrace band band e v m p 0 = 0 := by
  rw [currentBandBlockTrace_eq_matrixTrace]
  have hEc : (((energy v m p 0 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  cases band <;>
    simp [bandProjector, Matrix.trace, Matrix.mul_apply, currentX, currentY,
      hamiltonian, sigmaX, sigmaY, sigmaZ] <;>
    field_simp [hEc] <;>
    ring

/-- The direct `x-y` diagonal Bastin/Středa block therefore vanishes on the radial axis. -/
theorem bastinXYBandBlockTrace_same_radial
    (band : Band) (e v m p : ℝ) (hE : energy v m p 0 ≠ 0) :
    bastinXYBandBlockTrace band band e v m p 0 = 0 := by
  rw [bastinXYBandBlockTrace_eq_currentBandBlockTrace]
  exact currentBandBlockTrace_same_radial band e v m p hE

/-- The reversed `y-x` diagonal block has the same radial vanishing. -/
theorem bastinYXBandBlockTrace_same_radial
    (band : Band) (e v m p : ℝ) (hE : energy v m p 0 ≠ 0) :
    bastinYXBandBlockTrace band band e v m p 0 = 0 := by
  rw [bastinYXBandBlockTrace_eq_reversedCurrentBandBlockTrace]
  exact currentBandBlockTrace_same_radial band e v m p hE

/-- Both same-band contributions to the Středa surface primitive vanish on the radial axis. -/
theorem diagonalStredaSurfaceTraceContribution_radial_eq_zero
    (e v m p probeEnergy broadening : ℝ) (hE : energy v m p 0 ≠ 0) :
    diagonalStredaSurfaceTraceContribution e v m p 0 probeEnergy broadening = 0 := by
  unfold diagonalStredaSurfaceTraceContribution stredaSurfaceBandPairContribution
  rw [bastinXYBandBlockTrace_same_radial .lower e v m p hE,
    bastinYXBandBlockTrace_same_radial .lower e v m p hE,
    bastinXYBandBlockTrace_same_radial .upper e v m p hE,
    bastinYXBandBlockTrace_same_radial .upper e v m p hE]
  simp

/-- Hence the complete radial Středa surface primitive is exactly its interband sector at positive
broadening. -/
theorem regularizedStredaSurfacePrimitiveTrace_radial_eq_interband
    (e v m p probeEnergy broadening : ℝ)
    (hE : energy v m p 0 ≠ 0) (hbroadening : 0 < broadening) :
    regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m p 0)
        (currentXOperator e v) (currentYOperator e v)
        probeEnergy broadening =
      interbandStredaSurfaceTraceContribution
        e v m p 0 probeEnergy broadening := by
  rw [regularizedStredaSurfacePrimitiveTrace_eq_diagonal_add_interband
    e v m p 0 probeEnergy broadening hE hbroadening,
    diagonalStredaSurfaceTraceContribution_radial_eq_zero e v m p probeEnergy broadening hE,
    zero_add]

end

end AnomalousHall.MassiveDirac
