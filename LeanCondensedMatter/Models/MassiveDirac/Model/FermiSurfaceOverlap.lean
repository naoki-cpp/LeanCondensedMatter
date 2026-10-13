import LeanCondensedMatter.Models.MassiveDirac.Model.FermiSurface
import LeanCondensedMatter.Models.MassiveDirac.Model.Spectral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Upper-band Fermi-surface projector overlap

The gauge-independent projector trace and its real-valued on-shell Fermi-circle overlap
follow from the clean massive-Dirac spectral projectors and Fermi radius. These statements
do not assume scalar disorder, a scattering rate, or a relaxation-time approximation.

For scalar-impurity scattering, the overlap is consumed downstream as the angular weight
in `Disorder.TransportRate`; transport relaxation factors remain owned by that module.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

private theorem upperBandProjectorOverlap_eq
    (v m px py qx qy : ℝ)
    (hp : energy v m px py ≠ 0) (hq : energy v m qx qy ≠ 0) :
    Matrix.trace
        (bandProjector .upper v m px py * bandProjector .upper v m qx qy) =
      (((1 +
        (v ^ 2 * (px * qx + py * qy) + m ^ 2) /
          (energy v m px py * energy v m qx qy)) / 2 : ℝ) : ℂ) := by
  have htrace (u v : InternalSpace.PauliAxis → ℂ) :
      Matrix.trace
          (((1 / 2 : ℂ) •
              ((1 : InternalSpace.PauliMatrix) + InternalSpace.pauliCombination u)) *
            ((1 / 2 : ℂ) •
              ((1 : InternalSpace.PauliMatrix) + InternalSpace.pauliCombination v))) =
        (1 + dotProduct u v) / 2 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [add_mul, one_mul, mul_add, mul_one]
    simp [InternalSpace.trace_pauliCombination_mul_pauliCombination]
    ring
  rw [bandProjector_eq_pauliCombination, bandProjector_eq_pauliCombination, htrace]
  rw [InternalSpace.dotProduct_pauliAxis]
  simp [diracPauliCoefficients]
  field_simp [hp, hq]

/-- Gauge-independent scalar-disorder overlap weight between an upper-band state chosen on the
positive `p_x` axis and a state at relative Fermi-circle angle `θ`. This is the canonical real
representative of `Tr(P_+(p) P_+(p'))`; the theorem below proves the lossless complex-valued bridge
in the metallic regime rather than projecting with `Complex.re`. -/
def upperBandFermiSurfaceScalarOverlapWeight
    (_v m fermiEnergy θ : ℝ) : ℝ :=
  (1 + m ^ 2 / fermiEnergy ^ 2 +
    (1 - m ^ 2 / fermiEnergy ^ 2) * Real.cos θ) / 2

/-- The real overlap weight embeds back into `ℂ` as exactly the projector trace on the Fermi circle.
This is the reality certificate for the physical scalar API whenever the Fermi radius is real and
the Fermi energy is nonzero. -/
theorem coe_upperBandFermiSurfaceScalarOverlapWeight_eq_projectorTrace
    (v m fermiEnergy θ : ℝ) (hv : v ≠ 0)
    (hmF : |m| ≤ fermiEnergy) (hfermiEnergy : fermiEnergy ≠ 0) :
    (upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ : ℂ) =
      Matrix.trace
        (bandProjector .upper v m (metallicFermiRadius v m fermiEnergy) 0 *
          bandProjector .upper v m
            (metallicFermiRadius v m fermiEnergy * Real.cos θ)
            (metallicFermiRadius v m fermiEnergy * Real.sin θ)) := by
  have hE := energy_metallicFermiRadius v m fermiEnergy hv hmF
  have hENe : energy v m (metallicFermiRadius v m fermiEnergy) 0 ≠ 0 := by
    rw [hE]
    exact hfermiEnergy
  rw [upperBandProjectorOverlap_eq]
  · rw [energy_polar_eq_radial, hE]
    have hpFproduct :
        metallicFermiRadius v m fermiEnergy *
              (metallicFermiRadius v m fermiEnergy * Real.cos θ) +
            0 * (metallicFermiRadius v m fermiEnergy * Real.sin θ) =
          metallicFermiRadius v m fermiEnergy ^ 2 * Real.cos θ := by
      ring
    rw [hpFproduct, metallicFermiRadius_sq v m fermiEnergy hmF]
    unfold upperBandFermiSurfaceScalarOverlapWeight
    push_cast
    (field_simp [hfermiEnergy, hv]; ring)
  · exact hENe
  · rw [energy_polar_eq_radial]
    exact hENe

end

end QuantumTheory.Models.MassiveDirac
