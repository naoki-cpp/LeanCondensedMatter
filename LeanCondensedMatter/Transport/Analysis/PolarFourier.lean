import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.Core
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Analysis.FourierGeometry

set_option linter.style.header false

/-!
# Physical two-dimensional polar Fourier transform

The angular Fourier–Bessel kernel and its analytic identities are provided by
`Analysis.Fourier.PolarRadialKernels.Core`. This physical adapter relates polar
momenta to Cartesian Fourier phases and defines the finite-cutoff transform
with the continuum momentum measure `d²p / (2πℏ)²`.
-/

namespace QuantumTheory

open AngularHarmonics
namespace Transport

open PolarRadialKernels

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- Two-dimensional polar point `(ρ cos φ, ρ sin φ)`. -/
def polarPoint2D (radius angle : ℝ) : Fin 2 → ℝ :=
  ![radius * Real.cos angle, radius * Real.sin angle]

/-- The two-dimensional polar point is the generic finite-dimensional radial scaling specialized to
its usual unit direction `(cos φ, sin φ)`. -/
theorem polarPoint2D_eq_radialPoint (radius angle : ℝ) :
    polarPoint2D radius angle =
      radialPoint radius ![Real.cos angle, Real.sin angle] := by
  funext i
  fin_cases i <;> simp [polarPoint2D, radialPoint]

/-- Negating the radius negates a two-dimensional polar point at fixed angle. -/
theorem neg_polarPoint2D (radius angle : ℝ) :
    -(polarPoint2D radius angle) = polarPoint2D (-radius) angle := by
  rw [polarPoint2D_eq_radialPoint, polarPoint2D_eq_radialPoint,
    radialPoint_neg_radius]

/-- Fourier phase `exp(i p·r / ℏ)` for polar momentum `(p cos θ, p sin θ)` in two dimensions. -/
def physicalMomentumPolarFourierPhase
    (hbar p θ : ℝ) (r : Fin 2 → ℝ) : ℂ :=
  physicalMomentumFourierPhase hbar (polarPoint2D p θ) r

/-- The physical polar Fourier phase at a polar real-space point depends only on the angular
difference `θ - φ`. -/
theorem physicalMomentumPolarFourierPhase_polarPoint2D
    (hbar p θ radius angle : ℝ) :
    physicalMomentumPolarFourierPhase hbar p θ (polarPoint2D radius angle) =
      polarFourierRadialPhase (p * radius / hbar) (θ - angle) := by
  unfold physicalMomentumPolarFourierPhase physicalMomentumFourierPhase polarFourierRadialPhase
  simp only [polarPoint2D, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.cos_sub]
  apply congrArg Complex.exp
  push_cast
  ring_nf

/-- Finite-cutoff polar Fourier transform of a complex scalar momentum field with the physical
momentum measure `d²p / (2πℏ)²` included exactly once. -/
noncomputable def finiteCutoffPhysicalMomentumPolarFourier
    (hbar pMax : ℝ) (field : ℝ → ℝ → ℂ) (r : Fin 2 → ℝ) : ℂ :=
  (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax,
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * physicalMomentumPolarFourierPhase hbar p θ r) * field p θ

/-- Finite-cutoff polar Fourier reduction of canonical harmonic coefficients at an arbitrary polar
real-space point. -/
theorem finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
    (hbar pMax radius angle : ℝ) (coefficients : ℝ → AngularHarmonicCoefficients ℂ) :
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
        (fun p θ => (coefficients p).eval θ) (polarPoint2D radius angle) =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) *
            (polarFourierZerothAngularKernel (p * radius / hbar) * (coefficients p).constant +
              polarFourierFirstCosineAngularKernel (p * radius / hbar) *
                (((Real.cos angle : ℝ) : ℂ) * (coefficients p).firstCosine +
                  ((Real.sin angle : ℝ) : ℂ) * (coefficients p).firstSine) +
              polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                    (((Real.sin angle : ℝ) : ℂ) ^ 2)) * (coefficients p).secondCosine +
                  (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
                    (coefficients p).secondMixed)) := by
  unfold finiteCutoffPhysicalMomentumPolarFourier
  apply congrArg (((momentumMeasurePrefactor hbar : ℝ) : ℂ) * ·)
  apply intervalIntegral.integral_congr
  intro p _
  simp_rw [physicalMomentumPolarFourierPhase_polarPoint2D]
  exact integral_polarFourierRadialPhase_harmonicCoefficients_shifted (coefficients p)
    (p * radius / hbar) p angle


end

end Transport
end QuantumTheory
