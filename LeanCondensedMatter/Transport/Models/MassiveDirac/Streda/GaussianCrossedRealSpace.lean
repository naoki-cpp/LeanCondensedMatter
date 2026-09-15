import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Finite-cutoff real-space realization of Gaussian crossed Hall blocks

This module connects the model-independent crossed trace boundary to the massive-Dirac finite-cutoff
finite-broadening Born-Dyson data. The real-space Green field is the polar momentum Fourier transform
of the existing Born-Dyson Green matrix. The real-space current block is the corresponding transform
of an advanced Green matrix, the diagonal dressed in-plane Pauli vertex, and a retarded Green matrix,
in the order appearing in Ado et al., EPL 111, 37004 (2015), Eq. (14).

For the crossed sector, Eq. (14) uses only the diagonal factor `F = 1 / (1 - A)` of the dressed
current from Eq. (11). Accordingly the current block below resums only the longitudinal current-rung
coordinate and applies that common scalar to the requested Cartesian Pauli direction. The transverse
`F² B` part of the full local retarded-advanced dressed current, and the corresponding higher-order
feedback into the exact two-component fixed point, are deliberately not inserted into `J_r`.
The finite radial cutoff and external broadening remain explicit; no cutoff removal, zero-broadening
limit, weak-disorder reduction, real-space `r` integration, Bessel-function representation, or
crossed conductivity value is claimed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- Fourier phase `exp(i p·r / ℏ)` in polar momentum coordinates. -/
def gaussianCrossedFourierPhase
    (hbar p θ : ℝ) (r : Fin 2 → ℝ) : ℂ :=
  Complex.exp
    (Complex.I *
      (((p * (r 0 * Real.cos θ + r 1 * Real.sin θ) / hbar : ℝ) : ℂ)))

/-- Finite-cutoff polar Fourier transform of a matrix-valued momentum field, including the physical
momentum measure `d²p / (2πℏ)²`. Since `Matrix2` is finite, the transform is defined entrywise as a
complex interval integral; no additional normed-space structure on the matrix representation is
introduced. Kept private because the current consumer is the crossed massive-Dirac realization below
rather than a repository-wide Fourier API. -/
private noncomputable def finiteCutoffPolarFourierMatrix
    (hbar pMax : ℝ) (field : ℝ → ℝ → Matrix2) (r : Fin 2 → ℝ) : Matrix2 :=
  fun i j => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax,
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * gaussianCrossedFourierPhase hbar p θ r) * field p θ i j

/-- Finite-cutoff finite-`η` real-space Born-Dyson Green matrix. -/
noncomputable def finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) : Matrix2 :=
  finiteCutoffPolarFourierMatrix hbar pMax
    (fun p θ =>
      finiteCutoffContinuumBornDysonGreenMatrix
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax)
    r

/-- Diagonal dressed-current factor used by the Gaussian crossed sector.

This is the finite-`η` diagonal ladder resummation `(1 - A)⁻¹`, where `A` is the longitudinal
source-`x` current-rung coefficient. It is the regularized repository counterpart of the factor `F`
retained in Ado et al. Eq. (14), rather than the complete two-component dressed-current fixed point. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (1 - finiteCutoffContinuumBornDysonCurrentRungVector
    v m probeEnergy broadening disorderStrength hbar pMax 0)⁻¹

@[simp]
theorem finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening 0 hbar pMax = 1 := by
  simp [finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor,
    finiteCutoffContinuumBornDysonCurrentRungVector]

/-- Source-indexed finite-cutoff finite-`η` real-space current block.

This is the regularized massive-Dirac realization of the `J_r` object entering the crossed trace
kernel. Its Fourier integrand is `Gᴬ (F σ_source) Gᴿ`, with `F` supplied by the diagonal ladder
resummation above. The transverse component of the full local dressed vertex is intentionally absent,
matching the leading crossed-sector reduction used in Ado et al. Eq. (14). -/
noncomputable def finiteCutoffContinuumBornDysonRealSpaceCurrentBlock
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) : Matrix2 :=
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let vertex : Matrix2 := factor • directionPauli source
  finiteCutoffPolarFourierMatrix hbar pMax
    (fun p θ =>
      finiteCutoffContinuumBornDysonGreenMatrix
          .advanced v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax *
        vertex *
        finiteCutoffContinuumBornDysonGreenMatrix
          .retarded v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax)
    r

/-- Massive-Dirac finite-cutoff finite-`η` realization of the pointwise Gaussian crossed trace
kernel. The remaining real-space integral and conductivity normalization stay downstream. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) : ℂ :=
  gaussianCrossedTraceKernel diagram
    (finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
      .retarded v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
      .advanced v m probeEnergy broadening disorderStrength hbar pMax)
    (fun source =>
      finiteCutoffContinuumBornDysonRealSpaceCurrentBlock
        source v m probeEnergy broadening disorderStrength hbar pMax)
    r

/-- The model-specific finite-cutoff `Psi` trace kernel remains real by the same trace-level
Hermitian-conjugate construction as the abstract crossed boundary. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel_psi_im
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) :
    (finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
      .psi v m probeEnergy broadening disorderStrength hbar pMax r).im = 0 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
  exact gaussianCrossedTraceKernel_psi_im _ _ _ r

end

end QuantumTheory.Transport.Models.MassiveDirac
