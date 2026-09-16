import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornRealSpacePropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedTrace

set_option linter.style.header false

/-!
# Finite-cutoff real-space realization of Gaussian crossed Hall blocks

This module connects the crossed trace boundary to the massive-Dirac finite-cutoff finite-broadening
Born-Dyson data. The real-space Green field is consumed from the disorder-owned Born-Dyson
real-space propagator. The crossed current block applies the shared physical-momentum polar Fourier
transform entrywise to an advanced Green matrix, the diagonal crossed-sector in-plane Pauli vertex,
and a retarded Green matrix, in the order appearing in Ado et al., EPL 111, 37004 (2015), Eq. (14).

For the crossed sector, Eq. (14) uses only the diagonal factor `F = 1 / (1 - A)` of the dressed
current from Eq. (11). Accordingly the current block below resums only the longitudinal current-rung
coordinate and applies that common scalar to the requested Cartesian Pauli direction. The transverse
`F² B` part of the full local retarded-advanced dressed current, and the corresponding higher-order
feedback into the exact two-component fixed point, are deliberately not inserted into `J_r`.
The finite momentum cutoff and external broadening remain explicit; no cutoff removal,
zero-broadening limit, weak-disorder reduction, real-space `r` integration, Bessel-function
representation, or crossed conductivity value is claimed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

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

/-- Source-indexed finite-cutoff finite-`η` Gaussian-crossed real-space current block.

This is the regularized massive-Dirac realization of the `J_r` object entering the crossed trace
kernel. Its Fourier integrand is `Gᴬ (F σ_source) Gᴿ`, with `F` supplied by the diagonal ladder
resummation above. The transverse component of the full local dressed vertex is intentionally absent,
matching the leading crossed-sector reduction used in Ado et al. Eq. (14). -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) : Matrix2 :=
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let vertex : Matrix2 := factor • directionPauli source
  fun i j =>
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
      (fun p θ =>
        (finiteCutoffContinuumBornDysonGreenMatrix
            .advanced v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax *
          vertex *
          finiteCutoffContinuumBornDysonGreenMatrix
            .retarded v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax) i j)
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
      finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock
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
