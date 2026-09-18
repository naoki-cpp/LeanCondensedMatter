import LeanCondensedMatter.Transport.Models.MassiveDirac.Scaling.Domain
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.NonCrossing

set_option linter.style.header false

/-!
# Normalized longitudinal/Hall pair for massive-Dirac AHE scaling

This module packages the physically normalized massive-Dirac conductivity tensor into the
dimensionless pair used by the AHE scaling program. The tensor layer remains the unique owner of the
Bastin/Středa trace and continuum-measure normalization. This layer only multiplies the completed
physical conductivity by `h / e²`.

The longitudinal coordinate is the ordered `xx` component. The transverse coordinate is the
antisymmetric Hall projection `hallComponent 0 1`; rotational closure proves that it equals the
ordered `xy` component for the finite-broadening tensor. Broadening and weak-disorder limits remain
sequential and the finite-broadening regulator is kept distinct from the scaling coordinate
`AheScalingParameters.gamma`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Complex-valued conductivity normalization used before zero-broadening or other reality
statements have been proved for a physical conductivity component. -/
def AheScalingParameters.normalizedComplexConductivity
    (params : AheScalingParameters) (sigma : ℂ) : ℂ :=
  (((planckFromReduced params.hbar / params.e ^ 2 : ℝ) : ℂ)) * sigma

/-- Dimensionless longitudinal/Hall conductivity coordinates. Finite-broadening values remain
complex until a separate reality theorem is available. -/
structure AheScalingPair where
  /-- Dimensionless longitudinal conductivity, `sxx = (h/e²) σxx`. -/
  sxx : ℂ
  /-- Dimensionless Hall conductivity, `sxy = (h/e²) σHall`. -/
  sxy : ℂ

/-- Extract the normalized `xx` and Hall coordinates from a completed physical conductivity
tensor. The input tensor is already physically normalized; this map does not attach a second
Bastin/Středa prefactor. -/
def AheScalingParameters.normalizedPairOfTensor
    (params : AheScalingParameters) (conductivity : ConductivityTensor (Fin 2)) :
    AheScalingPair where
  sxx := params.normalizedComplexConductivity (conductivity.longitudinal 0)
  sxy := params.normalizedComplexConductivity (conductivity.hallComponent 0 1)

/-- Finite-cutoff, finite-broadening normalized conductivity pair at the disorder strength stored in
`params`. The explicit `broadening` argument is the spectral regulator and is not identified with
`params.gamma`. -/
def AheScalingParameters.finiteBroadeningPair
    (params : AheScalingParameters) (broadening : ℝ) : AheScalingPair :=
  params.normalizedPairOfTensor
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
      params.e params.v params.m params.fermiEnergy broadening params.disorderStrength
      params.hbar params.pMax)

/-- Zero-broadening normalized pair as a function of disorder strength. This totalized family is the
boundary used for the subsequent one-sided weak-disorder limit. -/
def AheScalingParameters.zeroBroadeningPairAtDisorder
    (params : AheScalingParameters) (disorderStrength : ℝ) : AheScalingPair :=
  params.normalizedPairOfTensor
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
      params.e params.v params.m params.fermiEnergy disorderStrength params.hbar params.pMax)

/-- Zero-broadening normalized pair at the positive disorder strength stored in `params`. -/
def AheScalingParameters.zeroBroadeningPair
    (params : AheScalingParameters) : AheScalingPair :=
  params.zeroBroadeningPairAtDisorder params.disorderStrength

/-- The finite-broadening longitudinal scaling coordinate is the normalized ordered `xx`
conductivity component. -/
@[simp]
theorem AheScalingParameters.finiteBroadeningPair_sxx
    (params : AheScalingParameters) (broadening : ℝ) :
    (params.finiteBroadeningPair broadening).sxx =
      params.normalizedComplexConductivity
        ((finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
          params.e params.v params.m params.fermiEnergy broadening params.disorderStrength
          params.hbar params.pMax).component 0 0) :=
  rfl

/-- Rotational closure identifies the finite-broadening Hall projection with ordered `xy`, so the
scaling coordinate has an explicit component orientation. -/
@[simp]
theorem AheScalingParameters.finiteBroadeningPair_sxy
    (params : AheScalingParameters) (broadening : ℝ) :
    (params.finiteBroadeningPair broadening).sxy =
      params.normalizedComplexConductivity
        ((finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
          params.e params.v params.m params.fermiEnergy broadening params.disorderStrength
          params.hbar params.pMax).component 0 1) := by
  unfold AheScalingParameters.finiteBroadeningPair
    AheScalingParameters.normalizedPairOfTensor
    AheScalingParameters.normalizedComplexConductivity
    ConductivityTensor.longitudinal ConductivityTensor.hallComponent
  rw [
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_yx_eq_neg_xy]
  ring

/-- The zero-broadening longitudinal scaling coordinate at arbitrary disorder strength is the
normalized ordered `xx` boundary component. -/
@[simp]
theorem AheScalingParameters.zeroBroadeningPairAtDisorder_sxx
    (params : AheScalingParameters) (disorderStrength : ℝ) :
    (params.zeroBroadeningPairAtDisorder disorderStrength).sxx =
      params.normalizedComplexConductivity
        ((finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
          params.e params.v params.m params.fermiEnergy disorderStrength params.hbar
          params.pMax).component 0 0) :=
  rfl

/-- The zero-broadening Hall scaling coordinate at arbitrary disorder strength is the normalized
ordered `xy` boundary, using the proved Hall projection identity. -/
@[simp]
theorem AheScalingParameters.zeroBroadeningPairAtDisorder_sxy
    (params : AheScalingParameters) (disorderStrength : ℝ) :
    (params.zeroBroadeningPairAtDisorder disorderStrength).sxy =
      params.normalizedComplexConductivity
        (finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
          params.e params.v params.m params.fermiEnergy disorderStrength params.hbar
          params.pMax) := by
  simp [AheScalingParameters.zeroBroadeningPairAtDisorder,
    AheScalingParameters.normalizedPairOfTensor]

/-- At the stored disorder strength, the zero-broadening longitudinal scaling coordinate is the
normalized ordered `xx` boundary component. -/
@[simp]
theorem AheScalingParameters.zeroBroadeningPair_sxx
    (params : AheScalingParameters) :
    params.zeroBroadeningPair.sxx =
      params.normalizedComplexConductivity
        ((finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
          params.e params.v params.m params.fermiEnergy params.disorderStrength params.hbar
          params.pMax).component 0 0) := by
  simp [AheScalingParameters.zeroBroadeningPair]

/-- At the stored disorder strength, the zero-broadening Hall scaling coordinate is the normalized
ordered `xy` boundary. -/
@[simp]
theorem AheScalingParameters.zeroBroadeningPair_sxy
    (params : AheScalingParameters) :
    params.zeroBroadeningPair.sxy =
      params.normalizedComplexConductivity
        (finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
          params.e params.v params.m params.fermiEnergy params.disorderStrength params.hbar
          params.pMax) := by
  simp [AheScalingParameters.zeroBroadeningPair]

/-- At fixed positive disorder, the normalized longitudinal coordinate converges componentwise to
the zero-broadening boundary. -/
theorem AheScalingParameters.tendsto_finiteBroadeningPair_sxx_broadening_zero
    (params : AheScalingParameters)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      params.v params.m params.fermiEnergy params.disorderStrength params.hbar params.pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      params.v params.m params.fermiEnergy params.disorderStrength params.hbar params.pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ => (params.finiteBroadeningPair broadening).sxx)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds params.zeroBroadeningPair.sxx) := by
  have h :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_broadening_zero
      (0 : Fin 2) (0 : Fin 2)
      params.e params.v params.m params.fermiEnergy params.disorderStrength params.hbar params.pMax
      params.cutoff_nonneg params.velocity_ne_zero (ne_of_gt params.hbar_pos)
      params.disorder_pos params.metallic params.cutoff_shell hrenorm hdet
  have hnormalized :=
    h.const_mul
      (((planckFromReduced params.hbar / params.e ^ 2 : ℝ) : ℂ))
  simpa [AheScalingParameters.normalizedComplexConductivity] using hnormalized

/-- At fixed positive disorder, the normalized Hall coordinate converges to the Hall projection of
the zero-broadening tensor boundary. -/
theorem AheScalingParameters.tendsto_finiteBroadeningPair_sxy_broadening_zero
    (params : AheScalingParameters)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      params.v params.m params.fermiEnergy params.disorderStrength params.hbar params.pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      params.v params.m params.fermiEnergy params.disorderStrength params.hbar params.pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ => (params.finiteBroadeningPair broadening).sxy)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds params.zeroBroadeningPair.sxy) := by
  have h :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_broadening_zero
      (0 : Fin 2) (1 : Fin 2)
      params.e params.v params.m params.fermiEnergy params.disorderStrength params.hbar params.pMax
      params.cutoff_nonneg params.velocity_ne_zero (ne_of_gt params.hbar_pos)
      params.disorder_pos params.metallic params.cutoff_shell hrenorm hdet
  have hnormalized :=
    h.const_mul
      (((planckFromReduced params.hbar / params.e ^ 2 : ℝ) : ℂ))
  simpa [AheScalingParameters.normalizedComplexConductivity,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary]
    using hnormalized

/-- The normalized Hall coordinate inherits the existing sequential zero-broadening then
weak-disorder non-crossing limit. No finite-broadening skew contribution is introduced here. -/
theorem AheScalingParameters.tendsto_zeroBroadeningPairAtDisorder_sxy_disorder_zero
    (params : AheScalingParameters) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (params.zeroBroadeningPairAtDisorder disorderStrength).sxy)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (params.normalizedComplexConductivity
          (((nonCrossingHallConductivity
            params.e params.hbar params.m params.fermiEnergy : ℝ) : ℂ)))) := by
  have h :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_disorder_zero_eq_nonCrossing
      params.e params.v params.m params.fermiEnergy params.hbar params.pMax
      params.velocity_ne_zero params.hbar_pos params.metallic params.cutoff_shell
  have hnormalized :=
    h.const_mul
      (((planckFromReduced params.hbar / params.e ^ 2 : ℝ) : ℂ))
  simpa [AheScalingParameters.zeroBroadeningPairAtDisorder,
    AheScalingParameters.normalizedPairOfTensor,
    AheScalingParameters.normalizedComplexConductivity] using hnormalized

end

end QuantumTheory.Transport.Models.MassiveDirac
