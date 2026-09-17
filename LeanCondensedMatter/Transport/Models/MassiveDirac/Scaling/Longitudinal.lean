import LeanCondensedMatter.Transport.Models.MassiveDirac.Scaling.Domain
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.BornRelaxationTime
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Born-RTA longitudinal benchmark for the AHE scaling domain

The microscopic scalar-disorder transport lifetime is fed into the existing zero-temperature RTA
benchmark.  This exposes the Drude `1/W` law and its finite disorder-scaled coefficient in the
same parameter package used by the later Hall and normalized-pair constructions.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- The zero-temperature Born-RTA longitudinal conductivity at a scaling-domain point. -/
def AheScalingParameters.bornRtaLongitudinalConductivity
    (params : AheScalingParameters) : ℝ :=
  zeroTemperatureRelaxationTimeLongitudinalConductivity
    params.e params.hbar params.v params.m params.fermiEnergy
    (continuumBornUpperBandPositiveTransportLifetime
      params.v params.m params.fermiEnergy params.disorderStrength params.hbar
      params.velocity_ne_zero params.hbar_pos params.disorder_pos params.metallic)

/-- The finite coefficient left after multiplying the Born-RTA conductivity by `W`. -/
def AheScalingParameters.bornRtaLongitudinalCoefficient
    (params : AheScalingParameters) : ℝ :=
  params.e ^ 2 * params.hbar * params.v ^ 2 *
      (params.fermiEnergy ^ 2 - params.m ^ 2) /
    (Real.pi * (params.fermiEnergy ^ 2 + 3 * params.m ^ 2))

/-- The microscopic Born-RTA conductivity has the explicit `1/W` closed form. -/
theorem AheScalingParameters.bornRtaLongitudinalConductivity_eq
    (params : AheScalingParameters) :
    params.bornRtaLongitudinalConductivity =
      params.e ^ 2 * params.hbar * params.v ^ 2 *
          (params.fermiEnergy ^ 2 - params.m ^ 2) /
        (Real.pi * params.disorderStrength *
          (params.fermiEnergy ^ 2 + 3 * params.m ^ 2)) := by
  exact zeroTemperatureRelaxationTimeLongitudinalConductivity_bornTransportLifetime_eq
    params.e params.hbar params.v params.m params.fermiEnergy params.disorderStrength
    params.velocity_ne_zero params.hbar_pos params.disorder_pos params.metallic

/-- Multiplication by disorder strength removes the Drude divergence and gives the finite
coefficient used in the weak-disorder scaling limit. -/
theorem AheScalingParameters.disorderStrength_mul_bornRtaLongitudinalConductivity_eq
    (params : AheScalingParameters) :
    params.disorderStrength * params.bornRtaLongitudinalConductivity =
      params.bornRtaLongitudinalCoefficient := by
  simpa [AheScalingParameters.bornRtaLongitudinalCoefficient] using
    disorderStrength_mul_zeroTemperatureRelaxationTimeLongitudinalConductivity_bornTransportLifetime_eq
      params.e params.hbar params.v params.m params.fermiEnergy params.disorderStrength
      params.velocity_ne_zero params.hbar_pos params.disorder_pos params.metallic

/-- The totalized closed form has a well-defined positive-disorder scaling limit. -/
def bornRtaLongitudinalConductivityClosedForm
    (e hbar v m fermiEnergy disorderStrength : ℝ) : ℝ :=
  e ^ 2 * hbar * v ^ 2 * (fermiEnergy ^ 2 - m ^ 2) /
    (Real.pi * disorderStrength * (fermiEnergy ^ 2 + 3 * m ^ 2))

theorem tendsto_disorderStrength_mul_bornRtaLongitudinalConductivityClosedForm
    (e hbar v m fermiEnergy : ℝ)
    (hmetal : |m| < fermiEnergy) :
    Tendsto
      (fun disorderStrength : ℝ =>
        disorderStrength *
          bornRtaLongitudinalConductivityClosedForm
            e hbar v m fermiEnergy disorderStrength)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (e ^ 2 * hbar * v ^ 2 * (fermiEnergy ^ 2 - m ^ 2) /
          (Real.pi * (fermiEnergy ^ 2 + 3 * m ^ 2)))) := by
  have hfermiPos : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_ne_zero hfermiNe
  have hden : fermiEnergy ^ 2 + 3 * m ^ 2 ≠ 0 :=
    ne_of_gt
      (add_pos_of_pos_of_nonneg hfermiSq
        (mul_nonneg (by norm_num) (sq_nonneg m)))
  have hconst : Tendsto
      (fun _ : ℝ =>
        e ^ 2 * hbar * v ^ 2 * (fermiEnergy ^ 2 - m ^ 2) /
          (Real.pi * (fermiEnergy ^ 2 + 3 * m ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (e ^ 2 * hbar * v ^ 2 * (fermiEnergy ^ 2 - m ^ 2) /
          (Real.pi * (fermiEnergy ^ 2 + 3 * m ^ 2)))) :=
    tendsto_const_nhds
  refine hconst.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with disorderStrength hdisorder
  unfold bornRtaLongitudinalConductivityClosedForm
  field_simp [ne_of_gt hdisorder, hden, Real.pi_ne_zero]

end

end QuantumTheory.Transport.Models.MassiveDirac
