import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaZeroTemperature
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSpectral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinBands
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.Tactic

set_option linter.style.header false

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- A retarded scalar projector-resolvent coefficient vanishes as the real probe energy tends to
`-∞` at fixed broadening. -/
theorem tendsto_retarded_projectorResolventCoefficient_atBot_zero
    (band : Band) (v m px py broadening : ℝ) :
    Tendsto
      (fun probeEnergy : ℝ =>
        projectorResolventCoefficient
          (retardedSpectralParameter probeEnergy broadening) band v m px py)
      atBot (nhds 0) := by
  have hreal :
      Tendsto (fun probeEnergy : ℝ => (probeEnergy : ℂ)) atBot
        (Bornology.cobounded ℂ) :=
    RCLike.tendsto_ofReal_atBot_cobounded ℂ
  let c : ℂ := (broadening : ℂ) * Complex.I - ((bandEnergy band v m px py : ℝ) : ℂ)
  have hden :
      Tendsto (fun probeEnergy : ℝ => (probeEnergy : ℂ) + c) atBot
        (Bornology.cobounded ℂ) :=
    (tendsto_add_const_cobounded c).comp hreal
  have hinv :
      Tendsto (fun probeEnergy : ℝ => ((probeEnergy : ℂ) + c)⁻¹) atBot (nhds 0) :=
    Filter.tendsto_inv₀_cobounded.comp hden
  simpa [projectorResolventCoefficient, retardedSpectralParameter, c, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm] using hinv

/-- An advanced scalar projector-resolvent coefficient has the same lower-energy limit. -/
theorem tendsto_advanced_projectorResolventCoefficient_atBot_zero
    (band : Band) (v m px py broadening : ℝ) :
    Tendsto
      (fun probeEnergy : ℝ =>
        projectorResolventCoefficient
          (advancedSpectralParameter probeEnergy broadening) band v m px py)
      atBot (nhds 0) := by
  have hreal :
      Tendsto (fun probeEnergy : ℝ => (probeEnergy : ℂ)) atBot
        (Bornology.cobounded ℂ) :=
    RCLike.tendsto_ofReal_atBot_cobounded ℂ
  let c : ℂ := -((broadening : ℂ) * Complex.I) - ((bandEnergy band v m px py : ℝ) : ℂ)
  have hden :
      Tendsto (fun probeEnergy : ℝ => (probeEnergy : ℂ) + c) atBot
        (Bornology.cobounded ℂ) :=
    (tendsto_add_const_cobounded c).comp hreal
  have hinv :
      Tendsto (fun probeEnergy : ℝ => ((probeEnergy : ℂ) + c)⁻¹) atBot (nhds 0) :=
    Filter.tendsto_inv₀_cobounded.comp hden
  simpa [projectorResolventCoefficient, advancedSpectralParameter, c, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm] using hinv

/-- At fixed positive broadening, the massive-Dirac regularized Středa surface primitive vanishes
at the lower-energy boundary. -/
theorem tendsto_regularizedStredaSurfacePrimitiveTrace_massiveDirac_atBot_zero
    (e v m px py broadening : ℝ) (hE : energy v m px py ≠ 0)
    (hbroadening : 0 < broadening) :
    Tendsto
      (fun probeEnergy : ℝ =>
        regularizedStredaSurfacePrimitiveTrace
          (hamiltonianOperator v m px py)
          (currentXOperator e v) (currentYOperator e v)
          probeEnergy broadening)
      atBot (nhds 0) := by
  have hretLower := tendsto_retarded_projectorResolventCoefficient_atBot_zero
    .lower v m px py broadening
  have hretUpper := tendsto_retarded_projectorResolventCoefficient_atBot_zero
    .upper v m px py broadening
  have hadvLower := tendsto_advanced_projectorResolventCoefficient_atBot_zero
    .lower v m px py broadening
  have hadvUpper := tendsto_advanced_projectorResolventCoefficient_atBot_zero
    .upper v m px py broadening
  have hretProj :
      Tendsto
        (fun probeEnergy : ℝ =>
          projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py)
        atBot (nhds 0) := by
    simpa only [projectorResolvent_eq_coefficients, zero_smul, zero_add] using
      (hretLower.smul_const (bandProjectorOperator .lower v m px py)).add
        (hretUpper.smul_const (bandProjectorOperator .upper v m px py))
  have hadvProj :
      Tendsto
        (fun probeEnergy : ℝ =>
          projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py)
        atBot (nhds 0) := by
    simpa only [projectorResolvent_eq_coefficients, zero_smul, zero_add] using
      (hadvLower.smul_const (bandProjectorOperator .lower v m px py)).add
        (hadvUpper.smul_const (bandProjectorOperator .upper v m px py))
  have hret :
      Tendsto
        (fun probeEnergy : ℝ =>
          retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening)
        atBot (nhds 0) := by
    apply hretProj.congr'
    filter_upwards with probeEnergy
    exact (retardedResolvent_eq_projectorResolvent
      v m px py probeEnergy broadening hE hbroadening).symm
  have hadv :
      Tendsto
        (fun probeEnergy : ℝ =>
          advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening)
        atBot (nhds 0) := by
    apply hadvProj.congr'
    filter_upwards with probeEnergy
    exact (advancedResolvent_eq_projectorResolvent
      v m px py probeEnergy broadening hE hbroadening).symm
  have hcurrentX :
      Tendsto
        (fun _ : ℝ => currentXOperator e v)
        atBot (nhds (currentXOperator e v)) :=
    tendsto_const_nhds
  have hcurrentY :
      Tendsto
        (fun _ : ℝ => currentYOperator e v)
        atBot (nhds (currentYOperator e v)) :=
    tendsto_const_nhds
  have hleftRet := ((hcurrentX.mul hret).mul hcurrentY)
  have hleftAdv := ((hcurrentY.mul hadv).mul hcurrentX)
  have hleft := hleftRet.sub hleftAdv
  have hdiff := hret.sub hadv
  have hfactor := hleft.mul hdiff
  have hscalar :
      Tendsto (fun _ : ℝ => (-(1 / 2 : ℂ))) atBot (nhds (-(1 / 2 : ℂ))) :=
    tendsto_const_nhds
  have hscaled := hscalar.smul hfactor
  have hoperator :
      Tendsto
        (fun probeEnergy : ℝ =>
          regularizedStredaSurfacePrimitiveOperator
            (hamiltonianOperator v m px py)
            (currentXOperator e v) (currentYOperator e v)
            probeEnergy broadening)
        atBot (nhds 0) := by
    simpa only [regularizedStredaSurfacePrimitiveOperator, smrckaStredaSurfaceFactor,
      retardedAdvancedResolventDifference, mul_zero, zero_mul, sub_self, smul_zero] using hscaled
  have htrace :=
    (finiteDimensionalOperatorTrace (H := DiracHilbert)).continuous.continuousAt.tendsto.comp
      hoperator
  simpa only [regularizedStredaSurfacePrimitiveTrace, Function.comp_def, map_zero] using htrace

/-- Therefore the finite-window zero-temperature Fermi-surface term tends to the single Fermi-edge
primitive as the lower energy is sent to `-∞`. -/
theorem tendsto_massiveDiracZeroTemperatureStredaFermiSurface_atBot
    (e v m px py broadening fermiEnergy : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    Tendsto
      (fun lowerEnergy : ℝ =>
        massiveDiracZeroTemperatureStredaFermiSurface
          e v m px py broadening lowerEnergy fermiEnergy)
      atBot
      (nhds (regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (currentXOperator e v) (currentYOperator e v)
        fermiEnergy broadening)) := by
  have hlower := tendsto_regularizedStredaSurfacePrimitiveTrace_massiveDirac_atBot_zero
    e v m px py broadening hE hbroadening
  simpa [massiveDiracZeroTemperatureStredaFermiSurface] using
    (tendsto_const_nhds.sub hlower)

end

end AnomalousHall.MassiveDirac
