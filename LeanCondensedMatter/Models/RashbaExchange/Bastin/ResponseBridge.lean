import LeanCondensedMatter.Models.RashbaExchange.Bastin.Bands
import LeanCondensedMatter.Models.RashbaExchange.Response

set_option linter.style.header false

/-!
# Rashba-exchange Bastin finite-window response bridge

Connect the direction-indexed pointwise Bastin band-pair identities to the
existing clean finite-energy-window response and its antisymmetric Hall
projection. This module depends on both the algebraic `Bastin/Bands` layer
and the physical `Response` layer; neither layer imports this bridge.

The equalities rewrite the integrands on fixed energy windows. They do not
assert integrability of separately isolated terms, interchange limits with
integration, or identify the value at zero broadening with a clean limit.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

open QuantumTheory.Transport
open ContinuousLinearMap

/-- The physical clean ordered Bastin energy integral equals the weighted
band-pair integral on any finite energy window. No limit interchange occurs. -/
theorem cleanBastinPointResponse_eq_integral_band_sum
    (params : Parameters) (μ ν : Fin 2)
    (px py lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hbroadening : params.broadening ≠ 0) :
    cleanBastinPointResponse params μ ν px py lowerEnergy upperEnergy occupation =
      ∫ probeEnergy in lowerEnergy..upperEnergy,
        occupation probeEnergy *
          (∑ source : Band, ∑ target : Band,
            bastinBandPairContribution params μ ν source target
              px py probeEnergy params.broadening) := by
  unfold cleanBastinPointResponse regularizedTracedBastinEnergyIntegral
  apply intervalIntegral.integral_congr
  intro probeEnergy _
  dsimp only
  rw [regularizedBastinTraceIntegrand_eq_band_sum
    params μ ν px py probeEnergy params.broadening hE hbroadening]

/-- The weighted finite-window Bastin energy response retains diagonal and
interband contributions separately, for any ordered current directions. -/
theorem cleanBastinPointResponse_eq_integral_diagonal_add_interband
    (params : Parameters) (μ ν : Fin 2)
    (px py lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hbroadening : params.broadening ≠ 0) :
    cleanBastinPointResponse params μ ν px py lowerEnergy upperEnergy occupation =
      ∫ probeEnergy in lowerEnergy..upperEnergy,
        occupation probeEnergy *
          ((∑ band : Band,
            bastinBandPairContribution params μ ν band band
              px py probeEnergy params.broadening) +
           (∑ band : Band,
            bastinBandPairContribution params μ ν band (oppositeBand band)
              px py probeEnergy params.broadening)) := by
  unfold cleanBastinPointResponse regularizedTracedBastinEnergyIntegral
  apply intervalIntegral.integral_congr
  intro probeEnergy _
  dsimp only
  rw [regularizedBastinTraceIntegrand_eq_band_sum
    params μ ν px py probeEnergy params.broadening hE hbroadening]
  simp only [sum_band, oppositeBand_lower, oppositeBand_upper]
  ring

/-- The antisymmetric clean Bastin response is exactly the difference of
the two direction-ordered finite-window band-pair integrals. -/
theorem antisymmetricCleanBastinPointResponse_eq_integral_band_sum
    (params : Parameters) (μ ν : Fin 2)
    (px py lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hbroadening : params.broadening ≠ 0) :
    antisymmetricCleanBastinPointResponse params μ ν px py
        lowerEnergy upperEnergy occupation =
      (1 / 2 : ℂ) *
        ((∫ probeEnergy in lowerEnergy..upperEnergy,
            occupation probeEnergy *
              (∑ source : Band, ∑ target : Band,
                bastinBandPairContribution params μ ν source target
                  px py probeEnergy params.broadening)) -
         (∫ probeEnergy in lowerEnergy..upperEnergy,
            occupation probeEnergy *
              (∑ source : Band, ∑ target : Band,
                bastinBandPairContribution params ν μ source target
                  px py probeEnergy params.broadening))) := by
  unfold antisymmetricCleanBastinPointResponse
  rw [cleanBastinPointResponse_eq_integral_band_sum
      params μ ν px py lowerEnergy upperEnergy occupation hE hbroadening,
    cleanBastinPointResponse_eq_integral_band_sum
      params ν μ px py lowerEnergy upperEnergy occupation hE hbroadening]

end

end QuantumTheory.Models.RashbaExchange
