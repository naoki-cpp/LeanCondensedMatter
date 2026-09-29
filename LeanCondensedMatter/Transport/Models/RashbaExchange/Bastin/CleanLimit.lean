import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PairBerry

set_option linter.style.header false

/-!
# Pointwise clean Bastin limit of the Rashba-exchange model

This module names the local clean-limit response density extracted from the fixed-window interband
Bastin pair.  It deliberately stops before momentum integration or any interchange of the momentum
integral with the zero-broadening limit.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open Filter

/-- Pointwise real clean-limit density of one target-band interband Bastin pair. -/
def cleanInterbandBastinPairLimitDensity
    (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  -2 * Real.pi *
    (params.signedCharge ^ 2 * berryCurvature params band px py)

/-- The fixed-window zero-broadening theorem expressed through the named clean-limit density. -/
theorem tendsto_targetCenteredInterbandBastinPairIntegral_re_cleanLimitDensity
    (params : Parameters) (band : Band) (px py radius : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap params band px py|) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredInterbandBastinPairIntegral
          params band px py radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (cleanInterbandBastinPairLimitDensity params band px py)) := by
  simpa [cleanInterbandBastinPairLimitDensity] using
    tendsto_targetCenteredInterbandBastinPairIntegral_re_berryCurvature
      params band px py radius hE hradiusPos hradius

/-- Zero Rashba coupling makes the clean interband Bastin-pair density vanish. -/
@[simp] theorem cleanInterbandBastinPairLimitDensity_rashba_zero
    (params : Parameters) (band : Band) (px py : ℝ)
    (hAlpha : params.rashbaVelocity = 0) :
    cleanInterbandBastinPairLimitDensity params band px py = 0 := by
  simp [cleanInterbandBastinPairLimitDensity, hAlpha]

end

end QuantumTheory.Transport.Models.RashbaExchange
