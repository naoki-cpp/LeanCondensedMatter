import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleErrorBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-window zero-broadening limit of the massive-Dirac Bastin pole error

The regular spectator/current factor differs from its target-pole value by a term that is small near
the pole and merely bounded away from it.  The preceding files converted those facts into a full
fixed-window estimate consisting of an inner Lorentzian mass and an outer Lorentzian tail mass.

This file closes that estimate: on every positive target-centered window strictly narrower than the
interband gap, the Lorentzian-weighted spectator error tends to zero as the broadening tends to zero
from the positive side.  The result remains pointwise in momentum; no momentum integration or
limit/integral interchange in momentum is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Every symmetric Lorentzian mass is strictly smaller than `π`. -/
theorem integral_lorentzianSpectralKernel_symmetric_lt_pi
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius,
      lorentzianSpectralKernel offset broadening) < Real.pi := by
  rw [integral_lorentzianSpectralKernel_symmetric]
  linarith [Real.arctan_lt_pi_div_two (radius / broadening)]

/-- On a fixed positive target-centered window narrower than the interband gap, the complete
Lorentzian-weighted regular spectator error vanishes in the positive zero-broadening limit. -/
theorem tendsto_targetCenteredInterbandSpectatorCurrentErrorIntegral_zero
    (band : Band) (e v m px py outerRadius : ℝ)
    (hE : energy v m px py ≠ 0)
    (houterPos : 0 < outerRadius)
    (houter : outerRadius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredInterbandSpectatorCurrentErrorIntegral
          band e v m px py outerRadius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  rcases exists_nonneg_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_le_on_rectangle
      band e v m px py outerRadius 1 houter with ⟨C, hCnonneg, hC⟩
  apply Metric.tendsto_nhds.2
  intro ε hε
  let tolerance : ℝ := ε / (4 * (Real.pi + 1))
  have hpiOnePos : 0 < Real.pi + 1 := by positivity
  have htolerancePos : 0 < tolerance := by
    dsimp [tolerance]
    positivity
  rcases exists_delta_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_lt_of_coordinates
      band e v m px py tolerance hE htolerancePos with ⟨δ, hδ, hlocal⟩
  let innerRadius : ℝ := min (outerRadius / 2) (δ / 2)
  have hinnerPos : 0 < innerRadius := by
    dsimp [innerRadius]
    exact lt_min_iff.mpr ⟨half_pos houterPos, half_pos hδ⟩
  have hinnerNonneg : 0 ≤ innerRadius := hinnerPos.le
  have hnested : innerRadius ≤ outerRadius := by
    dsimp [innerRadius]
    calc
      min (outerRadius / 2) (δ / 2) ≤ outerRadius / 2 := min_le_left _ _
      _ ≤ outerRadius := by linarith
  have hinnerLtDelta : innerRadius < δ := by
    dsimp [innerRadius]
    calc
      min (outerRadius / 2) (δ / 2) ≤ δ / 2 := min_le_right _ _
      _ < δ := by linarith
  let etaRadius : ℝ := min δ 1
  have hetaRadiusPos : 0 < etaRadius := by
    dsimp [etaRadius]
    exact lt_min_iff.mpr ⟨hδ, zero_lt_one⟩
  have hwithin_le : nhdsWithin 0 (Set.Ioi 0) ≤ nhds (0 : ℝ) := by
    exact inf_le_left
  have hetaSmall : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      broadening < etaRadius :=
    hwithin_le (Iio_mem_nhds hetaRadiusPos)
  have hetaPos : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < broadening := by
    change Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0)
    exact self_mem_nhdsWithin
  let tailTolerance : ℝ := ε / (4 * (C + 1))
  have hCOnePos : 0 < C + 1 := by linarith
  have htailTolerancePos : 0 < tailTolerance := by
    dsimp [tailTolerance]
    exact div_pos hε (mul_pos (by norm_num) hCOnePos)
  have htail := tendsto_lorentzianSpectralTailMass_zero
    innerRadius outerRadius hinnerPos hnested
  have htailClose : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      dist (lorentzianSpectralTailMass innerRadius outerRadius broadening) 0 <
        tailTolerance :=
    (Metric.tendsto_nhds.1 htail) tailTolerance htailTolerancePos
  filter_upwards [hetaPos, hetaSmall, htailClose] with broadening hbroadening hsmall htailCloseAt
  have hbroadeningLtDelta : broadening < δ := by
    exact lt_of_lt_of_le hsmall (min_le_left _ _)
  have hbroadeningLtOne : broadening < 1 := by
    exact lt_of_lt_of_le hsmall (min_le_right _ _)
  have hlocalAt : ∀ offset : ℝ, |offset| ≤ innerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ tolerance := by
    intro offset hoffset
    have hoffsetLtDelta : |offset| < δ := lt_of_le_of_lt hoffset hinnerLtDelta
    have hbroadeningAbsLtDelta : |broadening| < δ := by
      simpa [abs_of_pos hbroadening] using hbroadeningLtDelta
    have h := hlocal offset broadening hoffsetLtDelta hbroadeningAbsLtDelta
    simpa [targetCenteredInterbandSpectatorCurrentError] using h.le
  have hannulusAt : ∀ offset : ℝ,
      innerRadius ≤ |offset| → |offset| ≤ outerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ C := by
    intro offset _ hoffsetOuter
    apply hC (offset, broadening)
    refine ⟨abs_le.mp hoffsetOuter, ?_⟩
    exact ⟨hbroadening.le, hbroadeningLtOne.le⟩
  have hbound :=
    norm_targetCenteredInterbandSpectatorCurrentErrorIntegral_le_inner_add_tail
      band e v m px py innerRadius outerRadius broadening tolerance C
      hinnerNonneg hnested houter hbroadening hlocalAt hannulusAt
  have hmassLtPi :=
    integral_lorentzianSpectralKernel_symmetric_lt_pi innerRadius broadening
  have hinnerTermLt :
      tolerance *
          (∫ offset in -innerRadius..innerRadius,
            lorentzianSpectralKernel offset broadening) < ε / 4 := by
    have hmassLt :
        (∫ offset in -innerRadius..innerRadius,
          lorentzianSpectralKernel offset broadening) < Real.pi + 1 := by
      linarith
    calc
      tolerance *
          (∫ offset in -innerRadius..innerRadius,
            lorentzianSpectralKernel offset broadening) <
        tolerance * (Real.pi + 1) :=
          mul_lt_mul_of_pos_left hmassLt htolerancePos
      _ = ε / 4 := by
        dsimp [tolerance]
        field_simp [ne_of_gt hpiOnePos]
  have htailLt :
      lorentzianSpectralTailMass innerRadius outerRadius broadening < tailTolerance := by
    have habs :
        |lorentzianSpectralTailMass innerRadius outerRadius broadening| < tailTolerance := by
      simpa [Real.dist_eq] using htailCloseAt
    exact lt_of_le_of_lt (le_abs_self _) habs
  have houterTermLe :
      C * lorentzianSpectralTailMass innerRadius outerRadius broadening ≤ ε / 4 := by
    calc
      C * lorentzianSpectralTailMass innerRadius outerRadius broadening ≤
          C * tailTolerance :=
        mul_le_mul_of_nonneg_left (le_of_lt htailLt) hCnonneg
      _ ≤ (C + 1) * tailTolerance :=
        mul_le_mul_of_nonneg_right (by linarith) htailTolerancePos.le
      _ = ε / 4 := by
        dsimp [tailTolerance]
        field_simp [ne_of_gt hCOnePos]
  have hnormLt :
      ‖targetCenteredInterbandSpectatorCurrentErrorIntegral
          band e v m px py outerRadius broadening‖ < ε := by
    calc
      ‖targetCenteredInterbandSpectatorCurrentErrorIntegral
          band e v m px py outerRadius broadening‖ ≤
        tolerance *
            (∫ offset in -innerRadius..innerRadius,
              lorentzianSpectralKernel offset broadening) +
          C * lorentzianSpectralTailMass innerRadius outerRadius broadening := hbound
      _ < ε / 4 + ε / 4 := add_lt_add_of_lt_of_le hinnerTermLt houterTermLe
      _ < ε := by linarith
  simpa [dist_eq_norm] using hnormLt

end

end AnomalousHall.MassiveDirac
