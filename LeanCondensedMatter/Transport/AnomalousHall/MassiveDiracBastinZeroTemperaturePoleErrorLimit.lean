import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperaturePoleErrorBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening limit of the zero-temperature weighted spectator error

The previous quadratic estimate bounds the occupation-weighted regular-spectator error by a local
Lorentzian term plus a term linear in the broadening.  Joint continuity at the target pole makes the
local coefficient arbitrarily small; compactness gives one global coefficient on the fixed outer
window.  Hence the complete weighted error tends to zero as the broadening approaches zero from the
positive side.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- On a fixed positive target-centered window narrower than the interband gap, the
zero-temperature occupation-weighted regular spectator error vanishes as `η → 0⁺`. -/
theorem tendsto_targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral_zero
    (band : Band) (e v m px py fermiEnergy outerRadius : ℝ)
    (hE : energy v m px py ≠ 0)
    (houterPos : 0 < outerRadius)
    (houter : outerRadius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
          band e v m px py fermiEnergy outerRadius broadening)
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
  have hinnerLtDelta : innerRadius < δ := by
    dsimp [innerRadius]
    calc
      min (outerRadius / 2) (δ / 2) ≤ δ / 2 := min_le_right _ _
      _ < δ := by linarith
  let D : ℝ := (C / innerRadius ^ 2) * (2 * outerRadius)
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (div_nonneg hCnonneg (sq_nonneg innerRadius))
      (mul_nonneg (by norm_num) houterPos.le)
  let etaLinear : ℝ := ε / (4 * (D + 1))
  have hDOnePos : 0 < D + 1 := by linarith
  have hetaLinearPos : 0 < etaLinear := by
    dsimp [etaLinear]
    positivity
  let etaRadius : ℝ := min δ (min 1 etaLinear)
  have hetaRadiusPos : 0 < etaRadius := by
    dsimp [etaRadius]
    exact lt_min_iff.mpr ⟨hδ, lt_min_iff.mpr ⟨zero_lt_one, hetaLinearPos⟩⟩
  have hwithin_le : nhdsWithin 0 (Set.Ioi 0) ≤ nhds (0 : ℝ) := inf_le_left
  have hetaSmall : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      broadening < etaRadius :=
    hwithin_le (Iio_mem_nhds hetaRadiusPos)
  have hetaPos : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < broadening := by
    change Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0)
    exact self_mem_nhdsWithin
  filter_upwards [hetaPos, hetaSmall] with broadening hbroadening hsmall
  have hbroadeningLtDelta : broadening < δ :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  have hbroadeningLtOne : broadening < 1 := by
    have : etaRadius ≤ 1 := by
      dsimp [etaRadius]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    exact lt_of_lt_of_le hsmall this
  have hbroadeningLtLinear : broadening < etaLinear := by
    have : etaRadius ≤ etaLinear := by
      dsimp [etaRadius]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    exact lt_of_lt_of_le hsmall this
  have hlocalAt : ∀ offset : ℝ, |offset| ≤ innerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ tolerance := by
    intro offset hoffset
    have hoffsetLtDelta : |offset| < δ := lt_of_le_of_lt hoffset hinnerLtDelta
    have hbroadeningAbsLtDelta : |broadening| < δ := by
      simpa [abs_of_pos hbroadening] using hbroadeningLtDelta
    have h := hlocal offset broadening hoffsetLtDelta hbroadeningAbsLtDelta
    simpa [targetCenteredInterbandSpectatorCurrentError] using h.le
  have hglobalAt : ∀ offset : ℝ, |offset| ≤ outerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ C := by
    intro offset hoffset
    apply hC (offset, broadening)
    refine ⟨abs_le.mp hoffset, ?_⟩
    exact ⟨hbroadening.le, hbroadeningLtOne.le⟩
  have hbound :=
    norm_targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral_le_pi_add_linear
      band e v m px py fermiEnergy innerRadius outerRadius broadening tolerance C
      hinnerPos houterPos.le htolerancePos.le hCnonneg hbroadening hlocalAt hglobalAt
  have hlocalTermLt : tolerance * Real.pi < ε / 4 := by
    have hpiLt : Real.pi < Real.pi + 1 := by linarith
    calc
      tolerance * Real.pi < tolerance * (Real.pi + 1) :=
        mul_lt_mul_of_pos_left hpiLt htolerancePos
      _ = ε / 4 := by
        dsimp [tolerance]
        field_simp [ne_of_gt hpiOnePos]
  have hlinearLt : D * broadening < ε / 4 := by
    calc
      D * broadening ≤ (D + 1) * broadening := by
        exact mul_le_mul_of_nonneg_right (by linarith) hbroadening.le
      _ < (D + 1) * etaLinear :=
        mul_lt_mul_of_pos_left hbroadeningLtLinear hDOnePos
      _ = ε / 4 := by
        dsimp [etaLinear]
        field_simp [ne_of_gt hDOnePos]
  have hbound' :
      ‖targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
          band e v m px py fermiEnergy outerRadius broadening‖ ≤
        tolerance * Real.pi + D * broadening := by
    simpa [D, mul_assoc] using hbound
  have hnormLt :
      ‖targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
          band e v m px py fermiEnergy outerRadius broadening‖ < ε := by
    calc
      _ ≤ tolerance * Real.pi + D * broadening := hbound'
      _ < ε / 4 + ε / 4 := add_lt_add hlocalTermLt hlinearLt
      _ < ε := by linarith
  simpa [dist_eq_norm] using hnormLt

end

end AnomalousHall.MassiveDirac
