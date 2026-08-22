import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleWindowBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Local error control for the massive-Dirac Bastin pole factor

The regular interband spectator/current factor is jointly continuous at the target pole.  For the
occupation-weighted energy integral we need that statement in an explicit epsilon-delta form: when
both the energy offset and broadening are sufficiently small, the regular factor is uniformly close
to its pole value.

This file exposes both the metric-ball statement and a coordinatewise version adapted to a
rectangular `(offset, broadening)` neighborhood.  The latter is the form consumed by the local
Lorentzian error estimate.  No energy integration or momentum integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Joint continuity at the target pole gives direct epsilon-delta norm control of the regular
spectator/current factor. -/
theorem exists_delta_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_lt
    (band : Band) (e v m px py ε : ℝ)
    (hE : energy v m px py ≠ 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p : ℝ × ℝ,
      dist p (0, 0) < δ →
        ‖targetCenteredInterbandSpectatorCurrentFactor band e v m px py p -
          targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0)‖ < ε := by
  have hcont :=
    continuousAt_targetCenteredInterbandSpectatorCurrentFactor_zero band e v m px py hE
  rw [Metric.continuousAt_iff] at hcont
  rcases hcont ε hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  have h := hclose hp
  simpa [dist_eq_norm] using h

/-- Coordinatewise version of the local pole estimate.  If both the energy offset and broadening
have absolute value below the same sufficiently small scale, the regular factor differs from its
pole value by less than the prescribed tolerance. -/
theorem exists_delta_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_lt_of_coordinates
    (band : Band) (e v m px py ε : ℝ)
    (hE : energy v m px py ≠ 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ offset broadening : ℝ,
      |offset| < δ → |broadening| < δ →
        ‖targetCenteredInterbandSpectatorCurrentFactor band e v m px py
            (offset, broadening) -
          targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0)‖ < ε := by
  rcases exists_delta_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_lt
      band e v m px py ε hE hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro offset broadening hoffset hbroadening
  apply hclose
  rw [Prod.dist_eq]
  simp only [Real.dist_eq, sub_zero]
  exact max_lt hoffset hbroadening

end

end AnomalousHall.MassiveDirac
