import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.SingleParticleRate
import LeanCondensedMatter.Transport.Analysis.RelaxationTime
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Typed Born single-particle lifetime of the metallic upper band

The model-specific disorder layer already derives the microscopic upper-band Born scattering rate
and its reciprocal scalar lifetime.  This file does not introduce a second rate or lifetime formula.
Instead it connects that existing result to the generic distinction between the spectral lifetime
`τ_q` and the transport lifetime `τ_tr`.

The upstream chain is

```text
Im Tr[P₊ Σᴿ] → -Γ_Born,
1 / τ_q = 2 Γ_Born / ℏ,
τ_q = (1 / τ_q)⁻¹.
```

Here the decay-width limit is exposed through the generic convention `Γ_q = -Im Σᴿ`, and the
existing positive model lifetime is packaged as `PositiveSingleParticleLifetime`.  No equality with
`PositiveTransportLifetime` is asserted; a collision or current-vertex calculation is still needed
before connecting this microscopic spectral lifetime to the longitudinal RTA benchmark.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- The decay half-width extracted from the finite-cutoff retarded upper-band projection converges
to the canonical positive Born damping energy. -/
theorem tendsto_finiteCutoffContinuumBornRetardedUpperBandFermiProjection_decayWidth_broadening_zero
    (v m fermiEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hm : 0 < m) (hmF : m < fermiEnergy)
    (hcutoff : fermiEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        retardedSelfEnergyDecayWidth
          (finiteCutoffContinuumBornRetardedUpperBandFermiProjection
            v m fermiEnergy broadening disorderStrength hbar pMax))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (continuumBornUpperBandDampingEnergy
        v m fermiEnergy disorderStrength hbar)) := by
  simpa [retardedSelfEnergyDecayWidth] using
    (tendsto_finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_dampingEnergy
      v m fermiEnergy disorderStrength hbar pMax
      hvelocity hhbar hm hmF hcutoff).neg

/-- Typed positive Born single-particle lifetime of the metallic upper band.

Its scalar value is proved below to agree with the already-derived model lifetime. -/
noncomputable def continuumBornUpperBandPositiveSingleParticleLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) : PositiveSingleParticleLifetime :=
  singleParticleLifetimeOfDecayWidth hbar
    (continuumBornUpperBandDampingEnergy v m fermiEnergy disorderStrength hbar)
    hhbar
    (continuumBornUpperBandDampingEnergy_pos
      v m fermiEnergy disorderStrength hbar
      hvelocity (ne_of_gt hhbar) hdisorder hm hmF)

@[simp] theorem continuumBornUpperBandPositiveSingleParticleLifetime_lifetime_decayWidth
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    (continuumBornUpperBandPositiveSingleParticleLifetime
      v m fermiEnergy disorderStrength hbar
      hvelocity hhbar hdisorder hm hmF).lifetime =
      hbar /
        (2 * continuumBornUpperBandDampingEnergy
          v m fermiEnergy disorderStrength hbar) := by
  rfl

/-- The typed lifetime agrees exactly with the scalar lifetime already derived as the reciprocal of
the microscopic Born scattering rate. -/
theorem continuumBornUpperBandPositiveSingleParticleLifetime_lifetime_eq_model
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    (continuumBornUpperBandPositiveSingleParticleLifetime
      v m fermiEnergy disorderStrength hbar
      hvelocity hhbar hdisorder hm hmF).lifetime =
      continuumBornUpperBandSingleParticleLifetime
        v m fermiEnergy disorderStrength hbar := by
  rw [continuumBornUpperBandPositiveSingleParticleLifetime_lifetime_decayWidth]
  unfold continuumBornUpperBandSingleParticleLifetime
    continuumBornUpperBandSingleParticleScatteringRate
  have hwidthPos := continuumBornUpperBandDampingEnergy_pos
    v m fermiEnergy disorderStrength hbar
    hvelocity (ne_of_gt hhbar) hdisorder hm hmF
  have hwidthNe :
      continuumBornUpperBandDampingEnergy v m fermiEnergy disorderStrength hbar ≠ 0 :=
    ne_of_gt hwidthPos
  have hhbarNe : hbar ≠ 0 := ne_of_gt hhbar
  field_simp [hwidthNe, hhbarNe]

/-- Closed form of the typed upper-band Born single-particle lifetime,

`τ_q = 2 ℏ³ v² ε_F / [disorderStrength (ε_F² + m²)]`. -/
theorem continuumBornUpperBandPositiveSingleParticleLifetime_eq_closed
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    (continuumBornUpperBandPositiveSingleParticleLifetime
      v m fermiEnergy disorderStrength hbar
      hvelocity hhbar hdisorder hm hmF).lifetime =
      2 * hbar ^ 3 * v ^ 2 * fermiEnergy /
        (disorderStrength * (fermiEnergy ^ 2 + m ^ 2)) := by
  rw [continuumBornUpperBandPositiveSingleParticleLifetime_lifetime_decayWidth]
  unfold continuumBornUpperBandDampingEnergy
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt (lt_trans hm hmF)
  have hhbarNe : hbar ≠ 0 := ne_of_gt hhbar
  have hdisorderNe : disorderStrength ≠ 0 := ne_of_gt hdisorder
  field_simp [hvelocity, hhbarNe, hdisorderNe, hfermiNe]
  ring

/-- Closed form of the existing scalar model lifetime, obtained through the typed lifetime bridge. -/
theorem continuumBornUpperBandSingleParticleLifetime_eq_closed
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    continuumBornUpperBandSingleParticleLifetime
        v m fermiEnergy disorderStrength hbar =
      2 * hbar ^ 3 * v ^ 2 * fermiEnergy /
        (disorderStrength * (fermiEnergy ^ 2 + m ^ 2)) := by
  rw [← continuumBornUpperBandPositiveSingleParticleLifetime_lifetime_eq_model
    v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hm hmF]
  exact continuumBornUpperBandPositiveSingleParticleLifetime_eq_closed
    v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hm hmF

end

end AnomalousHall.MassiveDirac
