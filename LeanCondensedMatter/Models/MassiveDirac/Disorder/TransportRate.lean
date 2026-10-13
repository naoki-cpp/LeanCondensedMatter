import LeanCondensedMatter.Transport.Analysis.RelaxationTime
import LeanCondensedMatter.Models.MassiveDirac.Disorder.SingleParticleRate
import LeanCondensedMatter.Models.MassiveDirac.Disorder.ScalarAngularWeights
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Metallic upper-band Born transport scattering

The single-particle scattering rate and lifetime follow from Born damping in
`Disorder.SingleParticleRate`. This module owns the upper-band transport scattering rate and
lifetime for short-range scalar disorder, using the same Fermi-circle normalization and
the additional current-relaxing factor `1 - cos θ`.

For `|m| < ε_F`, the gauge-independent upper-band projector overlap reduces to

```text
W(θ) = [1 + m²/ε_F² + (1 - m²/ε_F²) cos θ] / 2,
```

so the unweighted and transport-weighted angular means (derived in `ScalarAngularWeights`)
give the relation between `τ_sp` and `τ_tr`.
No Kubo ladder equation, Ward identity, crossed diagram, or identification with the exact disorder-
averaged conductivity is claimed here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Common continuum Born Fermi-circle rate prefactor after isolating the dimensionless projector
angular weight. Its normalization is checked below against the already-derived self-energy rate. -/
def continuumBornUpperBandFermiCircleRatePrefactor
    (v fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength * fermiEnergy / (hbar ^ 3 * v ^ 2)

/-- The microscopic single-particle rate factorizes into the common Fermi-circle prefactor and the
unweighted projector-overlap average whenever the algebraic denominators are nonzero. -/
theorem continuumBornUpperBandSingleParticleScatteringRate_eq_prefactor_mul_angularWeight
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandSingleParticleScatteringRate
        v m fermiEnergy disorderStrength hbar =
      continuumBornUpperBandFermiCircleRatePrefactor
          v fermiEnergy disorderStrength hbar *
        isotropicUpperBandSingleParticleAngularWeight v m fermiEnergy := by
  rw [continuumBornUpperBandSingleParticleScatteringRate_eq
    v m fermiEnergy disorderStrength hbar hvelocity hhbar hfermiEnergy]
  rw [isotropicUpperBandSingleParticleAngularWeight_eq v m fermiEnergy]
  unfold continuumBornUpperBandFermiCircleRatePrefactor
  field_simp [hvelocity, hhbar, hfermiEnergy]

/-- Upper-band Born transport scattering rate obtained from the same microscopic scalar-disorder
normalization as `1/τ_sp`, but with the current-relaxing `1 - cos θ` angular weight. -/
def continuumBornUpperBandTransportScatteringRate
    (v m fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornUpperBandFermiCircleRatePrefactor
      v fermiEnergy disorderStrength hbar *
    isotropicUpperBandTransportAngularWeight v m fermiEnergy

/-- Closed physical-momentum expression for the upper-band Born transport scattering rate. -/
theorem continuumBornUpperBandTransportScatteringRate_eq
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandTransportScatteringRate
        v m fermiEnergy disorderStrength hbar =
      disorderStrength / (4 * hbar ^ 3 * v ^ 2) *
        (fermiEnergy + 3 * m ^ 2 / fermiEnergy) := by
  rw [continuumBornUpperBandTransportScatteringRate,
    isotropicUpperBandTransportAngularWeight_eq v m fermiEnergy]
  unfold continuumBornUpperBandFermiCircleRatePrefactor
  field_simp [hvelocity, hhbar, hfermiEnergy]

/-- The Born transport scattering rate is positive for positive disorder strength and positive
`ℏ` in the strict metallic regime `|m| < εF`. -/
theorem continuumBornUpperBandTransportScatteringRate_pos
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hmF : |m| < fermiEnergy) :
    0 < continuumBornUpperBandTransportScatteringRate
      v m fermiEnergy disorderStrength hbar := by
  have hfermiPos : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  rw [continuumBornUpperBandTransportScatteringRate_eq
    v m fermiEnergy disorderStrength hbar hvelocity (ne_of_gt hhbar) hfermiNe]
  have hnum : 0 < fermiEnergy + 3 * m ^ 2 / fermiEnergy := by positivity
  have hden : 0 < 4 * hbar ^ 3 * v ^ 2 := by positivity
  exact mul_pos (div_pos hdisorder hden) hnum

/-- The transport rate relative to the single-particle rate is fixed entirely by the massive-Dirac
Fermi-circle angular structure whenever the common rate prefactors and Fermi energy are nonzero. -/
theorem continuumBornUpperBandTransportRate_div_singleParticleRate
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : disorderStrength ≠ 0)
    (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandTransportScatteringRate
        v m fermiEnergy disorderStrength hbar /
      continuumBornUpperBandSingleParticleScatteringRate
        v m fermiEnergy disorderStrength hbar =
      (fermiEnergy ^ 2 + 3 * m ^ 2) /
        (2 * (fermiEnergy ^ 2 + m ^ 2)) := by
  rw [continuumBornUpperBandTransportScatteringRate_eq
      v m fermiEnergy disorderStrength hbar hvelocity hhbar hfermiEnergy,
    continuumBornUpperBandSingleParticleScatteringRate_eq
      v m fermiEnergy disorderStrength hbar hvelocity hhbar hfermiEnergy]
  field_simp [hvelocity, hhbar, hfermiEnergy, hdisorder]
  ring

/-- Upper-band Born transport lifetime, defined as the reciprocal of the derived transport rate. -/
def continuumBornUpperBandTransportLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  (continuumBornUpperBandTransportScatteringRate
    v m fermiEnergy disorderStrength hbar)⁻¹

/-- The microscopic Born transport lifetime is positive in the physical metallic regime. -/
theorem continuumBornUpperBandTransportLifetime_pos
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hmF : |m| < fermiEnergy) :
    0 < continuumBornUpperBandTransportLifetime
      v m fermiEnergy disorderStrength hbar := by
  unfold continuumBornUpperBandTransportLifetime
  exact inv_pos.mpr
    (continuumBornUpperBandTransportScatteringRate_pos
      v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hmF)

/-- The transport lifetime differs from the single-particle lifetime by the reciprocal angular
factor whenever the common Born prefactors and Fermi energy are nonzero. -/
theorem continuumBornUpperBandTransportLifetime_eq_factor_mul_singleParticleLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : disorderStrength ≠ 0)
    (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandTransportLifetime
        v m fermiEnergy disorderStrength hbar =
      (2 * (fermiEnergy ^ 2 + m ^ 2) /
          (fermiEnergy ^ 2 + 3 * m ^ 2)) *
        continuumBornUpperBandSingleParticleLifetime
          v m fermiEnergy disorderStrength hbar := by
  rw [continuumBornUpperBandTransportLifetime,
    continuumBornUpperBandSingleParticleLifetime]
  rw [continuumBornUpperBandTransportScatteringRate_eq
      v m fermiEnergy disorderStrength hbar hvelocity hhbar hfermiEnergy,
    continuumBornUpperBandSingleParticleScatteringRate_eq
      v m fermiEnergy disorderStrength hbar hvelocity hhbar hfermiEnergy]
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_ne_zero hfermiEnergy
  have hsum1 : fermiEnergy ^ 2 + m ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hfermiSq (sq_nonneg m))
  have hsum3 : fermiEnergy ^ 2 + 3 * m ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hfermiSq
      (mul_nonneg (by norm_num) (sq_nonneg m)))
  (field_simp [hvelocity, hhbar, hfermiEnergy, hdisorder, hsum1, hsum3]; ring)

/-- Package the microscopic Born transport lifetime as the generic positive current-relaxation datum
consumed by the longitudinal RTA benchmark. This bridge does not identify the derivation with a
Kubo ladder resummation; it only records the positive scalar lifetime obtained from the Born angular
transport kernel above. -/
def continuumBornUpperBandPositiveTransportLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hmF : |m| < fermiEnergy) : PositiveTransportLifetime where
  lifetime := continuumBornUpperBandTransportLifetime
    v m fermiEnergy disorderStrength hbar
  lifetime_pos := continuumBornUpperBandTransportLifetime_pos
    v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hmF

end

end QuantumTheory.Models.MassiveDirac
