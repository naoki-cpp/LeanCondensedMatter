import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.UpperBandDamping
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Metallic upper-band Born single-particle scattering rate

This Phase 4 slice converts the already-proved on-shell upper-band Born damping energy into the
single-particle scattering-rate convention used by the weak-disorder retarded/advanced propagators.
The rate is derived from the microscopic Born damping,

```text
1 / τ_sp = 2 Γ_Born / ℏ,
```

and the corresponding lifetime is only its reciprocal.  Neither quantity is a supplied transport
relaxation time, and no identification with the phenomenological `PositiveTransportLifetime` /
`τ_tr` is made here.

This convention matches the massive-Dirac weak-disorder propagator in Ado et al., EPL 111, 37004
(2015), arXiv:1504.03658, Eq. (8): in their `ℏ = v = 1` convention the imaginary Born self-energy
produces the electron scattering rate entering the disorder-averaged retarded Green function.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Upper-band Born single-particle scattering rate derived from the on-shell damping half-width.

This is the convention `1 / τ_sp = 2 Γ_Born / ℏ`.  It is a model-specific microscopic output, not
the phenomenological current-relaxation time `τ_tr`. -/
def continuumBornUpperBandSingleParticleScatteringRate
    (v m fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  2 * continuumBornUpperBandDampingEnergy
      v m fermiEnergy disorderStrength hbar / hbar

/-- Closed physical-momentum expression for the upper-band Born single-particle scattering rate. -/
theorem continuumBornUpperBandSingleParticleScatteringRate_eq
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandSingleParticleScatteringRate
        v m fermiEnergy disorderStrength hbar =
      disorderStrength / (2 * hbar ^ 3 * v ^ 2) *
        (fermiEnergy + m ^ 2 / fermiEnergy) := by
  unfold continuumBornUpperBandSingleParticleScatteringRate
    continuumBornUpperBandDampingEnergy
  (field_simp [hvelocity, hhbar, hfermiEnergy]; ring)

/-- The Born single-particle scattering rate is nonzero whenever its algebraic prefactors and Fermi
energy are nonzero. -/
theorem continuumBornUpperBandSingleParticleScatteringRate_ne_zero
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : disorderStrength ≠ 0)
    (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandSingleParticleScatteringRate
      v m fermiEnergy disorderStrength hbar ≠ 0 := by
  rw [continuumBornUpperBandSingleParticleScatteringRate_eq
    v m fermiEnergy disorderStrength hbar hvelocity hhbar hfermiEnergy]
  apply mul_ne_zero
  · exact div_ne_zero hdisorder
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hhbar))
        (pow_ne_zero 2 hvelocity))
  · have hsum : fermiEnergy ^ 2 + m ^ 2 ≠ 0 := by
      exact ne_of_gt
        (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hfermiEnergy) (sq_nonneg m))
    have hterm :
        fermiEnergy + m ^ 2 / fermiEnergy =
          (fermiEnergy ^ 2 + m ^ 2) / fermiEnergy := by
      field_simp [hfermiEnergy]
    rw [hterm]
    exact div_ne_zero hsum hfermiEnergy

/-- The Born single-particle scattering rate is positive for positive `ℏ` and positive disorder
strength in the strict metallic regime. -/
theorem continuumBornUpperBandSingleParticleScatteringRate_pos
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    0 < continuumBornUpperBandSingleParticleScatteringRate
      v m fermiEnergy disorderStrength hbar := by
  unfold continuumBornUpperBandSingleParticleScatteringRate
  exact div_pos
    (mul_pos (by norm_num)
      (continuumBornUpperBandDampingEnergy_pos
        v m fermiEnergy disorderStrength hbar
        hvelocity (ne_of_gt hhbar) hdisorder hm hmF))
    hhbar

/-- The damping energy is one half of `ℏ` times the derived single-particle scattering rate. -/
theorem continuumBornUpperBandDampingEnergy_eq_half_hbar_mul_scatteringRate
    (v m fermiEnergy disorderStrength hbar : ℝ) (hhbar : hbar ≠ 0) :
    continuumBornUpperBandDampingEnergy
        v m fermiEnergy disorderStrength hbar =
      (hbar / 2) *
        continuumBornUpperBandSingleParticleScatteringRate
          v m fermiEnergy disorderStrength hbar := by
  unfold continuumBornUpperBandSingleParticleScatteringRate
  field_simp [hhbar]

/-- Upper-band Born single-particle lifetime, defined only as the reciprocal of the microscopic
Born scattering rate.  It is not an independent relaxation-time input. -/
def continuumBornUpperBandSingleParticleLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  (continuumBornUpperBandSingleParticleScatteringRate
    v m fermiEnergy disorderStrength hbar)⁻¹

/-- The derived Born single-particle lifetime is positive in the physical metallic regime. -/
theorem continuumBornUpperBandSingleParticleLifetime_pos
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    0 < continuumBornUpperBandSingleParticleLifetime
      v m fermiEnergy disorderStrength hbar := by
  unfold continuumBornUpperBandSingleParticleLifetime
  exact inv_pos.mpr
    (continuumBornUpperBandSingleParticleScatteringRate_pos
      v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hm hmF)

/-- The derived scattering rate and lifetime are reciprocal whenever the rate prefactors and Fermi
energy are nonzero. -/
theorem continuumBornUpperBandSingleParticleScatteringRate_mul_lifetime
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : disorderStrength ≠ 0)
    (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandSingleParticleScatteringRate
        v m fermiEnergy disorderStrength hbar *
      continuumBornUpperBandSingleParticleLifetime
        v m fermiEnergy disorderStrength hbar = 1 := by
  have hrateNe :=
    continuumBornUpperBandSingleParticleScatteringRate_ne_zero
      v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hfermiEnergy
  unfold continuumBornUpperBandSingleParticleLifetime
  simp [hrateNe]

/-- Equivalent lifetime form of the Born pole-width convention,
`Γ_Born = ℏ / (2 τ_sp)`. -/
theorem continuumBornUpperBandDampingEnergy_eq_hbar_div_two_lifetime
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : disorderStrength ≠ 0)
    (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandDampingEnergy
        v m fermiEnergy disorderStrength hbar =
      hbar /
        (2 * continuumBornUpperBandSingleParticleLifetime
          v m fermiEnergy disorderStrength hbar) := by
  have hrateNe :=
    continuumBornUpperBandSingleParticleScatteringRate_ne_zero
      v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hfermiEnergy
  rw [continuumBornUpperBandDampingEnergy_eq_half_hbar_mul_scatteringRate
    v m fermiEnergy disorderStrength hbar hhbar]
  unfold continuumBornUpperBandSingleParticleLifetime
  field_simp [hrateNe]

end

end AnomalousHall.MassiveDirac
