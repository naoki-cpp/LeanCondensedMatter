import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialFrozenUV

set_option linter.style.header false

/-!
# Exact Bessel-J representation of the cutoff-independent massive-Dirac Green kernel

The ultraviolet finite part established in `Born.RadialUVFinitePart` is
written entirely in Mathlib's **actual first-kind Bessel functions**
`Complex.besselJ 0` and `Complex.besselJ 1`, not the abstract polar
angular Fourier kernels. It depends on the complex *spectral center*
`s = E²-M²`, allowing its later identification with an outgoing
Hankel function of `sqrt(s) r / v`.

The order-one Bessel integral is absolutely convergent on the UV tail.
No arbitrary Bessel-Y function, Wronskian assumption, or unproved
Hankel identity is used. This provides an exact, normalized analytic
boundary for the remaining Hankel-Y identification in Phase 7.

The physically cut-off Born effective parameters are **frozen** during
the outer momentum-UV limit. No diagonal Born cutoff limit is claimed.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- Fully explicit Bessel-J form of the massive-Dirac Fourier UV finite
part, parametrized by the complex quadratic spectral center rather
than separate energy and mass. The factors of `2π` and `i` are
inherited from the exact full-angle Fourier–Bessel identities. -/
noncomputable def massiveDiracRadialBesselJCenterUVFinitePartAt
    (v c a : ℝ) (center : ℂ) : ℂ :=
  (∫ p in (0 : ℝ)..a,
      (p : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) * Complex.besselJ 0 ((p * c : ℝ) : ℂ)) *
        (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) +
    ((-((a : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          Complex.besselJ 1 ((a * c : ℝ) : ℂ)) *
        (center - ((v ^ 2 * a ^ 2 : ℝ) : ℂ))⁻¹) -
      ∫ p in Set.Ioi a,
        (p : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            Complex.besselJ 1 ((p * c : ℝ) : ℂ)) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹ ^ 2)) /
      (Complex.I * (c : ℂ)))

/-- No assumptions are needed for the finite-part change of basis:
the result is *exactly* the full-angle Bessel J0/J1 transform with
its spectral center `E²-M²`, including both UV boundary terms. -/
theorem massiveDiracRadialFourierUVFinitePartAt_eq_besselJCenter
    (v c a : ℝ) (energy mass : ℂ) :
    massiveDiracRadialFourierUVFinitePartAt v c a energy mass =
      massiveDiracRadialBesselJCenterUVFinitePartAt
        v c a (energy ^ 2 - mass ^ 2) := by
  unfold massiveDiracRadialFourierUVFinitePartAt
    massiveDiracRadialBesselJCenterUVFinitePartAt
  simp_rw [polarFourierZerothAngularKernel_eq_besselJ,
    polarFourierFirstCosineAngularKernel_eq_besselJ]
  rfl

/-- Canonically normalized Bessel-J spectral-center Fourier value.
Its split scale is fixed solely by the norm of the spectral center,
not by an arbitrary choice of energy/mass decomposition. -/
noncomputable def massiveDiracRadialBesselJCenterUVValue
    (v c : ℝ) (center : ℂ) : ℂ :=
  massiveDiracRadialBesselJCenterUVFinitePartAt
    v c (max (1 : ℝ) (2 * ‖center‖ / v ^ 2)) center

/-- The existing explicitly evaluated Fourier UV finite part is
precisely the Bessel-J spectral-center value, not an unrelated
model of the Green function or a hypothesized Hankel boundary. -/
theorem massiveDiracRadialFourierUVValue_eq_besselJCenter
    (v c : ℝ) (energy mass : ℂ) :
    massiveDiracRadialFourierUVValue v c energy mass =
      massiveDiracRadialBesselJCenterUVValue
        v c (energy ^ 2 - mass ^ 2) := by
  unfold massiveDiracRadialFourierUVValue massiveDiracRadialBesselJCenterUVValue
  exact massiveDiracRadialFourierUVFinitePartAt_eq_besselJCenter
    v c (max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2)) energy mass

/-- Exact order-zero Bessel-J resolvent UV limit, with an explicitly
identified finite part and a standard complex spectral branch condition.
In particular, the normalization of J0 is `2π`, not unity. -/
theorem massiveDiracRadialBesselJ_tendsto_uvValue
    (v c : ℝ) (energy mass : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hcenter : (energy ^ 2 - mass ^ 2).im ≠ 0) :
    Filter.Tendsto
      (fun b : ℝ => ∫ p in (0 : ℝ)..b,
        (p : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) *
            Complex.besselJ 0 ((p * c : ℝ) : ℂ)) *
          (energy ^ 2 - mass ^ 2 - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹)
      Filter.atTop
      (nhds (massiveDiracRadialBesselJCenterUVValue
        v c (energy ^ 2 - mass ^ 2))) := by
  have hlimit := massiveDiracRadialFourier_tendsto_uvValue
    v c energy mass hv hc hcenter
  rw [massiveDiracRadialFourierUVValue_eq_besselJCenter] at hlimit
  simpa only [polarFourierZerothAngularKernel_eq_besselJ,
    massiveDiracRadialDenominator] using hlimit

/-- The finite-Born reference-cutoff radial Green UV value inherits
exactly the same canonical Bessel-J spectral center. The physical
momentum-measure prefactor is carried once, unchanged from the
original finite-cutoff propagator. -/
theorem finiteCutoffContinuumBornDysonRadialFrozenUVValue_eq_besselJCenter
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pRef radius : ℝ) :
    finiteCutoffContinuumBornDysonRadialFrozenUVValue
      side v m probeEnergy broadening disorderStrength hbar pRef radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        massiveDiracRadialBesselJCenterUVValue v (radius / hbar)
          ((finiteCutoffContinuumBornEffectiveEnergy
              side v m probeEnergy broadening disorderStrength hbar pRef) ^ 2 -
           (finiteCutoffContinuumBornEffectiveMass
              side v m probeEnergy broadening disorderStrength hbar pRef) ^ 2) := by
  unfold finiteCutoffContinuumBornDysonRadialFrozenUVValue
  dsimp only
  rw [massiveDiracRadialFourierUVValue_eq_besselJCenter]

end

end QuantumTheory.Models.MassiveDirac
