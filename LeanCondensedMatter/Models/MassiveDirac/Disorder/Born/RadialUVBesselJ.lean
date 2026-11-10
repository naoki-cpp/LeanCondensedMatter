import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialFrozenUV
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVSpectralConjugation

set_option linter.style.header false

/-!
# Massive-Dirac radial UV Fourier value in the Bessel-J representation

The cutoff-independent radial Fourier UV value is expressed in terms of
`Complex.besselJ 0` and `Complex.besselJ 1` at the quadratic spectral center
`s = E² - M²`. The order-one tail integral is absolutely convergent.
The normalization is fixed by the polar Fourier kernels.

The Born effective energy and mass are held fixed during the outer momentum
UV limit. Schwarz reflection follows from the finite-cutoff conjugation
identity and uniqueness of the spectral UV limit.

-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval ComplexConjugate

/-- Fully explicit Bessel-J form of the massive-Dirac Fourier UV finite
part, parametrized by the complex quadratic spectral center rather
than separate energy and mass. The factors of `2π` and `i` follow from the full-angle Fourier–Bessel identities. -/
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
theorem massiveDiracRadialFourierUVFinitePartCenter_eq_besselJCenter
    (v c a : ℝ) (center : ℂ) :
    massiveDiracRadialFourierUVFinitePartCenter v c a center =
      massiveDiracRadialBesselJCenterUVFinitePartAt v c a center := by
  unfold massiveDiracRadialFourierUVFinitePartCenter
    massiveDiracRadialBesselJCenterUVFinitePartAt
  simp_rw [polarFourierZerothAngularKernel_eq_besselJ,
    polarFourierFirstCosineAngularKernel_eq_besselJ]

/-- Canonically normalized Bessel-J spectral-center Fourier value.
Its split scale is fixed solely by the norm of the spectral center,
not by an arbitrary choice of energy/mass decomposition. -/
noncomputable def massiveDiracRadialBesselJCenterUVValue
    (v c : ℝ) (center : ℂ) : ℂ :=
  massiveDiracRadialBesselJCenterUVFinitePartAt
    v c (max (1 : ℝ) (2 * ‖center‖ / v ^ 2)) center

/-- The Fourier UV finite part equals the Bessel-J spectral-center value. -/
theorem massiveDiracRadialFourierUVCenter_eq_besselJCenter
    (v c : ℝ) (center : ℂ) :
    massiveDiracRadialFourierUVCenter v c center =
      massiveDiracRadialBesselJCenterUVValue v c center := by
  unfold massiveDiracRadialFourierUVCenter massiveDiracRadialBesselJCenterUVValue
  exact massiveDiracRadialFourierUVFinitePartCenter_eq_besselJCenter
    v c (max (1 : ℝ) (2 * ‖center‖ / v ^ 2)) center

/-- Exact order-zero Bessel-J resolvent UV limit, with an explicitly
identified finite part and a standard complex spectral branch condition.
In particular, the normalization of J0 is `2π`, not unity. -/
theorem massiveDiracRadialBesselJ_tendsto_uvValue
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hcenter : center.im ≠ 0) :
    Filter.Tendsto
      (fun b : ℝ => ∫ p in (0 : ℝ)..b,
        (p : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) *
            Complex.besselJ 0 ((p * c : ℝ) : ℂ)) *
          (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹)
      Filter.atTop
      (nhds (massiveDiracRadialBesselJCenterUVValue v c center)) := by
  have hlimit := massiveDiracRadialFourier_tendsto_uvValue_center
    v c center hv hc hcenter
  rw [massiveDiracRadialFourierUVCenter_eq_besselJCenter] at hlimit
  simpa only [polarFourierZerothAngularKernel_eq_besselJ] using hlimit

/-- The finite-Born reference-cutoff radial Green UV value has the same
Bessel-J spectral center and one physical momentum-measure prefactor. -/
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
  rw [massiveDiracRadialFourierUVCenter_eq_besselJCenter]


/-- Schwarz reflection of the Bessel-J UV value under conjugation of its
quadratic spectral center, away from the real axis. -/
theorem massiveDiracRadialBesselJCenterUVValue_conj
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hcenter : center.im ≠ 0) :
    conj (massiveDiracRadialBesselJCenterUVValue v c center) =
      massiveDiracRadialBesselJCenterUVValue v c (conj center) := by
  calc
    conj (massiveDiracRadialBesselJCenterUVValue v c center) =
        conj (massiveDiracRadialFourierUVCenter v c center) := by
      rw [massiveDiracRadialFourierUVCenter_eq_besselJCenter]
    _ = massiveDiracRadialFourierUVCenter v c (conj center) :=
      massiveDiracRadialFourierUVCenter_conj v c center hv hc hcenter
    _ = massiveDiracRadialBesselJCenterUVValue v c (conj center) :=
      massiveDiracRadialFourierUVCenter_eq_besselJCenter v c (conj center)

end

end QuantumTheory.Models.MassiveDirac
