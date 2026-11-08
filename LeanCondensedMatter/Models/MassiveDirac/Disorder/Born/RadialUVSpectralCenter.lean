import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVFinitePart
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.RCLike.Sqrt

set_option linter.style.header false

/-!
# Spectral-center form of the ultraviolet Dirac Fourier Green function

The momentum-UV finite part of the 2D massive-Dirac K0 Fourier
resolvent depends on the complex spectral parameters only through
the quadratic *center* Z = E² - M². We introduce a center-indexed
canonical function without choosing any complex square-root branch,
and prove it agrees identically with the explicitly evaluated
finite-part expression from PR #4514.

The resulting UV Green kernel is even in the real radial Fourier
argument and respects complex conjugation of the center. These facts
are proved from the finite Fourier integrals and *uniqueness of their
UV limits*; they do not assume a second-kind Bessel/Hankel API.

For a subsequent explicit Hankel representation, DLMF 10.22.46
indicates the modified Bessel K0 at sqrt(-Z)*|c/v|, with the correct
outgoing boundary fixed by Im(Z). Mathlib v4.35.0 has only the
first-kind Complex.besselJ, not Complex.besselK/Y. No such identity
is postulated or claimed proved here.

In particular, fixed E,M are NOT the running Born parameters of
the physical nonzero-disorder diagonal UV limit, which needs a
renormalization and a separate uniform convergence theorem.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval ComplexConjugate

/-- Canonical explicit finite part indexed by the only spectral
combination present in the massive-Dirac quadratic denominator. -/
noncomputable def massiveDiracRadialFourierUVFinitePartCenter
    (v c a : ℝ) (center : ℂ) : ℂ :=
  (∫ p in (0 : ℝ)..a,
      (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
        (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) +
    ((-((a : ℂ) * polarFourierFirstCosineAngularKernel (a * c) *
        (center - ((v ^ 2 * a ^ 2 : ℝ) : ℂ))⁻¹) -
      ∫ p in Set.Ioi a,
        (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹ ^ 2)) /
      (Complex.I * (c : ℂ)))

/-- The finite-part formula is literally a function of E²-M²:
neither separate E nor M survives its UV definition. -/
theorem massiveDiracRadialFourierUVFinitePartAt_eq_center
    (v c a : ℝ) (energy mass : ℂ) :
    massiveDiracRadialFourierUVFinitePartAt v c a energy mass =
      massiveDiracRadialFourierUVFinitePartCenter
        v c a (energy ^ 2 - mass ^ 2) := by
  rfl

/-- Canonical center-only UV Green function. Its split point is determined
solely by |Z| and the real quadratic-dispersion scale v². -/
noncomputable def massiveDiracRadialFourierUVCenter
    (v c : ℝ) (center : ℂ) : ℂ :=
  massiveDiracRadialFourierUVFinitePartCenter
    v c (max (1 : ℝ) (2 * ‖center‖ / v ^ 2)) center

/-- The canonical fixed-spectral Fourier UV value from #4514 is exactly
the center-only form, with no square-root branch choice. -/
theorem massiveDiracRadialFourierUVValue_eq_center
    (v c : ℝ) (energy mass : ℂ) :
    massiveDiracRadialFourierUVValue v c energy mass =
      massiveDiracRadialFourierUVCenter v c (energy ^ 2 - mass ^ 2) := by
  rfl

/-- Two possibly different complex energy/mass pairs with equal quadratic
spectral centers have the same canonical Fourier ultraviolet value. -/
theorem massiveDiracRadialFourierUVValue_eq_of_center
    (v c : ℝ) (energy mass energy' mass' : ℂ)
    (hcenter : energy ^ 2 - mass ^ 2 = energy' ^ 2 - mass' ^ 2) :
    massiveDiracRadialFourierUVValue v c energy mass =
      massiveDiracRadialFourierUVValue v c energy' mass' := by
  rw [massiveDiracRadialFourierUVValue_eq_center,
    massiveDiracRadialFourierUVValue_eq_center, hcenter]

/-- Evenness of the canonical K0 Fourier UV boundary in real-space
separation. This follows from the Fourier K0 parity and the unique
fixed-spectral-center cutoff limit, without a Hankel formula. -/
theorem massiveDiracRadialFourierUVValue_neg
    (v c : ℝ) (energy mass : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hcenter : (energy ^ 2 - mass ^ 2).im ≠ 0) :
    massiveDiracRadialFourierUVValue v (-c) energy mass =
      massiveDiracRadialFourierUVValue v c energy mass := by
  have hneg := massiveDiracRadialFourier_tendsto_uvValue
    v (-c) energy mass hv (neg_ne_zero.mpr hc) hcenter
  have hpos := massiveDiracRadialFourier_tendsto_uvValue
    v c energy mass hv hc hcenter
  have heq (b : ℝ) :
      (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * -c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹) =
      (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹) := by
    apply intervalIntegral.integral_congr
    intro p _
    dsimp only
    rw [show p * -c = -(p * c) by ring,
      polarFourierZerothAngularKernel_neg]
  exact tendsto_nhds_unique
    (hneg.congr' (Filter.Eventually.of_forall heq))
    hpos

/-- The center-indexed canonical UV Green function is even for every
complex spectral center away from the real axis. -/
theorem complex_sqrt_sq_spectral_center (z : ℂ) :
    (Complex.sqrt z) ^ 2 = z := by
  simpa [Complex.sqrt] using (Complex.cpow_ofNat_inv_pow z 2)

/-- Center-argument parity, independent of the chosen square root. -/
theorem massiveDiracRadialFourierUVCenter_neg
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hcenter : center.im ≠ 0) :
    massiveDiracRadialFourierUVCenter v (-c) center =
      massiveDiracRadialFourierUVCenter v c center := by
  have hminus : (Complex.sqrt center) ^ 2 - (0 : ℂ) ^ 2 = center := by
    simp [complex_sqrt_sq_spectral_center]
  have h := massiveDiracRadialFourierUVValue_neg
    v c (Complex.sqrt center) 0 hv hc (by simpa [hminus] using hcenter)
  rw [massiveDiracRadialFourierUVValue_eq_center,
    massiveDiracRadialFourierUVValue_eq_center, hminus] at h
  exact h

end

end QuantumTheory.Models.MassiveDirac
