import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVBesselJ

set_option linter.style.header false

/-!
# Causal Schwarz reflection of the complex spectral Green UV value

The explicitly constructed UV Fourier value is compatible with
complex conjugation of both spectral parameters. This is obtained
from the exact *finite*-momentum Fourier-conjugation identity and
uniqueness of the **proved** complex UV limit, with no unlicensed
exchange of conjugation and improper integration.

The spectral-center Bessel-J representation inherits the same
retarded/advanced reflection. This is the causal normalization
required for an eventual outgoing/incoming Hankel identification;
it does not itself identify either branch with a Bessel-Y function
or establish a Sommerfeld outgoing-wave condition.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval ComplexConjugate

/-- Complex conjugation of the exact finite-momentum radial Fourier
resolvent is obtained by conjugating its spectral energy and mass.
The K0 kernel is real for real spatial arguments. -/
theorem massiveDiracRadialFourierInterval_conj
    (v c cutoff : ℝ) (energy mass : ℂ) :
    conj (∫ p in (0 : ℝ)..cutoff,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹) =
      ∫ p in (0 : ℝ)..cutoff,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p (conj energy) (conj mass))⁻¹ := by
  have hmove :
      conj (∫ p in (0 : ℝ)..cutoff,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹) =
        ∫ p in (0 : ℝ)..cutoff,
          conj ((p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹) := by
    simpa using
      ((Complex.conjLIE.toLinearIsometry).intervalIntegral_comp_comm
        (f := fun p : ℝ =>
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹)
        (a := (0 : ℝ)) (b := cutoff)).symm
  rw [hmove]
  apply intervalIntegral.integral_congr
  intro p _
  simp only [map_mul, Complex.conj_ofReal,
    polarFourierZerothAngularKernel_conj, Complex.conj_inv]
  have hden :
      conj (massiveDiracRadialDenominator v p energy mass) =
        massiveDiracRadialDenominator v p (conj energy) (conj mass) := by
    simp only [massiveDiracRadialDenominator, map_sub, map_pow,
      Complex.conj_ofReal]
  rw [hden]

/-- The outgoing/incoming complex UV values satisfy Schwarz reflection
at fixed non-real spectral center. In particular, this does not
claim differentiability or outgoing asymptotics of the UV value. -/
theorem massiveDiracRadialFourierUVValue_conj
    (v c : ℝ) (energy mass : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hcenter : (energy ^ 2 - mass ^ 2).im ≠ 0) :
    conj (massiveDiracRadialFourierUVValue v c energy mass) =
      massiveDiracRadialFourierUVValue v c (conj energy) (conj mass) := by
  have hcenter' : ((conj energy) ^ 2 - (conj mass) ^ 2).im ≠ 0 := by
    have heq :
        (conj energy) ^ 2 - (conj mass) ^ 2 =
          conj (energy ^ 2 - mass ^ 2) := by
      simp only [map_sub, map_pow]
    rw [heq, Complex.conj_im]
    exact neg_ne_zero.mpr hcenter
  have hret := massiveDiracRadialFourier_tendsto_uvValue
    v c energy mass hv hc hcenter
  have hconj :
      Filter.Tendsto
        (fun b : ℝ => conj (∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹))
        Filter.atTop
        (nhds (conj (massiveDiracRadialFourierUVValue
          v c energy mass))) :=
    (Complex.continuous_conj.tendsto _).comp hret
  have hadv := massiveDiracRadialFourier_tendsto_uvValue
    v c (conj energy) (conj mass) hv hc hcenter'
  have heq (b : ℝ) :
      conj (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹) =
      ∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p
            (conj energy) (conj mass))⁻¹ :=
    massiveDiracRadialFourierInterval_conj v c b energy mass
  have hconj' := hconj.congr'
    (Filter.Eventually.of_forall fun b => (heq b).symm)
  exact tendsto_nhds_unique hconj' hadv

/-- The canonical Bessel-J spectral-center UV value has the correct
retarded/advanced conjugation under the physical decomposition
`s = E²-M²`. This result uses the *proved* finite-integral
conjugation, not an independent Bessel-Y or Hankel postulate. -/
theorem massiveDiracRadialBesselJCenterUVValue_conj_of_energy_mass
    (v c : ℝ) (energy mass : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hcenter : (energy ^ 2 - mass ^ 2).im ≠ 0) :
    conj (massiveDiracRadialBesselJCenterUVValue
      v c (energy ^ 2 - mass ^ 2)) =
    massiveDiracRadialBesselJCenterUVValue
      v c (conj (energy ^ 2 - mass ^ 2)) := by
  calc
    conj (massiveDiracRadialBesselJCenterUVValue
      v c (energy ^ 2 - mass ^ 2)) =
        conj (massiveDiracRadialFourierUVValue v c energy mass) := by
      rw [massiveDiracRadialFourierUVValue_eq_besselJCenter]
    _ = massiveDiracRadialFourierUVValue
          v c (conj energy) (conj mass) :=
      massiveDiracRadialFourierUVValue_conj v c energy mass hv hc hcenter
    _ = massiveDiracRadialBesselJCenterUVValue
          v c ((conj energy) ^ 2 - (conj mass) ^ 2) :=
      massiveDiracRadialFourierUVValue_eq_besselJCenter
        v c (conj energy) (conj mass)
    _ = massiveDiracRadialBesselJCenterUVValue
          v c (conj (energy ^ 2 - mass ^ 2)) := by
      simp only [map_sub, map_pow]

end

end QuantumTheory.Models.MassiveDirac
