import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lorentzian spectral kernel

This module owns the model-independent scalar Lorentzian kernel that appears in retarded-minus-
advanced resolvent differences,

```text
L_η(x) = η / (η² + x²).
```

It proves the elementary scalar resolvent identity, exact finite-interval integrals, symmetric-window
mass formula, and convergence of every fixed positive symmetric-window mass to `π` as
`η → 0⁺`.

No Hamiltonian, band structure, current operator, occupation function, conductivity normalization,
or concrete transport model appears here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open Filter

/-- Real Lorentzian kernel carrying the scalar retarded-minus-advanced spectral weight. -/
def lorentzianSpectralKernel (offset broadening : ℝ) : ℝ :=
  broadening / (broadening ^ 2 + offset ^ 2)

private theorem complex_offset_add_I_ne_zero
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (offset : ℂ) + (broadening : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have him : broadening = 0 := by
    simpa using congrArg Complex.im hzero
  exact hbroadening him

private theorem complex_offset_sub_I_ne_zero
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (offset : ℂ) - (broadening : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have him : broadening = 0 := by
    simpa using congrArg Complex.im hzero
  exact hbroadening him

/-- Elementary retarded-minus-advanced scalar resolvent identity. -/
theorem inv_add_I_sub_inv_sub_I_eq_lorentzian
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    ((offset : ℂ) + (broadening : ℂ) * Complex.I)⁻¹ -
        ((offset : ℂ) - (broadening : ℂ) * Complex.I)⁻¹ =
      (-2 * Complex.I) * (lorentzianSpectralKernel offset broadening : ℂ) := by
  have hplus := complex_offset_add_I_ne_zero offset broadening hbroadening
  have hminus := complex_offset_sub_I_ne_zero offset broadening hbroadening
  have hsumReal : broadening ^ 2 + offset ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hbroadening]
  have hsumPow : (broadening : ℂ) ^ 2 + (offset : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hsumReal
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = (-1 : ℂ) * Complex.I := by rw [hI]
      _ = -Complex.I := by ring
  unfold lorentzianSpectralKernel
  push_cast
  field_simp [hplus, hminus, hsumPow]
  ring_nf
  rw [hI3]
  ring

/-- Exact finite-interval mass of the Lorentzian kernel. -/
theorem integral_lorentzianSpectralKernel
    (lower upper broadening : ℝ) :
    (∫ offset in lower..upper, lorentzianSpectralKernel offset broadening) =
      Real.arctan (upper / broadening) - Real.arctan (lower / broadening) := by
  simpa [lorentzianSpectralKernel, add_comm] using
    (integral_div_sq_add_sq (a := lower) (b := upper) (c := broadening))

/-- On a symmetric interval the Lorentzian mass is `2 arctan(radius / η)`. -/
theorem integral_lorentzianSpectralKernel_symmetric
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening) =
      2 * Real.arctan (radius / broadening) := by
  rw [integral_lorentzianSpectralKernel]
  rw [show (-radius) / broadening = -(radius / broadening) by ring]
  rw [Real.arctan_neg]
  ring

/-- Every fixed positive symmetric neighborhood captures asymptotic Lorentzian mass `π` as the
broadening tends to zero from the positive side. -/
theorem tendsto_integral_lorentzianSpectralKernel_symmetric
    (radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) := by
  have hinv : Tendsto (fun broadening : ℝ => broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hscaled : Tendsto (fun broadening : ℝ => radius * broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => radius)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds radius)).pos_mul_atTop hradius hinv
  have harctanWithin := Real.tendsto_arctan_atTop.comp hscaled
  have harctan : Tendsto
      (fun broadening : ℝ => Real.arctan (radius / broadening))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    have h := tendsto_nhds_of_tendsto_nhdsWithin harctanWithin
    change Tendsto
      (fun broadening : ℝ => Real.arctan (radius * broadening⁻¹))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) at h
    simpa only [div_eq_mul_inv] using h
  have hmass := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2)).mul harctan
  have hfun :
      (fun broadening : ℝ =>
        ∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening) =
      (fun broadening : ℝ => 2 * Real.arctan (radius / broadening)) := by
    funext broadening
    exact integral_lorentzianSpectralKernel_symmetric radius broadening
  have hpi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by
    ring
  rw [hfun]
  rw [hpi] at hmass
  exact hmass

end

end Transport
end QuantumTheory
