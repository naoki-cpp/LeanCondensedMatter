import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Injectivity of dissipative spectral shifts

A self-adjoint bounded operator with a dissipative self-energy has an injective
spectral shift whenever the imaginary part of the spectral parameter is nonzero.
This statement is independent of the dimension of the Hilbert space and of any
particular disorder model.
-/

namespace QuantumTheory

noncomputable section

/-- A self-adjoint Hamiltonian and a self-energy with the opposite signed
imaginary quadratic form cannot cancel a nonreal spectral shift. -/
theorem dissipativeSpectralShift_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hamiltonian selfEnergy : H →L[ℂ] H)
    (hself : IsSelfAdjoint hamiltonian)
    (z : ℂ) (hz : z.im ≠ 0)
    (hdiss : ∀ ψ : H, z.im * (inner ℂ ψ (selfEnergy ψ)).im ≤ 0) :
    Function.Injective
      (algebraMap ℂ (H →L[ℂ] H) z - hamiltonian - selfEnergy) := by
  let shift := algebraMap ℂ (H →L[ℂ] H) z - hamiltonian - selfEnergy
  intro ψ φ hψφ
  have hsub : shift (ψ - φ) = 0 := by
    rw [map_sub, hψφ, sub_self]
  have hzero : ψ - φ = 0 := by
    by_contra hne
    have hnorm : 0 < ‖ψ - φ‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hne)
    have hregSq : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
    have hSigma := hdiss (ψ - φ)
    have hshiftApply :
        z • (ψ - φ) - hamiltonian (ψ - φ) - selfEnergy (ψ - φ) = 0 := by
      simpa [shift, Algebra.algebraMap_eq_smul_one] using hsub
    have hH : (inner ℂ (ψ - φ) (hamiltonian (ψ - φ))).im = 0 := by
      exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself).im_inner_self_apply (ψ - φ)
    have himSelf : (inner ℂ (ψ - φ) (ψ - φ)).im = 0 :=
      inner_self_im (𝕜 := ℂ) (ψ - φ)
    have hreSelf : (inner ℂ (ψ - φ) (ψ - φ)).re = ‖ψ - φ‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) (ψ - φ)).symm
    have him := congrArg (fun w : H => (inner ℂ (ψ - φ) w).im) hshiftApply
    rw [inner_sub_right, inner_sub_right, inner_smul_right] at him
    simp only [Complex.sub_im, Complex.mul_im,
      himSelf, hreSelf, hH, mul_zero, zero_add, sub_zero] at him
    have himZero :
        z.im * ‖ψ - φ‖ ^ 2 -
          (inner ℂ (ψ - φ) (selfEnergy (ψ - φ))).im = 0 := by
      simpa using him
    have hbalance :
        z.im * ‖ψ - φ‖ ^ 2 =
          (inner ℂ (ψ - φ) (selfEnergy (ψ - φ))).im :=
      sub_eq_zero.mp himZero
    rw [← hbalance] at hSigma
    have hpositive : 0 < z.im ^ 2 * ‖ψ - φ‖ ^ 2 :=
      mul_pos hregSq hnorm
    have hrewrite : z.im * (z.im * ‖ψ - φ‖ ^ 2) =
        z.im ^ 2 * ‖ψ - φ‖ ^ 2 := by ring
    rw [hrewrite] at hSigma
    linarith
  exact sub_eq_zero.mp hzero

end

end QuantumTheory
