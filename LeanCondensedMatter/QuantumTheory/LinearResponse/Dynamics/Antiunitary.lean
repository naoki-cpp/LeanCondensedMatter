import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option linter.style.header false

/-!
# Antiunitary maps for bounded linear-response systems

An antiunitary map is Mathlib's conjugate-linear isometric equivalence.
Hamiltonian and current covariance remain separate model-specific hypotheses.
-/

namespace QuantumTheory.LinearResponse

/-- Antiunitaries are conjugate-linear isometric equivalences. -/
abbrev AntiunitaryMap (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H ≃ₗᵢ⋆[ℂ] H

namespace AntiunitaryMap

/-- An antiunitary conjugates inner products. -/
theorem inner_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (θ : AntiunitaryMap H) (x y : H) :
    inner ℂ (θ x) (θ y) = (starRingEnd ℂ) (inner ℂ x y) := by
  have hI (v : H) : θ (Complex.I • v) = -(Complex.I • θ v) := by
    calc
      θ (Complex.I • v) = ((starRingEnd ℂ) Complex.I) • θ v :=
        θ.map_smulₛₗ Complex.I v
      _ = -(Complex.I • θ v) := by
        rw [starRingEnd_apply, Complex.star_def, Complex.conj_I, neg_smul]
  apply Complex.ext
  · rw [starRingEnd_apply, Complex.star_def, Complex.conj_re]
    rw [← RCLike.re_eq_complex_re]
    rw [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
      re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four]
    simp only [← map_add, ← map_sub, θ.norm_map]
  · rw [starRingEnd_apply, Complex.star_def, Complex.conj_im]
    rw [← RCLike.im_eq_complex_im]
    rw [im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four,
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
    have hIeq : (RCLike.I : ℂ) = Complex.I := rfl
    rw [hIeq]
    have hsub : θ x - Complex.I • θ y = θ (x + Complex.I • y) := by
      rw [map_add, hI]
      abel
    have hadd : θ x + Complex.I • θ y = θ (x - Complex.I • y) := by
      rw [map_sub, hI]
      abel
    rw [hsub, hadd, θ.norm_map, θ.norm_map]
    ring

end AntiunitaryMap
end QuantumTheory.LinearResponse
