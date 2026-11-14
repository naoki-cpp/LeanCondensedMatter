import LeanCondensedMatter.QuantumTheory.LinearResponse.Perturbation.TimeDependent
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option linter.style.header false

/-!
# Finite-time transition amplitudes and their leading squared weight

The first physical Dyson variation gives the matrix element
  a₁(t) = ⟪final, K_V(t) initial⟫,  K_V(t) = -(i/ℏ) ∫₀ᵗ V_I(s) ds.
For orthogonal initial and final vectors, the exact squared amplitude divided by λ²
converges to ‖a₁(t)‖² as λ → 0 at fixed finite time.

The statements do not assume a band structure or impurity ensemble. For normalized
vectors and a unitary propagator this squared amplitude is a transition probability;
Hermitian-continuous perturbations supply unitarity in Perturbation.Unitary.
No long-time limit, continuous final-state density, delta distribution, or golden-rule
transition rate is inferred from this fixed-time weak-coupling result.
-/

namespace QuantumTheory.LinearResponse

open Filter Set
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)

/-- The matrix element of the first Dyson variation is the derivative of the exact
interaction-picture transition amplitude at zero physical coupling. -/
theorem hasDerivAt_timeDependentTransitionAmplitude_zero_of_bound
    (initial final : H) {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => inner ℂ final (timeDependentInteractionPropagator U hbar V lam t initial))
      (inner ℂ final (timeDependentPropagatorFirstVariation U hbar V t initial)) 0 := by
  let matrixElement : (H →L[ℂ] H) →L[ℂ] ℂ :=
    (innerSL ℂ final).comp (ContinuousLinearMap.apply ℂ H initial)
  exact (matrixElement.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_timeDependentInteractionPropagator_zero_of_bound U hbar hM hV ht)

/-- Orthogonality removes the zeroth-order amplitude. The leading transition weight is
quadratic in the physical coupling at each fixed time; it is a probability for normalized
vectors when the exact propagator is unitary. -/
theorem tendsto_timeDependentTransitionWeight_div_sq_zero_of_bound
    (initial final : H) (horthogonal : inner ℂ final initial = 0)
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    Tendsto
      (fun lam : ℝ =>
        ‖inner ℂ final (timeDependentInteractionPropagator U hbar V lam t initial)‖ ^ 2 /
          lam ^ 2)
      (𝓝[≠] 0)
      (𝓝 (‖inner ℂ final (timeDependentPropagatorFirstVariation U hbar V t initial)‖ ^ 2)) := by
  have hderiv := hasDerivAt_timeDependentTransitionAmplitude_zero_of_bound
    U hbar initial final hM hV ht
  have hzero :
      inner ℂ final (timeDependentInteractionPropagator U hbar V 0 t initial) = 0 := by
    simpa only [timeDependentInteractionPropagator_zero_coupling, one_apply_eq_self] using
      horthogonal
  have hslope := hderiv.tendsto_slope_zero
  simp only [zero_add, hzero, sub_zero] at hslope
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv, mul_pow, inv_pow, sq_abs,
    div_eq_mul_inv, mul_comm] using hslope.norm.pow 2

end
end QuantumTheory.LinearResponse