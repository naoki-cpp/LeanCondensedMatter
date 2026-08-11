import LeanCondensedMatter.Analysis.Dyson.FirstVariation
import LeanCondensedMatter.QuantumTheory.LinearResponse.InteractionPicture
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option linter.style.header false

/-!
# First-variation control for bounded linear response

This module specializes the generic second-order Dyson remainder estimate to the physical coupling
convention

`H_λ(t) = H₀ - λ f(t) B`.

The generic Dyson parameter is `-λ i / ℏ`, whose norm is `|λ| / ℏ`. Consequently the part of the
interaction-picture propagator beyond its constant and linear terms is controlled by a majorant
starting at order two. The quadratic estimate proves differentiability at zero coupling, with the
first variation `+(i/ℏ) ∫ V_I` dictated by the Hamiltonian sign convention.
-/

namespace QuantumTheory
namespace LinearResponse

open Filter Set
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The norm of the generic Dyson parameter induced by the real physical coupling. -/
theorem norm_physicalDysonCoupling (lam : ℝ) :
    ‖physicalDysonCoupling system lam‖ = |lam| / system.hbar := by
  simp [physicalDysonCoupling, abs_of_pos system.hbar_pos, div_eq_mul_inv]

/-- The interaction-picture propagator differs from its constant and linear Dyson terms by a
series beginning at quadratic order in the physical coupling. -/
theorem norm_interactionPropagator_sub_firstOrder_le_of_bound
    {B : H →L[ℂ] H} {f : ℝ → ℝ}
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β, ‖interactionPerturbation system B f s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ) :
    ‖interactionPropagator system B f lam t -
        (1 + ((lam : ℂ) * (Complex.I / (system.hbar : ℂ))) •
          ∫ s in (0 : ℝ)..t, interactionPerturbation system B f s)‖ ≤
      ∑' n : ℕ, Dyson.majorant ((|lam| / system.hbar) * M) t (n + 2) := by
  have hOne : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_of_bound
    (interactionPerturbation system B f) hOne hM hV
    (physicalDysonCoupling system lam) ht
  simpa only [interactionPropagator, interactionDysonTerm_one,
    norm_physicalDysonCoupling] using h

/-- On the physical unit-coupling neighborhood `|λ| / ℏ ≤ 1`, the propagator remainder is bounded
by an explicit constant times `(|λ| / ℏ)²`. -/
theorem norm_interactionPropagator_sub_firstOrder_le_sq_mul_of_bound
    {B : H →L[ℂ] H} {f : ℝ → ℝ}
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β, ‖interactionPerturbation system B f s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ)
    (hlam : |lam| / system.hbar ≤ 1) :
    ‖interactionPropagator system B f lam t -
        (1 + ((lam : ℂ) * (Complex.I / (system.hbar : ℂ))) •
          ∫ s in (0 : ℝ)..t, interactionPerturbation system B f s)‖ ≤
      (|lam| / system.hbar) ^ 2 *
        ∑' n : ℕ, Dyson.majorant M t (n + 2) := by
  have hOne : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_sq_mul_of_bound
    (interactionPerturbation system B f) hOne hM hV
    (physicalDysonCoupling system lam) (by simpa [norm_physicalDysonCoupling] using hlam) ht
  simpa only [interactionPropagator, interactionDysonTerm_one,
    norm_physicalDysonCoupling] using h

/-- The interaction-picture propagator is differentiable at zero physical coupling. Its derivative
is the first Dyson variation `+(i/ℏ) ∫₀ᵗ V_I(s) ds`, with the sign derived from
`H_λ(t) = H₀ - λ f(t) B`. -/
theorem hasDerivAt_interactionPropagator_zero_of_bound
    {B : H →L[ℂ] H} {f : ℝ → ℝ}
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β, ‖interactionPerturbation system B f s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => interactionPropagator system B f lam t)
      ((Complex.I / (system.hbar : ℂ)) •
        ∫ s in (0 : ℝ)..t, interactionPerturbation system B f s)
      0 := by
  have hOne : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  simpa [interactionPropagator, physicalDysonCoupling] using
    Dyson.hasDerivAt_evolution_linear_coupling_zero_of_bound
      (interactionPerturbation system B f) hOne hM hV ht
      (-(Complex.I / (system.hbar : ℂ)))

end
end LinearResponse
end QuantumTheory
