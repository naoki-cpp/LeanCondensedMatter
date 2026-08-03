import LeanCondensedMatter.Analysis.Dyson.FirstVariation
import LeanCondensedMatter.QuantumTheory.LinearResponse.InteractionPicture

set_option linter.style.header false

/-!
# First-variation control for bounded linear response

This module specializes the generic second-order Dyson remainder estimate to the physical coupling
convention

`H_λ(t) = H₀ - λ f(t) B`.

The generic Dyson parameter is `-λ i / ℏ`, whose norm is `|λ| / ℏ`. Consequently the part of the
interaction-picture propagator beyond its constant and linear terms is controlled by a majorant
starting at order two. This is the quantitative input for differentiability at zero coupling.
-/

namespace QuantumTheory
namespace LinearResponse

open Set

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
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_of_bound
    (interactionPerturbation system B f) BoundedDyson.norm_one_le hM hV
    (physicalDysonCoupling system lam) ht
  simpa only [interactionPropagator, interactionDysonTerm_one,
    norm_physicalDysonCoupling] using h

end
end LinearResponse
end QuantumTheory
