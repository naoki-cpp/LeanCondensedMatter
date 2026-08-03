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
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_sq_mul_of_bound
    (interactionPerturbation system B f) BoundedDyson.norm_one_le hM hV
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
  rw [hasDerivAt_iff_tendsto]
  let C : ℝ := ∑' n : ℕ, Dyson.majorant M t (n + 2)
  have hC : 0 ≤ C := by
    exact tsum_nonneg fun n => Dyson.majorant_nonneg hM ht.1 (n + 2)
  have habs : Tendsto (fun lam : ℝ => |lam|) (𝓝 0) (𝓝 0) := by
    simpa [Real.norm_eq_abs] using (continuous_norm.tendsto (0 : ℝ))
  have hsmall : ∀ᶠ lam : ℝ in 𝓝 0, |lam| / system.hbar ≤ 1 := by
    have hevent : ∀ᶠ lam : ℝ in 𝓝 0, |lam| < system.hbar :=
      habs (Iio_mem_nhds system.hbar_pos)
    filter_upwards [hevent] with lam hlam
    exact (div_le_one system.hbar_pos).2 hlam.le
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun lam =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · filter_upwards [hsmall] with lam hlam
    have hrem := norm_interactionPropagator_sub_firstOrder_le_sq_mul_of_bound
      system hM hV ht lam hlam
    have hrem' :
        ‖interactionPropagator system B f lam t -
            interactionPropagator system B f 0 t -
            lam • ((Complex.I / (system.hbar : ℂ)) •
              ∫ s in (0 : ℝ)..t, interactionPerturbation system B f s)‖ ≤
          (|lam| / system.hbar) ^ 2 * C := by
      simpa [C, interactionPropagator_zero_coupling, smul_smul, sub_eq_add_neg,
        add_assoc] using hrem
    by_cases hlam0 : lam = 0
    · subst lam
      simp
    · have habs0 : |lam| ≠ 0 := abs_ne_zero.mpr hlam0
      calc
        ‖lam - 0‖⁻¹ *
            ‖interactionPropagator system B f lam t -
              interactionPropagator system B f 0 t -
              (lam - 0) • ((Complex.I / (system.hbar : ℂ)) •
                ∫ s in (0 : ℝ)..t, interactionPerturbation system B f s)‖ ≤
            |lam|⁻¹ * ((|lam| / system.hbar) ^ 2 * C) := by
          simpa [Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left hrem' (inv_nonneg.mpr (abs_nonneg lam))
        _ = |lam| * (C / system.hbar ^ 2) := by
          field_simp [habs0, system.hbar_ne_zero]
          <;> ring
  · simpa using habs.mul_const (C / system.hbar ^ 2)

end
end LinearResponse
end QuantumTheory
