import LeanCondensedMatter.Analysis.Dyson.FirstVariation
import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option linter.style.header false

/-!
# General bounded time-dependent perturbations

This module treats a general bounded time-dependent perturbation

`H_λ(t) = H₀ + λ V(t)`

without assuming a separated source form such as `f(t) B`. Its interaction-picture representative is

`V_I(t) = U₀(-t) V(t) U₀(t)`.

The generic Dyson recursion uses `Dₙ₊₁(t) = -∫₀ᵗ V_I(s) Dₙ(s) ds`, so the physical scalar coupling
is `λ i / ℏ`. Consequently the first propagator variation is

`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`.

Source-coupled perturbations are downstream specializations obtained by choosing, for example,
`V(t) = -f(t) B`.
-/

namespace QuantumTheory
namespace LinearResponse

open Filter Set
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The interaction-picture form `V_I(t) = U₀(-t) V(t) U₀(t)` of a general time-dependent
bounded perturbation. -/
noncomputable def timeDependentInteractionPerturbation
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  heisenbergEvolution system (V t) t

/-- The generic Dyson scalar corresponding to `H_λ(t) = H₀ + λ V(t)`. -/
noncomputable def timeDependentPhysicalDysonCoupling (lam : ℝ) : ℂ :=
  (lam : ℂ) * (Complex.I / (system.hbar : ℂ))

/-- The norm of the physical scalar coupling is `|λ| / ℏ`. -/
theorem norm_timeDependentPhysicalDysonCoupling (lam : ℝ) :
    ‖timeDependentPhysicalDysonCoupling system lam‖ = |lam| / system.hbar := by
  simp [timeDependentPhysicalDysonCoupling, abs_of_pos system.hbar_pos, div_eq_mul_inv]

/-- The interaction-picture propagator for the general perturbation `H₀ + λ V(t)`. -/
noncomputable def timeDependentInteractionPropagator
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) : H →L[ℂ] H :=
  Dyson.evolution (timeDependentInteractionPerturbation system V)
    (timeDependentPhysicalDysonCoupling system lam) t

/-- The first propagator variation
`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`. -/
noncomputable def timeDependentPropagatorFirstVariation
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  (-(Complex.I / (system.hbar : ℂ))) •
    ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s

omit [CompleteSpace H] in
/-- A generic Dyson evolution is the identity at zero scalar coupling. -/
theorem timeDependentDysonEvolution_zero_coupling
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) :
    Dyson.evolution V 0 t = 1 := by
  rw [Dyson.evolution, tsum_eq_single 0]
  · simp [Dyson.term]
  · intro n hn
    simp [Dyson.term, hn]

@[simp]
theorem timeDependentInteractionPropagator_zero_coupling
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) :
    timeDependentInteractionPropagator system V 0 t = 1 := by
  simp [timeDependentInteractionPropagator, timeDependentPhysicalDysonCoupling,
    timeDependentDysonEvolution_zero_coupling]

omit [CompleteSpace H] in
/-- The first generic Dyson coefficient is the negative integral of the interaction. -/
theorem timeDependentDysonCoeff_one (V : ℝ → (H →L[ℂ] H)) (t : ℝ) :
    Dyson.coeff V 1 t = -∫ s in (0 : ℝ)..t, V s := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, Dyson.coeff_succ]
  simp

/-- The exact first weighted Dyson term for `H₀ + λ V(t)`. -/
theorem timeDependentDysonTerm_one
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) :
    Dyson.term (timeDependentInteractionPerturbation system V)
        (timeDependentPhysicalDysonCoupling system lam) t 1 =
      ((lam : ℂ) * (-(Complex.I / (system.hbar : ℂ)))) •
        ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s := by
  simp [Dyson.term, timeDependentPhysicalDysonCoupling, timeDependentDysonCoeff_one]

/-- After subtracting the identity and exact first term, the propagator remainder starts at order
`λ²`. -/
theorem norm_timeDependentInteractionPropagator_sub_firstOrder_le_of_bound
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ) :
    ‖timeDependentInteractionPropagator system V lam t -
        (1 + ((lam : ℂ) * (-(Complex.I / (system.hbar : ℂ)))) •
          ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s)‖ ≤
      ∑' n : ℕ, Dyson.majorant ((|lam| / system.hbar) * M) t (n + 2) := by
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_of_bound
    (timeDependentInteractionPerturbation system V) BoundedDyson.norm_one_le hM hV
    (timeDependentPhysicalDysonCoupling system lam) ht
  simpa only [timeDependentInteractionPropagator, timeDependentDysonTerm_one,
    norm_timeDependentPhysicalDysonCoupling] using h

/-- On `|λ| / ℏ ≤ 1`, the general time-dependent propagator remainder has an explicit quadratic
bound. -/
theorem norm_timeDependentInteractionPropagator_sub_firstOrder_le_sq_mul_of_bound
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ)
    (hlam : |lam| / system.hbar ≤ 1) :
    ‖timeDependentInteractionPropagator system V lam t -
        (1 + ((lam : ℂ) * (-(Complex.I / (system.hbar : ℂ)))) •
          ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s)‖ ≤
      (|lam| / system.hbar) ^ 2 *
        ∑' n : ℕ, Dyson.majorant M t (n + 2) := by
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_sq_mul_of_bound
    (timeDependentInteractionPerturbation system V) BoundedDyson.norm_one_le hM hV
    (timeDependentPhysicalDysonCoupling system lam)
    (by simpa [norm_timeDependentPhysicalDysonCoupling] using hlam) ht
  simpa only [timeDependentInteractionPropagator, timeDependentDysonTerm_one,
    norm_timeDependentPhysicalDysonCoupling] using h

/-- The general interaction-picture propagator is differentiable at zero physical coupling. -/
theorem hasDerivAt_timeDependentInteractionPropagator_zero_of_bound
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => timeDependentInteractionPropagator system V lam t)
      (timeDependentPropagatorFirstVariation system V t)
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
  refine squeeze_zero'
    (g := fun lam : ℝ => |lam| * (C / system.hbar ^ 2)) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun lam =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · filter_upwards [hsmall] with lam hlam
    have hrem := norm_timeDependentInteractionPropagator_sub_firstOrder_le_sq_mul_of_bound
      system hM hV ht lam hlam
    have hlin :
        lam • timeDependentPropagatorFirstVariation system V t =
          ((lam : ℂ) * (-(Complex.I / (system.hbar : ℂ)))) •
            ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s := by
      rw [timeDependentPropagatorFirstVariation, ← smul_smul]
      rfl
    have hrem' :
        ‖timeDependentInteractionPropagator system V lam t -
            timeDependentInteractionPropagator system V 0 t -
            lam • timeDependentPropagatorFirstVariation system V t‖ ≤
          (|lam| / system.hbar) ^ 2 * C := by
      rw [hlin]
      simpa [C, timeDependentInteractionPropagator_zero_coupling,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrem
    by_cases hlam0 : lam = 0
    · subst lam
      simp
    · have habs0 : |lam| ≠ 0 := abs_ne_zero.mpr hlam0
      calc
        ‖lam - 0‖⁻¹ *
            ‖timeDependentInteractionPropagator system V lam t -
              timeDependentInteractionPropagator system V 0 t -
              (lam - 0) • timeDependentPropagatorFirstVariation system V t‖ ≤
            |lam|⁻¹ * ((|lam| / system.hbar) ^ 2 * C) := by
          simpa [Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left hrem' (inv_nonneg.mpr (abs_nonneg lam))
        _ = |lam| * (C / system.hbar ^ 2) := by
          field_simp [habs0, system.hbar_ne_zero]
  · simpa using habs.mul_const (C / system.hbar ^ 2)

end
end LinearResponse
end QuantumTheory
