import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Free
import Mathlib.Algebra.Star.BigOperators

set_option linter.style.header false

/-!
# Exact finite disorder ensembles

This module introduces the finite probabilistic layer used before any weak-disorder or
thermodynamic-limit approximation. A finite ensemble consists of a clean bounded Hamiltonian,
a self-adjoint impurity potential for each configuration, and a normalized nonnegative weight.

For every configuration the exact Hamiltonian is `Hω = H₀ + Vω`. Scalar and operator-valued
ensemble averages are finite weighted sums kept outside the configuration-wise response.

No Gaussian law, independence assumption, Born approximation, disorder expansion, trace per unit
volume, or infinite-volume limit is introduced here.
-/

namespace QuantumTheory
namespace Transport

open scoped BigOperators
open LinearResponse

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

/-- Exact finite disorder data on a bounded Hilbert-space Hamiltonian. -/
structure FiniteDisorderEnsemble where
  /-- Clean bounded self-adjoint Hamiltonian. -/
  baseHamiltonian : Observable H
  /-- Bounded self-adjoint impurity potential in each finite configuration. -/
  impurityPotential : Ω → Observable H
  /-- Probability weight of each configuration. -/
  probability : Ω → ℝ
  probability_nonneg : ∀ ω, 0 ≤ probability ω
  probability_sum : ∑ ω, probability ω = 1

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Exact configuration Hamiltonian `Hω = H₀ + Vω`. -/
noncomputable def configurationHamiltonian (ω : Ω) : Observable H :=
  ⟨ensemble.baseHamiltonian.1 + (ensemble.impurityPotential ω).1, by
    exact ensemble.baseHamiltonian.2.add (ensemble.impurityPotential ω).2⟩

/-- Configuration-wise bounded free system with a common positive reduced Planck constant. -/
noncomputable def configurationSystem
    (hbar : ℝ) (hbar_pos : 0 < hbar) (ω : Ω) : BoundedFreeSystem H where
  hamiltonian := ensemble.configurationHamiltonian ω
  hbar := hbar
  hbar_pos := hbar_pos

/-- Exact normalized finite disorder averaging for any complex module. -/
noncomputable def average {E : Type*} [AddCommMonoid E] [Module ℂ E] :
    (Ω → E) →ₗ[ℂ] E where
  toFun response := ∑ ω, (ensemble.probability ω : ℂ) • response ω
  map_add' left right := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' c response := by simp [Finset.smul_sum, smul_smul, mul_comm]

/-- Every complex-linear map commutes with finite disorder averaging. -/
theorem map_average {E F : Type*}
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid F] [Module ℂ F]
    (f : E →ₗ[ℂ] F) (response : Ω → E) :
    f (ensemble.average response) = ensemble.average (fun ω => f (response ω)) := by
  change f (∑ ω, (ensemble.probability ω : ℂ) • response ω) =
    ∑ ω, (ensemble.probability ω : ℂ) • f (response ω)
  simp only [map_sum, map_smul]

/-- Normalization makes the finite disorder average fix constant families. -/
@[simp]
theorem average_const {E : Type*} [AddCommMonoid E] [Module ℂ E] (value : E) :
    ensemble.average (fun _ => value) = value := by
  change (∑ ω, (ensemble.probability ω : ℂ) • value) = value
  rw [← Finset.sum_smul]
  have hsum : (∑ ω, (ensemble.probability ω : ℂ)) = 1 := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) ensemble.probability_sum
  simp [hsum]

/-- A normalized finite disorder average is norm-contractive on pointwise bounded families.
The same estimate applies to operator and scalar responses without introducing a second
probability-averaging API. -/
theorem norm_average_le_of_forall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (response : Ω → E) (bound : ℝ) (hbound : 0 ≤ bound)
    (hpoint : ∀ ω, ‖response ω‖ ≤ bound) :
    ‖ensemble.average response‖ ≤ bound := by
  calc
    ‖ensemble.average response‖ =
        ‖∑ ω, (ensemble.probability ω : ℂ) • response ω‖ := rfl
    _ ≤ ∑ ω, ‖(ensemble.probability ω : ℂ) • response ω‖ :=
      norm_sum_le _ _
    _ = ∑ ω, ensemble.probability ω * ‖response ω‖ := by
      apply Finset.sum_congr rfl
      intro ω _
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ensemble.probability_nonneg ω)]
    _ ≤ ∑ ω, ensemble.probability ω * bound := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hpoint ω) (ensemble.probability_nonneg ω)
    _ = bound := by
      rw [← Finset.sum_mul, ensemble.probability_sum, one_mul]

/-- Finite operator averaging commutes with adjunction because ensemble weights are real. -/
theorem average_star (operator : Ω → H →L[ℂ] H) :
    ensemble.average (fun ω => star (operator ω)) = star (ensemble.average operator) := by
  change (∑ ω, (ensemble.probability ω : ℂ) • star (operator ω)) =
    star (∑ ω, (ensemble.probability ω : ℂ) • operator ω)
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro ω _
  simp

end FiniteDisorderEnsemble

end

end Transport
end QuantumTheory
