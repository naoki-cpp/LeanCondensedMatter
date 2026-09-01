import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics
import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import Mathlib.Algebra.Star.BigOperators

set_option linter.style.header false

/-!
# Exact finite disorder ensembles

This module introduces the finite probabilistic layer used before any weak-disorder or
thermodynamic-limit approximation. A finite ensemble consists of a clean bounded Hamiltonian,
a self-adjoint impurity potential for each configuration, and a normalized nonnegative weight.

For every configuration the exact Hamiltonian is `Hω = H₀ + Vω`. Scalar and operator-valued
ensemble averages are finite weighted sums kept outside the configuration-wise response. In finite
dimension, the scalar average of an ordinary operator trace is proved equal to the trace of the
exact operator average.

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

/-- Exact finite disorder average of a complex configuration observable. -/
noncomputable def average (response : Ω → ℂ) : ℂ :=
  ∑ ω, (ensemble.probability ω : ℂ) * response ω

/-- Pointwise-equal configuration observables have the same finite disorder average. -/
theorem average_congr {left right : Ω → ℂ} (h : ∀ ω, left ω = right ω) :
    ensemble.average left = ensemble.average right := by
  unfold average
  apply Finset.sum_congr rfl
  intro ω _
  rw [h ω]

/-- Exact weighted finite average of an operator-valued configuration observable. -/
noncomputable def operatorAverage
    (operator : Ω → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ ω, (ensemble.probability ω : ℂ) • operator ω

/-- Exact finite operator averaging commutes with adjunction because every ensemble weight is real. -/
theorem operatorAverage_star
    (operator : Ω → H →L[ℂ] H) :
    ensemble.operatorAverage (fun ω => star (operator ω)) =
      star (ensemble.operatorAverage operator) := by
  unfold operatorAverage
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro ω _
  simp

/-- Finite disorder averaging commutes with the ordinary finite-dimensional operator trace. -/
theorem average_finiteDimensionalOperatorTrace
    [FiniteDimensional ℂ H]
    (operator : Ω → H →L[ℂ] H) :
    ensemble.average
        (fun ω => finiteDimensionalOperatorTrace (H := H) (operator ω)) =
      finiteDimensionalOperatorTrace (H := H) (ensemble.operatorAverage operator) := by
  unfold average operatorAverage
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [map_smul]
  rfl

end FiniteDisorderEnsemble

end

end Transport
end QuantumTheory
