import LeanCondensedMatter.Analysis.Operator.AdjointConjugation
import LeanCondensedMatter.QuantumTheory.LinearResponse.Perturbation.Hermitian
import Mathlib.Analysis.Normed.Operator.Mul

set_option linter.style.header false

/-!
# Perturbed interaction-picture observables

The Dyson interaction-picture propagator defines the finite-coupling observable
`U_I† A_I U_I` and its continuous-linear-map realization. These definitions
belong to the perturbation layer, independently of any normalized expectation
or Kubo response formula.

Unitarity of the propagator is proved in `Perturbation.Unitary`, downstream
of these definitions. The Kubo first-variation formulas live separately in
`Response.KuboFormula`.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)

/-- The interaction-picture observable conjugated by the perturbed propagator. -/
noncomputable def timeDependentPerturbedObservable
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H)
    (lam t : ℝ) : H →L[ℂ] H :=
  ContinuousLinearMap.adjointConjugate
    (star (timeDependentInteractionPropagator U hbar V lam t))
    (heisenbergEvolution U t A)

/-- The continuous linear map sending an ordinary observable `A` to its perturbed
interaction-picture representative `U_I† A_I U_I`. -/
noncomputable def timeDependentPerturbedObservableMap
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  let W := timeDependentInteractionPropagator U hbar V lam t
  let U₀ : H →L[ℂ] H := U (Multiplicative.ofAdd t)
  let left := star W * star U₀
  let right := U₀ * W
  ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip right).comp
    ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)) left)

@[simp]
theorem timeDependentPerturbedObservableMap_apply
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H)
    (lam t : ℝ) :
    timeDependentPerturbedObservableMap U hbar V lam t A =
      timeDependentPerturbedObservable U hbar V A lam t := by
  simp [timeDependentPerturbedObservableMap, timeDependentPerturbedObservable,
    ContinuousLinearMap.adjointConjugate, heisenbergEvolution_apply, mul_assoc]

@[simp]
theorem timeDependentPerturbedObservable_zero_coupling
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H) (t : ℝ) :
    timeDependentPerturbedObservable U hbar V A 0 t =
      heisenbergEvolution U t A := by
  simp [timeDependentPerturbedObservable, ContinuousLinearMap.adjointConjugate]

end
end LinearResponse
end QuantumTheory
