import LeanCondensedMatter.QuantumTheory.DensityOperator.Normalize
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Gibbs density states

For bounded Hamiltonians, compactness of the unnormalized Gibbs operator already forces finite
dimension, so spectral summability is derived rather than supplied independently.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unnormalized Gibbs operator `e^{-βH}`. -/
noncomputable def gibbsOp (Hop : Observable H) (β : ℝ) : H →L[ℂ] H :=
  cfc (fun x : ℝ => Real.exp (-β * x)) Hop.1

private noncomputable def gibbsOpUnit (Hop : Observable H) (β : ℝ) : (H →L[ℂ] H)ˣ :=
  cfcUnits (fun x : ℝ => Real.exp (-β * x)) Hop.1
    (fun x _ => (Real.exp_pos _).ne') (hf := by fun_prop) (ha := Hop.2)

private theorem coe_gibbsOpUnit (Hop : Observable H) (β : ℝ) :
    (gibbsOpUnit Hop β : H →L[ℂ] H) = gibbsOp Hop β := by
  rfl

/-- The Gibbs operator acts on an energy eigenvector by the Boltzmann factor. -/
theorem gibbsOp_apply_eigenvector (Hop : Observable H) (β : ℝ) {v : H} {E : ℝ}
    (hv : (Hop.1 : H →ₗ[ℂ] H) v = (E : ℂ) • v) :
    gibbsOp Hop β v = (Real.exp (-β * E) : ℂ) • v := by
  simpa [gibbsOp] using
    (cfc_apply_eigenvector (T := Hop.1) Hop.2 hv
      (f := fun x : ℝ => Real.exp (-β * x)) (by fun_prop))

/-- For bounded Hamiltonians, compactness of the Gibbs operator forces finite dimension. -/
theorem finiteDimensional_of_gibbsOp_isCompact (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β)) : FiniteDimensional ℂ H := by
  let u := gibbsOpUnit Hop β
  have hcompact_u : IsCompactOperator (u : H →L[ℂ] H) := by
    simpa [u, coe_gibbsOpUnit] using hcompact
  have hcompact_one : IsCompactOperator (1 : H →L[ℂ] H) := by
    have hcompact_inv_mul :
        IsCompactOperator ((↑u⁻¹ : H →L[ℂ] H) * (u : H →L[ℂ] H)) := by
      change IsCompactOperator (⇑(↑u⁻¹ : H →L[ℂ] H) ∘ ⇑(u : H →L[ℂ] H))
      exact hcompact_u.clm_comp (↑u⁻¹ : H →L[ℂ] H)
    exact u.inv_val ▸ hcompact_inv_mul
  have hone : (⇑(1 : H →L[ℂ] H)) = (id : H → H) := by
    rfl
  apply FiniteDimensional.of_isCompactOperator_id
  rw [← hone]
  exact hcompact_one

/-- `gibbsOp` is positive. -/
theorem gibbsOp_isPositive (Hop : Observable H) (β : ℝ) : (gibbsOp Hop β).IsPositive := by
  rw [gibbsOp, ← nonneg_iff_isPositive]
  exact cfc_nonneg (fun x _ => (Real.exp_pos _).le)

/-- On a nontrivial Hilbert space, the Gibbs operator is nonzero because it is invertible. -/
theorem gibbsOp_ne_zero [Nontrivial H] (Hop : Observable H) (β : ℝ) :
    gibbsOp Hop β ≠ 0 := by
  rw [← coe_gibbsOpUnit]
  exact Units.ne_zero _

/-- A compact Gibbs operator has summable nonzero real eigenvalues automatically. -/
private theorem gibbsOp_hasSummableRealEigenvalues_of_isCompact (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β)) :
    HasSummableRealEigenvalues (gibbsOp Hop β) := by
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  letI : Finite (EigenvectorIndex (gibbsOp Hop β)) :=
    (orthonormal_eigenvectorFamily hcompact
      (gibbsOp_isPositive Hop β).isSelfAdjoint.isSymmetric).linearIndependent.finite
  exact Summable.of_finite

/-- A compact Gibbs operator carries the canonical positive spectral-trace-class data. -/
theorem gibbsOp_spectralTraceClass (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β)) :
    SpectralTraceClass (gibbsOp Hop β) :=
  SpectralTraceClass.ofPositive hcompact (gibbsOp_isPositive Hop β)
    (gibbsOp_hasSummableRealEigenvalues_of_isCompact Hop β hcompact)

/-- The normalized Gibbs density operator. -/
noncomputable def gibbsState [Nontrivial H] (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β)) : DensityOperator H :=
  DensityOperator.normalizePositive
    (gibbsOp Hop β) (gibbsOp_isPositive Hop β)
    (gibbsOp_spectralTraceClass Hop β hcompact) (gibbsOp_ne_zero Hop β)

@[simp]
theorem gibbsState_op [Nontrivial H] (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β)) :
    (gibbsState Hop β hcompact).op =
      (spectralTrace (gibbsOp Hop β))⁻¹ • gibbsOp Hop β := by
  rw [gibbsState, DensityOperator.normalizePositive_op]
  rw [(gibbsOp_spectralTraceClass Hop β hcompact).trace_eq_spectralTrace]

end QuantumTheory
