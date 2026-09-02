import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import LeanCondensedMatter.Analysis.Operator.TraceClass.Scalar
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
  let u : (H →L[ℂ] H)ˣ :=
    cfcUnits (fun x : ℝ => Real.exp (-β * x)) Hop.1
      (fun x _ => (Real.exp_pos _).ne') (hf := by fun_prop) (ha := Hop.2)
  have hu : (u : H →L[ℂ] H) = gibbsOp Hop β := by
    rfl
  have hcompact_u : IsCompactOperator (u : H →L[ℂ] H) := by
    rw [hu]
    exact hcompact
  have hcompact_inv_mul :
      IsCompactOperator ((↑u⁻¹ : H →L[ℂ] H) * (u : H →L[ℂ] H)) := by
    change IsCompactOperator (⇑(↑u⁻¹ : H →L[ℂ] H) ∘ ⇑(u : H →L[ℂ] H))
    exact hcompact_u.clm_comp (↑u⁻¹ : H →L[ℂ] H)
  have hcompact_one : IsCompactOperator (1 : H →L[ℂ] H) := by
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

/-- A compact Gibbs operator has summable nonzero real eigenvalues automatically. -/
theorem gibbsOp_hasSummableRealEigenvalues_of_isCompact (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β)) :
    HasSummableRealEigenvalues (gibbsOp Hop β) := by
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  letI : Finite (EigenvectorIndex (gibbsOp Hop β)) :=
    (orthonormal_eigenvectorFamily hcompact
      (gibbsOp_isPositive Hop β).isSelfAdjoint.isSymmetric).linearIndependent.finite
  exact Summable.of_finite

/-- The normalized Gibbs density operator. -/
noncomputable def gibbsState (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) : DensityOperator H := by
  let hsummable : HasSummableRealEigenvalues (gibbsOp Hop β) :=
    gibbsOp_hasSummableRealEigenvalues_of_isCompact Hop β hcompact
  let Z : ℝ := spectralTrace (gibbsOp Hop β)
  let r : ℝ := Z⁻¹
  have hrne : r ≠ 0 := by
    dsimp [r, Z]
    exact inv_ne_zero hZ
  have hpos : (r • gibbsOp Hop β).IsPositive := by
    rw [show r • gibbsOp Hop β = (r : ℂ) • gibbsOp Hop β by
      ext x
      simp]
    refine (gibbsOp_isPositive Hop β).smul_of_nonneg ?_
    have hZnonneg : 0 ≤ Z :=
      trace_nonneg (gibbsOp_isPositive Hop β).toLinearMap
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hZnonneg)
  have hsummableScaled :
      HasSummableRealEigenvalues (r • gibbsOp Hop β) :=
    hasSummableRealEigenvalues_smul hrne hsummable
  let htraceClass : SpectralTraceClass (r • gibbsOp Hop β) :=
    SpectralTraceClass.ofPositive (hcompact.smul _) hpos hsummableScaled
  exact {
    op := r • gibbsOp Hop β
    pos := hpos
    spectralTraceClass := htraceClass
    spectralTrace_eq_one := by
      rw [htraceClass.trace_eq_spectralTrace]
      rw [spectralTrace_smul hrne hsummable hsummableScaled]
      dsimp [r, Z]
      exact inv_mul_cancel₀ hZ
  }

end QuantumTheory
