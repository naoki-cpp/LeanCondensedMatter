import LeanCondensedMatter.QuantumTheory.DensityOperatorTraceClass
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
# Canonical Gibbs density operator via spectral trace (infinite dimensions)

The normalized Gibbs state `e^{-βH}/Z(β)` is constructed with explicit compactness and spectral
summability hypotheses on the unnormalized Gibbs operator.

**Bounded-Hamiltonian limitation.** `QuantumTheory.Observable H` models a Hamiltonian as a bounded
self-adjoint operator. For bounded `Hop`, the continuous-functional-calculus operator
`exp (-β Hop)` is invertible, with inverse `exp (β Hop)`. Consequently, if `gibbsOp Hop β` is
also compact, then the identity is compact and `H` is finite-dimensional; this is formalized by
`finiteDimensional_of_gibbsOp_isCompact` below. Thus the construction below is
dimension-independent as an API, but its compactness hypothesis does not describe a genuinely
infinite-dimensional Gibbs state while Hamiltonians remain bounded. Such states require a later
theory of unbounded self-adjoint Hamiltonians.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unnormalized Gibbs operator `e^{-βH}`. -/
noncomputable def gibbsOp (Hop : Observable H) (β : ℝ) : H →L[ℂ] H :=
  cfc (fun x : ℝ => Real.exp (-β * x)) Hop.1

/-- The Gibbs operator acts on an energy eigenvector by the corresponding Boltzmann factor. -/
theorem gibbsOp_apply_eigenvector (Hop : Observable H) (β : ℝ) {v : H} {E : ℝ}
    (hv : (Hop.1 : H →ₗ[ℂ] H) v = (E : ℂ) • v) :
    gibbsOp Hop β v = (Real.exp (-β * E) : ℂ) • v := by
  simpa [gibbsOp] using
    (cfc_apply_eigenvector (T := Hop.1) Hop.2 hv
      (f := fun x : ℝ => Real.exp (-β * x)) (by fun_prop))

/-- For the repository's bounded notion of Hamiltonian, compactness of the Gibbs operator forces
the Hilbert space to be finite-dimensional. The Gibbs operator is a unit by `cfcUnits`; composing
its inverse with the assumed compact operator makes the identity compact. -/
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
  have hinv_comp :
      (⇑(↑u⁻¹ : H →L[ℂ] H) ∘ ⇑(u : H →L[ℂ] H)) = id := by
    funext x
    have h := congrArg (fun T : H →L[ℂ] H => T x) u.inv_val
    simpa using h
  have hcompact_id : IsCompactOperator (id : H → H) := by
    rw [← hinv_comp]
    exact hcompact_u.clm_comp (↑u⁻¹ : H →L[ℂ] H)
  exact FiniteDimensional.of_isCompactOperator_id hcompact_id

/-- `gibbsOp` is positive. -/
theorem gibbsOp_isPositive (Hop : Observable H) (β : ℝ) : (gibbsOp Hop β).IsPositive := by
  rw [gibbsOp, ← nonneg_iff_isPositive]
  exact cfc_nonneg (fun x _ => (Real.exp_pos _).le)

/-- The normalized Gibbs density operator. -/
noncomputable def gibbsState (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : ContinuousLinearMap.HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : ContinuousLinearMap.spectralTrace hsummable ≠ 0) : DensityOperator H := by
  let Z : ℝ := ContinuousLinearMap.spectralTrace hsummable
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
      ContinuousLinearMap.trace_nonneg hsummable (gibbsOp_isPositive Hop β).toLinearMap
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hZnonneg)
  have hsummableScaled :
      ContinuousLinearMap.HasSummableRealEigenvalues (r • gibbsOp Hop β) :=
    ContinuousLinearMap.hasSummableRealEigenvalues_smul hrne hsummable
  exact {
    op := r • gibbsOp Hop β
    pos := hpos
    spectralTraceClass := ContinuousLinearMap.SpectralTraceClass.ofPositive
      (hcompact.smul _) hpos hsummableScaled
    spectralTrace_eq_one := by
      change ContinuousLinearMap.spectralTrace hsummableScaled = 1
      rw [ContinuousLinearMap.spectralTrace_smul hrne hsummable hsummableScaled]
      dsimp [r, Z]
      exact inv_mul_cancel₀ hZ
  }

end QuantumTheory.TraceClass
