import LeanCondensedMatter.QuantumTheory.DensityOperatorTraceClass
import LeanCondensedMatter.Analysis.Operator.TraceClass.Scalar
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.Exp

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Canonical Gibbs density operator via spectral trace (infinite dimensions)

The normalized Gibbs state `e^{-βH}/Z(β)` is constructed with explicit compactness and spectral
summability hypotheses on the unnormalized Gibbs operator.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unnormalized Gibbs operator `e^{-βH}`. -/
noncomputable def gibbsOp (Hop : Observable H) (β : ℝ) : H →L[ℂ] H :=
  cfc (fun x : ℝ => Real.exp (-β * x)) Hop.1

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
      ContinuousLinearMap.spectralTrace_nonneg hsummable (gibbsOp_isPositive Hop β).toLinearMap
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
