module

import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Normed.Module.FiniteDimension

public section

set_option linter.style.header false

/-!
# Ordinary finite-dimensional operator trace

This module owns general ordinary finite-dimensional trace infrastructure for bounded endomorphisms.
The trace is bundled as a continuous complex-linear functional, with reusable cyclicity,
and matrix/operator transport. The ordinary trace and cyclicity only require a
finite-dimensional normed space; the adjoint law requires an
inner-product space.

Mathlib supplies the underlying `LinearMap.trace`, finite-dimensional cyclicity, the canonical
Euclidean matrix/operator equivalence, and derivative composition machinery. This file provides the
thin analysis-level wrappers needed by downstream physics code.

No Kubo–Bastin, Středa, disorder, model-specific, trace-per-volume, or thermodynamic-limit semantics
are introduced here. Downstream physics layers apply these primitives where an ordinary finite trace
is genuinely required.
-/

namespace ContinuousLinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H]

section Normed

variable [NormedSpace ℂ H] [FiniteDimensional ℂ H]

/-- Ordinary finite-dimensional trace, bundled as a continuous linear functional on bounded
endomorphisms. Continuity follows because the bounded-endomorphism space is finite-dimensional. -/
noncomputable def finiteDimensionalOperatorTrace :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  ((LinearMap.trace ℂ H).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap

@[simp]
theorem finiteDimensionalOperatorTrace_apply (operator : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (H := H) operator =
      LinearMap.trace ℂ H (operator : H →ₗ[ℂ] H) :=
  (rfl)

/-- The finite-dimensional operator trace of a matrix transported through the canonical Euclidean
matrix/operator equivalence is its ordinary matrix trace. -/
theorem finiteDimensionalOperatorTrace_toEuclideanCLM
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    finiteDimensionalOperatorTrace
        ((Matrix.toEuclideanCLM :
          Matrix ι ι ℂ ≃⋆ₐ[ℂ]
            (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) M) =
      Matrix.trace M := by
  rw [finiteDimensionalOperatorTrace_apply]
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq M (EuclideanSpace.basisFun ι ℂ).toBasis

/-- Cyclicity of the bundled ordinary trace for two bounded endomorphisms. -/
theorem finiteDimensionalOperatorTrace_mul_comm
    (left right : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (H := H) (left * right) =
      finiteDimensionalOperatorTrace (H := H) (right * left) := by
  simp only [finiteDimensionalOperatorTrace_apply]
  exact LinearMap.trace_mul_comm ℂ (left : H →ₗ[ℂ] H) (right : H →ₗ[ℂ] H)

end Normed

section InnerProduct

variable [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

local instance : CompleteSpace H := FiniteDimensional.complete ℂ H

/-- The ordinary finite trace is bounded by the Hilbert-space dimension times the
operator norm. The dimension factor is explicit (as opposed to an opaque trace-functional
norm) and applies to any finite-dimensional complex Hilbert space. -/
theorem norm_finiteDimensionalOperatorTrace_le_finrank_mul
    (operator : H →L[ℂ] H) :
    ‖finiteDimensionalOperatorTrace (H := H) operator‖ ≤
      (Module.finrank ℂ H : ℝ) * ‖operator‖ := by
  let b := stdOrthonormalBasis ℂ H
  rw [finiteDimensionalOperatorTrace_apply]
  rw [LinearMap.trace_eq_sum_inner (operator : H →ₗ[ℂ] H) b]
  calc
    ‖∑ i, inner ℂ (b i) (operator (b i))‖ ≤
        ∑ i, ‖inner ℂ (b i) (operator (b i))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin (Module.finrank ℂ H), ‖operator‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hb : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
      calc
        ‖inner ℂ (b i) (operator (b i))‖ ≤
            ‖b i‖ * ‖operator (b i)‖ := norm_inner_le_norm _ _
        _ = ‖operator (b i)‖ := by rw [hb, one_mul]
        _ ≤ ‖operator‖ * ‖b i‖ := operator.le_opNorm (b i)
        _ = ‖operator‖ := by rw [hb, mul_one]
    _ = (Module.finrank ℂ H : ℝ) * ‖operator‖ := by simp

/-- Ordinary finite-dimensional trace is invariant under unitary conjugation.
Use the transported orthonormal basis rather than a separate matrix realization. -/
theorem finiteDimensionalOperatorTrace_conjStarAlgEquiv
    (W : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (W.conjStarAlgEquiv A) =
      finiteDimensionalOperatorTrace A := by
  let b := stdOrthonormalBasis ℂ H
  rw [finiteDimensionalOperatorTrace_apply, finiteDimensionalOperatorTrace_apply,
    LinearMap.trace_eq_sum_inner _ (b.map W), LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (W (b i)) (W.conjStarAlgEquiv A (W (b i))) =
    inner ℂ (b i) (A (b i))
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, W.symm_apply_apply]
  exact W.inner_map_map _ _

/-- Ordinary finite-dimensional trace intertwines the operator adjoint with complex conjugation. -/
theorem finiteDimensionalOperatorTrace_star
    (operator : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (H := H) (star operator) =
      star (finiteDimensionalOperatorTrace (H := H) operator) := by
  let b := stdOrthonormalBasis ℂ H
  rw [finiteDimensionalOperatorTrace_apply, finiteDimensionalOperatorTrace_apply,
    LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.star_eq_adjoint]
  change inner ℂ (b i) (operator.adjoint (b i)) =
    star (inner ℂ (b i) (operator (b i)))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

end InnerProduct

end

end ContinuousLinearMap
