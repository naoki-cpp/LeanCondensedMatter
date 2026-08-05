import LeanCondensedMatter.QuantumTheory.DensityOperator.ExpectationOrder
import LeanCondensedMatter.QuantumTheory.DensityOperator.Pure
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Real expectations of observables

The canonical density-state expectation remains complex-linear on arbitrary bounded operators.
When the operator is an observable, self-adjointness proves that scalar to be real, and this module
transports it losslessly to `ℝ`. It also identifies the density-state expectation of a rank-one pure
state with the vector-state expectation from `QuantumTheory.Postulates`.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The complex density-state expectation of an observable, bundled with its self-adjointness. -/
noncomputable def DensityOperator.observableExpectationSelfAdjoint
    (ρ : DensityOperator H) (A : Observable H) : selfAdjoint ℂ :=
  ⟨ρ.expectation A.1,
    ρ.expectation_isSelfAdjoint_of_isSymmetric A.2.isSymmetric⟩

/-- The real expectation value of an observable in a density state, obtained losslessly from the
proved-self-adjoint complex expectation rather than by projecting an arbitrary scalar with `.re`. -/
noncomputable def DensityOperator.observableExpectation
    (ρ : DensityOperator H) (A : Observable H) : ℝ :=
  Complex.selfAdjointEquiv (ρ.observableExpectationSelfAdjoint A)

/-- The canonical complex expectation is exactly the complex embedding of the real observable
expectation. -/
@[simp]
theorem DensityOperator.expectation_observable
    (ρ : DensityOperator H) (A : Observable H) :
    ρ.expectation A.1 = (ρ.observableExpectation A : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa [DensityOperator.observableExpectation,
      DensityOperator.observableExpectationSelfAdjoint, Complex.selfAdjointEquiv] using
      ρ.expectation_im_eq_zero_of_isSymmetric A.2.isSymmetric

/-- The complex expectation in the rank-one density operator of a pure state agrees with the
canonical vector-state expectation. -/
theorem DensityOperator.expectation_pure_observable
    (ψ : State H) (A : Observable H) :
    (pure ψ).expectation A.1 = expValue A ψ := by
  letI := uniqueEigenvectorIndexRankOne ψ.2
  rw [(pure ψ).expectation_apply A.1]
  change
    (∑' a : EigenvectorIndex
      (InnerProductSpace.rankOne ℂ ψ.1 ψ.1 : H →L[ℂ] H),
      (a.1.1 : ℂ) *
        inner ℂ (eigenvectorFamily (pure ψ).spectralTraceClass.compact a)
          (A.1 (eigenvectorFamily (pure ψ).spectralTraceClass.compact a))) =
      expValue A ψ
  rw [tsum_eq_single (uniqueEigenvectorIndexRankOne ψ.2).default (fun b hb =>
    absurd (Subsingleton.elim b (uniqueEigenvectorIndexRankOne ψ.2).default) hb)]
  let a₀ := (uniqueEigenvectorIndexRankOne ψ.2).default
  let e := eigenvectorFamily (pure ψ).spectralTraceClass.compact a₀
  have ha₀ : a₀.1.1 = 1 := rfl
  have he_norm : ‖e‖ = 1 := by
    simpa [e, a₀] using eigenvectorFamily_norm_eq_one (pure ψ) a₀
  have he_eigen :
      ((InnerProductSpace.rankOne ℂ ψ.1 ψ.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) e =
        (1 : ℂ) • e := by
    have h := apply_eigenvectorFamily (pure ψ).spectralTraceClass.compact a₀
    change
      ((InnerProductSpace.rankOne ℂ ψ.1 ψ.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) e =
        (a₀.1.1 : ℂ) • e at h
    simpa [ha₀] using h
  have he_mem :
      e ∈ Module.End.eigenspace
        ((InnerProductSpace.rankOne ℂ ψ.1 ψ.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) 1 :=
    Module.End.mem_eigenspace_iff.mpr (by simpa using he_eigen)
  rw [eigenspace_rankOne_one ψ.2] at he_mem
  rcases Submodule.mem_span_singleton.mp he_mem with ⟨c, hc⟩
  have hc_norm : ‖c‖ = 1 := by
    have hnorm := congrArg norm hc
    simpa [norm_smul, ψ.2, he_norm] using hnorm
  have hscaled : ‖c • ψ.1‖ = 1 := by
    rw [hc, he_norm]
  have hphase := expValue_smul_of_norm_eq_one A ψ hc_norm hscaled
  have hinner : inner ℂ e (A.1 e) = expValue A ψ := by
    simpa [expValue, hc] using hphase
  change (a₀.1.1 : ℂ) * inner ℂ e (A.1 e) = expValue A ψ
  simpa [ha₀] using hinner

/-- The real observable expectation in a rank-one density operator agrees with the lossless real
vector-state expectation. -/
@[simp]
theorem DensityOperator.observableExpectation_pure
    (ψ : State H) (A : Observable H) :
    (pure ψ).observableExpectation A = observableExpValue A ψ := by
  apply Complex.ofReal_injective
  rw [← (pure ψ).expectation_observable A, coe_observableExpValue,
    DensityOperator.expectation_pure_observable]

end QuantumTheory
