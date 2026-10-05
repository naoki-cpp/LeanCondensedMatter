import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option linter.style.header false

/-!
# Finite-dimensional analytic realization of algebraic Fock operators

For a finite configuration type, `AlgebraicFock Config = Config →₀ ℂ` is transported through
`Finsupp.linearEquivFunOnFinite` to the normed finite-dimensional space `Config → ℂ`. Algebraic
endomorphisms are transported by the canonical conjugation algebra equivalence and the
finite-dimensional equivalence between linear and continuous linear endomorphisms.

The ordinary finite-dimensional trace is bundled on the continuous realization and proved compatible
with the existing algebraic `traceFock`. The coefficientwise `operatorIntervalIntegral` remains the
algebraic definition used by the Dyson and diagrammatic layers. The theorem
`continuousOperatorIntervalIntegral_eq` proves that, for a matrix-coefficient-continuous operator
family, its transported value agrees with Mathlib's Bochner interval integral. Thus analytic call
sites can use the normed continuous-operator API without imposing a topology or norm on
`AlgebraicFock Config` itself.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The finite-dimensional normed realization of the algebraic Fock space. -/
abbrev FiniteAnalyticFock (Config : Type*) := Config → ℂ

/-- Continuous endomorphisms of the finite-dimensional analytic Fock realization. -/
abbrev FiniteContinuousOperator (Config : Type*) :=
  FiniteAnalyticFock Config →L[ℂ] FiniteAnalyticFock Config

/-- The canonical finite-support/function linear equivalence for finite `Config`. -/
noncomputable def finiteAnalyticFockEquiv :
    AlgebraicFock Config ≃ₗ[ℂ] FiniteAnalyticFock Config :=
  Finsupp.linearEquivFunOnFinite ℂ ℂ Config

/-- Canonical transport of algebraic Fock endomorphisms to continuous finite-dimensional
operators. -/
noncomputable def finiteContinuousOperatorAlgEquiv :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) ≃ₐ[ℂ]
      FiniteContinuousOperator Config :=
  ((finiteAnalyticFockEquiv (Config := Config)).conjAlgEquiv ℂ).trans
    (Module.End.toContinuousLinearMap (FiniteAnalyticFock Config))

@[simp]
theorem finiteContinuousOperator_equiv_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (x : AlgebraicFock Config) :
    finiteContinuousOperatorAlgEquiv A (finiteAnalyticFockEquiv x) =
      finiteAnalyticFockEquiv (A x) := by
  change
    ((finiteAnalyticFockEquiv (Config := Config)).toLinearMap.comp
      (A.comp (finiteAnalyticFockEquiv (Config := Config)).symm.toLinearMap))
        (finiteAnalyticFockEquiv x) = finiteAnalyticFockEquiv (A x)
  simp

/-- The standard coordinate basis vector in the analytic realization. -/
noncomputable def finiteAnalyticBasis (n : Config) : FiniteAnalyticFock Config :=
  Pi.basisFun ℂ Config n

@[simp]
theorem finiteAnalyticFockEquiv_basisState (n : Config) :
    finiteAnalyticFockEquiv (basisState n) = finiteAnalyticBasis n := by
  classical
  rw [finiteAnalyticBasis, Pi.basisFun_apply]
  exact Finsupp.linearEquivFunOnFinite_single ℂ ℂ Config n 1

@[simp]
theorem finiteContinuousOperator_basis_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    finiteContinuousOperatorAlgEquiv A (finiteAnalyticBasis n) m = matrixCoeff A m n := by
  rw [← finiteAnalyticFockEquiv_basisState, finiteContinuousOperator_equiv_apply]
  rfl

/-- The ordinary finite-dimensional trace, bundled as a continuous linear functional on the
continuous-operator algebra. -/
noncomputable def finiteOperatorTrace :
    FiniteContinuousOperator Config →L[ℂ] ℂ :=
  ∑ n : Config,
    (ContinuousLinearMap.proj n : FiniteAnalyticFock Config →L[ℂ] ℂ).comp
      (ContinuousLinearMap.apply ℂ (FiniteAnalyticFock Config) (finiteAnalyticBasis n))

@[simp]
theorem finiteOperatorTrace_apply (A : FiniteContinuousOperator Config) :
    finiteOperatorTrace A = ∑ n : Config, A (finiteAnalyticBasis n) n := by
  simp [finiteOperatorTrace]

/-- The continuous trace agrees with the existing algebraic `traceFock` after transport. -/
theorem finiteOperatorTrace_finiteContinuousOperator
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteOperatorTrace (finiteContinuousOperatorAlgEquiv A) = traceFock A := by
  simp [finiteOperatorTrace_apply, traceFock_eq_sum_matrixCoeff,
    finiteContinuousOperator_basis_apply]

set_option linter.unusedFintypeInType false in
/-- Two continuous finite operators that agree on every standard basis vector are equal. -/
theorem finiteContinuousOperator_ext_basis
    {A B : FiniteContinuousOperator Config}
    (h : ∀ n : Config, A (finiteAnalyticBasis n) = B (finiteAnalyticBasis n)) : A = B := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  have hlinear : A.toLinearMap = B.toLinearMap := by
    apply (Pi.basisFun ℂ Config).ext
    intro n
    simpa [finiteAnalyticBasis] using h n
  exact LinearMap.congr_fun hlinear x

/-- Matrix-coefficient continuity implies continuity of the transported operator-valued family. -/
theorem continuous_finiteContinuousOperator
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hF : ∀ m n : Config, Continuous (fun τ : ℝ => matrixCoeff (F τ) m n)) :
    Continuous (fun τ : ℝ => finiteContinuousOperatorAlgEquiv (F τ)) := by
  classical
  let columns : FiniteContinuousOperator Config ≃L[ℂ] Config → FiniteAnalyticFock Config :=
    ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := FiniteAnalyticFock Config) Config
  have hcol (A : FiniteContinuousOperator Config) (n : Config) :
      columns A n = A (finiteAnalyticBasis n) := by
    simp [columns, finiteAnalyticBasis, ContinuousLinearEquiv.piRing, LinearEquiv.piRing_apply]
  have hcolumns : Continuous (fun τ : ℝ => columns (finiteContinuousOperatorAlgEquiv (F τ))) := by
    apply continuous_pi
    intro n
    apply continuous_pi
    intro m
    simpa only [hcol, finiteContinuousOperator_basis_apply] using hF m n
  exact (columns.symm.continuous.comp hcolumns).congr fun τ => columns.symm_apply_apply _

/-- Compatibility on each analytic basis vector between the coefficientwise algebraic integral and
Mathlib's Bochner interval integral of transported continuous operators. -/
private theorem continuousOperatorIntervalIntegral_basis
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hF : ∀ m n : Config, Continuous (fun τ : ℝ => matrixCoeff (F τ) m n))
    (a b : ℝ) (n : Config) :
    finiteContinuousOperatorAlgEquiv (operatorIntervalIntegral F a b) (finiteAnalyticBasis n) =
      (∫ τ in a..b, finiteContinuousOperatorAlgEquiv (F τ)) (finiteAnalyticBasis n) := by
  classical
  have hop : Continuous (fun τ : ℝ => finiteContinuousOperatorAlgEquiv (F τ)) :=
    continuous_finiteContinuousOperator F hF
  have hopInt : IntervalIntegrable (fun τ : ℝ => finiteContinuousOperatorAlgEquiv (F τ))
      MeasureTheory.volume a b := hop.intervalIntegrable a b
  rw [ContinuousLinearMap.intervalIntegral_apply hopInt]
  funext m
  rw [finiteContinuousOperator_basis_apply, matrixCoeff_operatorIntervalIntegral]
  have hvecCont : Continuous
      (fun τ : ℝ => finiteContinuousOperatorAlgEquiv (F τ) (finiteAnalyticBasis n)) :=
    hop.clm_apply continuous_const
  have hvecInt : IntervalIntegrable
      (fun τ : ℝ => finiteContinuousOperatorAlgEquiv (F τ) (finiteAnalyticBasis n))
      MeasureTheory.volume a b := hvecCont.intervalIntegrable a b
  change (∫ τ in a..b, matrixCoeff (F τ) m n) =
    (ContinuousLinearMap.proj m : FiniteAnalyticFock Config →L[ℂ] ℂ)
      (∫ τ in a..b, finiteContinuousOperatorAlgEquiv (F τ) (finiteAnalyticBasis n))
  rw [← (ContinuousLinearMap.proj m : FiniteAnalyticFock Config →L[ℂ] ℂ).intervalIntegral_comp_comm
    hvecInt]
  exact intervalIntegral.integral_congr fun τ _ => by
    simpa using (finiteContinuousOperator_basis_apply (F τ) m n).symm

/-- The transported coefficientwise algebraic interval integral equals Mathlib's Bochner interval
integral of the transported continuous-operator family. -/
theorem continuousOperatorIntervalIntegral_eq
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hF : ∀ m n : Config, Continuous (fun τ : ℝ => matrixCoeff (F τ) m n))
    (a b : ℝ) :
    finiteContinuousOperatorAlgEquiv (operatorIntervalIntegral F a b) =
      ∫ τ in a..b, finiteContinuousOperatorAlgEquiv (F τ) := by
  apply finiteContinuousOperator_ext_basis
  intro n
  exact continuousOperatorIntervalIntegral_basis F hF a b n

end
end Common
end SecondQuantization
