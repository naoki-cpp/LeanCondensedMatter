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

The existing coefficientwise `operatorIntervalIntegral` remains the algebraic definition used by
the Dyson and diagrammatic layers. The theorem `continuousOperatorIntervalIntegral_eq` proves that,
for a matrix-coefficient-continuous operator family, its transported value agrees with Mathlib's
Bochner interval integral. Thus analytic call sites can use the normed continuous-operator API
without imposing a topology or norm on `AlgebraicFock Config` itself.
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

/-- The continuous finite-dimensional operator induced by an algebraic Fock endomorphism. -/
noncomputable def finiteContinuousOperator
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    FiniteContinuousOperator Config :=
  finiteContinuousOperatorAlgEquiv A

@[simp]
theorem finiteContinuousOperator_equiv_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (x : AlgebraicFock Config) :
    finiteContinuousOperator A (finiteAnalyticFockEquiv x) = finiteAnalyticFockEquiv (A x) := by
  change
    ((finiteAnalyticFockEquiv (Config := Config)).toLinearMap.comp
      (A.comp (finiteAnalyticFockEquiv (Config := Config)).symm.toLinearMap))
        (finiteAnalyticFockEquiv x) = finiteAnalyticFockEquiv (A x)
  simp

@[simp]
theorem finiteContinuousOperator_zero :
    finiteContinuousOperator
        (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 0 := by
  simpa [finiteContinuousOperator] using
    map_zero (finiteContinuousOperatorAlgEquiv (Config := Config))

@[simp]
theorem finiteContinuousOperator_add
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteContinuousOperator (A + B) =
      finiteContinuousOperator A + finiteContinuousOperator B := by
  simpa [finiteContinuousOperator] using
    map_add (finiteContinuousOperatorAlgEquiv (Config := Config)) A B

@[simp]
theorem finiteContinuousOperator_smul (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteContinuousOperator (c • A) = c • finiteContinuousOperator A := by
  simpa [finiteContinuousOperator] using
    map_smul (finiteContinuousOperatorAlgEquiv (Config := Config)) c A

@[simp]
theorem finiteContinuousOperator_neg
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteContinuousOperator (-A) = -finiteContinuousOperator A := by
  simpa [finiteContinuousOperator] using
    map_neg (finiteContinuousOperatorAlgEquiv (Config := Config)) A

@[simp]
theorem finiteContinuousOperator_id :
    finiteContinuousOperator
        (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) =
      ContinuousLinearMap.id ℂ (FiniteAnalyticFock Config) := by
  change
    finiteContinuousOperatorAlgEquiv
        (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) =
      ContinuousLinearMap.id ℂ (FiniteAnalyticFock Config)
  rw [← Module.End.one_eq_id, ← ContinuousLinearMap.one_def]
  exact map_one (finiteContinuousOperatorAlgEquiv (Config := Config))

@[simp]
theorem finiteContinuousOperator_one :
    finiteContinuousOperator
        (1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 1 := by
  simpa [finiteContinuousOperator] using
    map_one (finiteContinuousOperatorAlgEquiv (Config := Config))

@[simp]
theorem finiteContinuousOperator_mul
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteContinuousOperator (A * B) =
      finiteContinuousOperator A * finiteContinuousOperator B := by
  simpa [finiteContinuousOperator] using
    map_mul (finiteContinuousOperatorAlgEquiv (Config := Config)) A B

@[simp]
theorem finiteContinuousOperator_comp
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteContinuousOperator (A.comp B) =
      (finiteContinuousOperator A).comp (finiteContinuousOperator B) := by
  change finiteContinuousOperator (A * B) =
    finiteContinuousOperator A * finiteContinuousOperator B
  exact finiteContinuousOperator_mul A B

@[simp]
theorem finiteContinuousOperator_pow
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    finiteContinuousOperator (A ^ n) = finiteContinuousOperator A ^ n := by
  simpa [finiteContinuousOperator] using
    map_pow (finiteContinuousOperatorAlgEquiv (Config := Config)) A n

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
    finiteContinuousOperator A (finiteAnalyticBasis n) m = matrixCoeff A m n := by
  rw [← finiteAnalyticFockEquiv_basisState, finiteContinuousOperator_equiv_apply]
  rfl

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

/-- Matrix multiplication formula for the transported continuous operator. -/
theorem finiteContinuousOperator_apply_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (x : FiniteAnalyticFock Config) (m : Config) :
    finiteContinuousOperator A x m = ∑ n : Config, matrixCoeff A m n * x n := by
  classical
  have hx : x = ∑ n : Config, x n • finiteAnalyticBasis n := by
    simpa [finiteAnalyticBasis] using (pi_eq_sum_univ' x)
  calc
    finiteContinuousOperator A x m =
        finiteContinuousOperator A (∑ n : Config, x n • finiteAnalyticBasis n) m :=
      congrArg (fun y => finiteContinuousOperator A y m) hx
    _ = (∑ n : Config, x n • finiteContinuousOperator A (finiteAnalyticBasis n)) m := by simp
    _ = ∑ n : Config, matrixCoeff A m n * x n := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        finiteContinuousOperator_basis_apply]
      exact Finset.sum_congr rfl fun n _ => mul_comm _ _

/-- Continuous finite operators are continuously equivalent to their columns on the standard
coordinate basis. -/
noncomputable def finiteContinuousOperatorColumns :
    FiniteContinuousOperator Config ≃L[ℂ] Config → FiniteAnalyticFock Config := by
  classical
  exact ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := FiniteAnalyticFock Config) Config

set_option linter.unusedFintypeInType false in
@[simp]
theorem finiteContinuousOperatorColumns_apply
    (A : FiniteContinuousOperator Config) (n : Config) :
    finiteContinuousOperatorColumns A n = A (finiteAnalyticBasis n) := by
  classical
  simp [finiteContinuousOperatorColumns, finiteAnalyticBasis,
    ContinuousLinearEquiv.piRing, LinearEquiv.piRing_apply]

/-- Matrix-coefficient continuity implies continuity of the transported operator-valued family. -/
theorem continuous_finiteContinuousOperator
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hF : ∀ m n : Config, Continuous (fun τ : ℝ => matrixCoeff (F τ) m n)) :
    Continuous (fun τ : ℝ => finiteContinuousOperator (F τ)) := by
  classical
  have hcolumns : Continuous (fun τ : ℝ =>
      finiteContinuousOperatorColumns (finiteContinuousOperator (F τ))) := by
    apply continuous_pi
    intro n
    apply continuous_pi
    intro m
    simpa only [finiteContinuousOperatorColumns_apply, finiteContinuousOperator_basis_apply]
      using hF m n
  exact (finiteContinuousOperatorColumns.symm.continuous.comp hcolumns).congr fun τ =>
    finiteContinuousOperatorColumns.symm_apply_apply _

/-- Coordinate evaluation on the analytic finite-dimensional realization. -/
noncomputable def finiteAnalyticCoordinate (m : Config) : FiniteAnalyticFock Config →L[ℂ] ℂ :=
  ({
    toFun := fun x => x m
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  } : FiniteAnalyticFock Config →ₗ[ℂ] ℂ).toContinuousLinearMap

@[simp]
theorem finiteAnalyticCoordinate_apply (m : Config) (x : FiniteAnalyticFock Config) :
    finiteAnalyticCoordinate m x = x m := rfl

/-- Compatibility on each analytic basis vector between the coefficientwise algebraic integral and
Mathlib's Bochner interval integral of transported continuous operators. -/
theorem continuousOperatorIntervalIntegral_basis
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hF : ∀ m n : Config, Continuous (fun τ : ℝ => matrixCoeff (F τ) m n))
    (a b : ℝ) (n : Config) :
    finiteContinuousOperator (operatorIntervalIntegral F a b) (finiteAnalyticBasis n) =
      (∫ τ in a..b, finiteContinuousOperator (F τ)) (finiteAnalyticBasis n) := by
  classical
  have hop : Continuous (fun τ : ℝ => finiteContinuousOperator (F τ)) :=
    continuous_finiteContinuousOperator F hF
  have hopInt : IntervalIntegrable (fun τ : ℝ => finiteContinuousOperator (F τ))
      MeasureTheory.volume a b := hop.intervalIntegrable a b
  rw [ContinuousLinearMap.intervalIntegral_apply hopInt]
  funext m
  rw [finiteContinuousOperator_basis_apply, matrixCoeff_operatorIntervalIntegral]
  have hvecCont : Continuous
      (fun τ : ℝ => finiteContinuousOperator (F τ) (finiteAnalyticBasis n)) :=
    hop.clm_apply continuous_const
  have hvecInt : IntervalIntegrable
      (fun τ : ℝ => finiteContinuousOperator (F τ) (finiteAnalyticBasis n))
      MeasureTheory.volume a b := hvecCont.intervalIntegrable a b
  change (∫ τ in a..b, matrixCoeff (F τ) m n) =
    finiteAnalyticCoordinate m
      (∫ τ in a..b, finiteContinuousOperator (F τ) (finiteAnalyticBasis n))
  rw [← (finiteAnalyticCoordinate m).intervalIntegral_comp_comm hvecInt]
  exact intervalIntegral.integral_congr fun τ _ => by
    simpa using (finiteContinuousOperator_basis_apply (F τ) m n).symm

/-- The transported coefficientwise algebraic interval integral equals Mathlib's Bochner interval
integral of the transported continuous-operator family. -/
theorem continuousOperatorIntervalIntegral_eq
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hF : ∀ m n : Config, Continuous (fun τ : ℝ => matrixCoeff (F τ) m n))
    (a b : ℝ) :
    finiteContinuousOperator (operatorIntervalIntegral F a b) =
      ∫ τ in a..b, finiteContinuousOperator (F τ) := by
  apply finiteContinuousOperator_ext_basis
  intro n
  exact continuousOperatorIntervalIntegral_basis F hF a b n

end
end Common
end SecondQuantization
