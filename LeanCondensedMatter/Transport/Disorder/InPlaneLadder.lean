import LeanCondensedMatter.Transport.Disorder.Ladder
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Isotropic in-plane ladder coefficient algebra

A two-component rung `r = (X,Y)` acts through the matrix
`[[X, -Y], [Y, X]]`. The canonical action, determinant, generic
resummation bridge, and convergence statements use the full coefficient
vector. The fixed-point solution for the first Cartesian basis vector is
explicit when the shifted determinant is nonzero.
-/

namespace QuantumTheory.Transport

noncomputable section

open Filter
open scoped Interval

/-- Two complex coefficients indexed by the in-plane Cartesian directions. -/
abbrev InPlaneCoefficientVector := Fin 2 → ℂ

/-- In-plane coefficient vector with components `(x,y)`. -/
def inPlaneCoefficientVector (x y : ℂ) : InPlaneCoefficientVector := ![x, y]

/-- Isotropic in-plane matrix derived from a rung vector `(X,Y)`. -/
def inPlaneRotationMatrix (rung : InPlaneCoefficientVector) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![rung 0, -(rung 1); rung 1, rung 0]

@[simp] theorem inPlaneRotationMatrix_apply_x_x (rung : InPlaneCoefficientVector) :
    inPlaneRotationMatrix rung 0 0 = rung 0 := by
  simp [inPlaneRotationMatrix]

@[simp] theorem inPlaneRotationMatrix_apply_x_y (rung : InPlaneCoefficientVector) :
    inPlaneRotationMatrix rung 0 1 = -(rung 1) := by
  simp [inPlaneRotationMatrix]

@[simp] theorem inPlaneRotationMatrix_apply_y_x (rung : InPlaneCoefficientVector) :
    inPlaneRotationMatrix rung 1 0 = rung 1 := by
  simp [inPlaneRotationMatrix]

@[simp] theorem inPlaneRotationMatrix_apply_y_y (rung : InPlaneCoefficientVector) :
    inPlaneRotationMatrix rung 1 1 = rung 0 := by
  simp [inPlaneRotationMatrix]

/-- In-plane ladder action on the complete coefficient vector. -/
def inPlaneLadderAction
    (rung coefficients : InPlaneCoefficientVector) : InPlaneCoefficientVector :=
  (inPlaneRotationMatrix rung).mulVec coefficients

/-- The two-component ladder as a bounded complex-linear endomorphism, suitable for
the generic ladder resummation API. -/
noncomputable def inPlaneLadderCLM
    (rung : InPlaneCoefficientVector) :
    InPlaneCoefficientVector →L[ℂ] InPlaneCoefficientVector :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (inPlaneRotationMatrix rung))

@[simp]
theorem inPlaneLadderCLM_apply
    (rung coefficients : InPlaneCoefficientVector) :
    inPlaneLadderCLM rung coefficients = inPlaneLadderAction rung coefficients :=
  rfl

/-- The represented in-plane rotation depends continuously on the full coefficient vector. -/
theorem continuous_inPlaneRotationMatrix :
    Continuous inPlaneRotationMatrix := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      inPlaneRotationMatrix_apply_x_x, inPlaneRotationMatrix_apply_x_y,
      inPlaneRotationMatrix_apply_y_x, inPlaneRotationMatrix_apply_y_y] <;>
    fun_prop

@[simp]
theorem inPlaneLadderAction_apply_x
    (rung coefficients : InPlaneCoefficientVector) :
    inPlaneLadderAction rung coefficients 0 =
      rung 0 * coefficients 0 - rung 1 * coefficients 1 := by
  simp [inPlaneLadderAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    inPlaneRotationMatrix, sub_eq_add_neg]

@[simp]
theorem inPlaneLadderAction_apply_y
    (rung coefficients : InPlaneCoefficientVector) :
    inPlaneLadderAction rung coefficients 1 =
      rung 1 * coefficients 0 + rung 0 * coefficients 1 := by
  simp [inPlaneLadderAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    inPlaneRotationMatrix]

/-- Convergence of rung and coefficient vectors propagates to the complete ladder action. -/
theorem tendsto_inPlaneLadderAction
    {ι : Type*} {l : Filter ι} {rung coefficients : ι → InPlaneCoefficientVector}
    {rung₀ coefficients₀ : InPlaneCoefficientVector} (hrung : Tendsto rung l (nhds rung₀))
    (hcoefficients : Tendsto coefficients l (nhds coefficients₀)) :
    Tendsto (fun a => inPlaneLadderAction (rung a) (coefficients a)) l
      (nhds (inPlaneLadderAction rung₀ coefficients₀)) := by
  have h : Continuous (fun x : InPlaneCoefficientVector × InPlaneCoefficientVector =>
      inPlaneLadderAction x.1 x.2) :=
    (continuous_inPlaneRotationMatrix.comp continuous_fst).matrix_mulVec continuous_snd
  have hpair : Tendsto (fun a => (rung a, coefficients a)) l
      (nhds (rung₀, coefficients₀)) := hrung.prodMk_nhds hcoefficients
  have hcomp := (h.tendsto (rung₀, coefficients₀)).comp hpair
  simpa only [Function.comp_def] using hcomp

/-- Integrating the in-plane ladder action against a fixed coefficient vector amounts to
integrating its rung vector. Integrability and the integral identity share the same hypotheses. -/
theorem inPlaneLadderAction_integrable_and_integral_eq
    (rung : ℝ → InPlaneCoefficientVector) (coefficients : InPlaneCoefficientVector)
    (a b : ℝ) (hrung : ∀ i, IntervalIntegrable (fun p => rung p i) MeasureTheory.volume a b)
    (direction : Fin 2) :
    IntervalIntegrable (fun p => inPlaneLadderAction (rung p) coefficients direction)
      MeasureTheory.volume a b ∧
    (∫ p in a..b, inPlaneLadderAction (rung p) coefficients direction) =
      inPlaneLadderAction (fun i => ∫ p in a..b, rung p i) coefficients direction := by
  have hcomm (r : InPlaneCoefficientVector) :
      inPlaneLadderAction r coefficients direction = inPlaneLadderAction coefficients r direction := by
    fin_cases direction <;> simp only [Fin.zero_eta, Fin.mk_one,
      inPlaneLadderAction_apply_x, inPlaneLadderAction_apply_y] <;> ring
  simp_rw [hcomm]
  simp only [inPlaneLadderAction, Matrix.mulVec, dotProduct]
  have hint (i : Fin 2) : IntervalIntegrable
      (fun p => inPlaneRotationMatrix coefficients direction i * rung p i)
      MeasureTheory.volume a b := (hrung i).const_mul _
  exact ⟨by simpa only [Finset.sum_fn] using
    (IntervalIntegrable.sum Finset.univ (fun i _ => hint i)), by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
    simp only [intervalIntegral.integral_const_mul]⟩

/-- Determinant of the shifted two-component ladder equation `I - L`. -/
def inPlaneLadderDeterminant (rung : InPlaneCoefficientVector) : ℂ :=
  (1 - rung 0) ^ 2 + (rung 1) ^ 2

/-- Matrix form of the shifted ladder operator `I - L`. -/
def inPlaneShiftMatrix (rung : InPlaneCoefficientVector) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 - inPlaneRotationMatrix rung

/-- The closed scalar ladder denominator is the determinant of the shifted matrix. -/
@[simp] theorem inPlaneShiftMatrix_det (rung : InPlaneCoefficientVector) :
    (inPlaneShiftMatrix rung).det = inPlaneLadderDeterminant rung := by
  rw [Matrix.det_fin_two]
  simp [inPlaneShiftMatrix, inPlaneRotationMatrix, inPlaneLadderDeterminant]
  ring

/-- The determinant condition is exactly sufficient for the generic shifted-ladder
endomorphism to be a unit on the represented in-plane coefficient space. -/
theorem inPlaneLadderShift_isUnit
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0) :
    IsUnit (1 - inPlaneLadderCLM rung) := by
  let E : Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ]
      (InPlaneCoefficientVector →L[ℂ] InPlaneCoefficientVector) :=
    Matrix.toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap InPlaneCoefficientVector)
  have hmatrix : IsUnit (inPlaneShiftMatrix rung) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (by
      rw [inPlaneShiftMatrix_det]
      exact isUnit_iff_ne_zero.mpr hdet)
  change IsUnit (1 - E (inPlaneRotationMatrix rung))
  rw [← map_one E, ← map_sub E]
  exact (isUnit_map_iff E _).2 hmatrix

/-- Convergence of rung vectors propagates to the shifted-ladder determinant. -/
theorem tendsto_inPlaneLadderDeterminant
    {ι : Type*} {l : Filter ι}
    {rung : ι → InPlaneCoefficientVector} {rung₀ : InPlaneCoefficientVector}
    (hrung : Tendsto rung l (nhds rung₀)) :
    Tendsto (fun a => inPlaneLadderDeterminant (rung a)) l
      (nhds (inPlaneLadderDeterminant rung₀)) := by
  have hcoord := tendsto_pi_nhds.mp hrung
  simpa only [inPlaneLadderDeterminant] using
    (((tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℂ)) l (nhds 1)).sub
      (hcoord 0)).pow 2).add ((hcoord 1).pow 2)

/-- First Cartesian basis vector as the bare source. -/
def inPlaneLadderBareXSource : InPlaneCoefficientVector :=
  inPlaneCoefficientVector 1 0

/-- Exact coefficient vector of the ladder fixed point for the first Cartesian basis vector. -/
def inPlaneLadderSolvedVector (rung : InPlaneCoefficientVector) : InPlaneCoefficientVector :=
  inPlaneCoefficientVector
    ((1 - rung 0) / inPlaneLadderDeterminant rung)
    (rung 1 / inPlaneLadderDeterminant rung)

@[simp] theorem inPlaneLadderSolvedVector_apply_x (rung : InPlaneCoefficientVector) :
    inPlaneLadderSolvedVector rung 0 =
      (1 - rung 0) / inPlaneLadderDeterminant rung := by
  simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector]

@[simp] theorem inPlaneLadderSolvedVector_apply_y (rung : InPlaneCoefficientVector) :
    inPlaneLadderSolvedVector rung 1 = rung 1 / inPlaneLadderDeterminant rung := by
  simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector]

/-- Convergence of rung vectors propagates to the solved ladder vector whenever the limiting
shifted-ladder determinant is nonzero. -/
theorem tendsto_inPlaneLadderSolvedVector
    {ι : Type*} {l : Filter ι}
    {rung : ι → InPlaneCoefficientVector} {rung₀ : InPlaneCoefficientVector}
    (hrung : Tendsto rung l (nhds rung₀))
    (hdet : inPlaneLadderDeterminant rung₀ ≠ 0) :
    Tendsto
      (fun a => inPlaneLadderSolvedVector (rung a))
      l (nhds (inPlaneLadderSolvedVector rung₀)) := by
  have hcoord := tendsto_pi_nhds.mp hrung
  have hOne : Tendsto (fun _ : ι => (1 : ℂ)) l (nhds 1) := tendsto_const_nhds
  have hdetLimit := tendsto_inPlaneLadderDeterminant hrung
  rw [tendsto_pi_nhds]
  intro output
  fin_cases output
  · simpa [inPlaneLadderSolvedVector, inPlaneCoefficientVector, div_eq_mul_inv] using
      (hOne.sub (hcoord 0)).mul (hdetLimit.inv₀ hdet)
  · simpa [inPlaneLadderSolvedVector, inPlaneCoefficientVector, div_eq_mul_inv] using
      (hcoord 1).mul (hdetLimit.inv₀ hdet)

/-- The explicit coefficient vector solves the two-component ladder fixed-point equation. -/
theorem inPlaneLadderSolvedVector_fixedPoint
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0) :
    inPlaneLadderSolvedVector rung =
      inPlaneLadderBareXSource + inPlaneLadderAction rung (inPlaneLadderSolvedVector rung) := by
  funext direction
  fin_cases direction
  · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector, inPlaneLadderAction_apply_x]
    field_simp [hdet]
    unfold inPlaneLadderDeterminant
    ring
  · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector, inPlaneLadderAction_apply_y]
    field_simp [hdet]
    ring

/-- The explicit two-component solution is the generic algebraically resummed ladder vertex. -/
theorem inPlaneLadderSolvedVector_eq_resummedLadderVertex
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0) :
    inPlaneLadderSolvedVector rung =
      resummedLadderVertex
        (inPlaneLadderCLM rung) (inPlaneLadderShift_isUnit rung hdet)
        inPlaneLadderBareXSource := by
  exact eq_resummedLadderVertex_of_fixedPoint
    (inPlaneLadderCLM rung) (inPlaneLadderShift_isUnit rung hdet)
    inPlaneLadderBareXSource (inPlaneLadderSolvedVector rung)
    (by simpa only [inPlaneLadderCLM_apply] using inPlaneLadderSolvedVector_fixedPoint rung hdet)

/-- With no transverse rung mixing, the vector solution reduces to the scalar ladder factor in the
longitudinal component and zero in the transverse component. -/
theorem inPlaneLadderSolvedVector_zero_transverse
    (x : ℂ) (hx : 1 - x ≠ 0) :
    inPlaneLadderSolvedVector (inPlaneCoefficientVector x 0) =
      inPlaneCoefficientVector (1 - x)⁻¹ 0 := by
  funext direction
  fin_cases direction
  · simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector, inPlaneLadderDeterminant]
    field_simp [hx]
  · simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector]

end

end QuantumTheory.Transport
