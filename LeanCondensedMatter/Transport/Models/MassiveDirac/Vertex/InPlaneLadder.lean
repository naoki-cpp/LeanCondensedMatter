import LeanCondensedMatter.Transport.Disorder.Ladder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

set_option linter.style.header false

/-!
# In-plane massive-Dirac ladder coefficient algebra

This module owns the exact two-component algebra needed once a massive-Dirac retarded-advanced
current rung has been reduced to the in-plane Pauli span. For the repository orientation
`Gᴿ Γ Gᴬ`, a rung vector `r = (X,Y)` acts through the matrix

```text
[[X, -Y], [Y, X]].
```

The rung, bare-`σₓ` source, and solved fixed point are standard `Fin 2 → ℂ` vectors. Coordinate
projections remain available where downstream physics needs a concrete `x` or `y` component, but
the canonical action, determinant, generic resummation bridge, and convergence statements consume
the complete vector. This file does not define the Born-Dyson momentum integrals that supply the rung, take any
broadening/disorder limit, identify a transport lifetime, or insert the result into conductivity.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter

/-- Two complex coefficients indexed by the in-plane Cartesian directions. -/
abbrev InPlaneCoefficientVector := Fin 2 → ℂ

/-- In-plane coefficient vector with components `(x,y)`. -/
def inPlaneCoefficientVector (x y : ℂ) : InPlaneCoefficientVector := ![x, y]

/-- Repository-oriented isotropic in-plane matrix derived from a rung vector `(X,Y)`. -/
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

/-- Repository-oriented in-plane ladder action on the complete coefficient vector. -/
def inPlaneLadderAction
    (rung coefficients : InPlaneCoefficientVector) : InPlaneCoefficientVector :=
  (inPlaneRotationMatrix rung).mulVec coefficients

/-- The two-component massive-Dirac ladder as a bounded complex-linear endomorphism, suitable for
the generic ladder resummation API. -/
noncomputable def inPlaneLadderCLM
    (rung : InPlaneCoefficientVector) :
    InPlaneCoefficientVector →L[ℂ] InPlaneCoefficientVector := by
  let linearMap : InPlaneCoefficientVector →ₗ[ℂ] InPlaneCoefficientVector :=
    Matrix.mulVecLin (inPlaneRotationMatrix rung)
  exact ⟨linearMap, linearMap.continuous_of_finiteDimensional⟩

@[simp]
theorem inPlaneLadderCLM_apply
    (rung coefficients : InPlaneCoefficientVector) :
    inPlaneLadderCLM rung coefficients = inPlaneLadderAction rung coefficients := by
  rfl

private theorem continuous_inPlaneRotationMatrix :
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
  have hrungMatrix :
      Tendsto (inPlaneRotationMatrix ∘ rung) l
        (nhds (inPlaneRotationMatrix rung₀)) :=
    (continuous_inPlaneRotationMatrix.tendsto rung₀).comp hrung
  have hmul :
      Continuous fun p :
        Matrix (Fin 2) (Fin 2) ℂ × InPlaneCoefficientVector => p.1.mulVec p.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  change Tendsto
    ((fun p : Matrix (Fin 2) (Fin 2) ℂ × InPlaneCoefficientVector => p.1.mulVec p.2) ∘
      fun a => (inPlaneRotationMatrix (rung a), coefficients a))
    l (nhds ((inPlaneRotationMatrix rung₀).mulVec coefficients₀))
  exact (hmul.tendsto (inPlaneRotationMatrix rung₀, coefficients₀)).comp
    (hrungMatrix.prodMk_nhds hcoefficients)

/-- Determinant of the shifted two-component ladder equation `I - L`. -/
def inPlaneLadderDeterminant (rung : InPlaneCoefficientVector) : ℂ :=
  (1 - rung 0) ^ 2 + (rung 1) ^ 2

/-- Matrix form of the shifted ladder operator `I - L`. -/
def inPlaneShiftMatrix (rung : InPlaneCoefficientVector) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 - inPlaneRotationMatrix rung

private theorem continuous_inPlaneShiftMatrix :
    Continuous inPlaneShiftMatrix := by
  unfold inPlaneShiftMatrix
  exact continuous_const.sub continuous_inPlaneRotationMatrix

/-- The closed scalar ladder denominator is the determinant of the shifted matrix. -/
@[simp] theorem inPlaneShiftMatrix_det (rung : InPlaneCoefficientVector) :
    (inPlaneShiftMatrix rung).det = inPlaneLadderDeterminant rung := by
  rw [Matrix.det_fin_two]
  simp [inPlaneShiftMatrix, inPlaneRotationMatrix, inPlaneLadderDeterminant]
  ring

/-- Acting with `I - L` is vector subtraction by the ladder action. -/
theorem inPlaneShiftMatrix_mulVec
    (rung coefficients : InPlaneCoefficientVector) :
    (inPlaneShiftMatrix rung).mulVec coefficients =
      coefficients - inPlaneLadderAction rung coefficients := by
  simpa [inPlaneShiftMatrix, inPlaneLadderAction] using
    (Matrix.sub_mulVec
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (inPlaneRotationMatrix rung) coefficients)

/-- A nonzero explicit two-component determinant supplies the generic ladder invertibility
hypothesis on the in-plane coefficient space. -/
theorem inPlaneLadderShift_isUnit
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0) :
    IsUnit (1 - inPlaneLadderCLM rung) := by
  let shift : InPlaneCoefficientVector →L[ℂ] InPlaneCoefficientVector :=
    1 - inPlaneLadderCLM rung
  have hinjective : Function.Injective shift := by
    have hmatrix : Function.Injective (inPlaneShiftMatrix rung).mulVec :=
      Matrix.mulVec_injective_of_det_ne_zero (by simpa using hdet)
    intro left right h
    apply hmatrix
    simpa [shift, inPlaneLadderCLM_apply, inPlaneShiftMatrix_mulVec] using h
  have hsurjective : Function.Surjective shift := by
    exact LinearMap.surjective_of_injective (f := shift.toLinearMap) hinjective
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinjective, hsurjective⟩

/-- Convergence of rung vectors propagates to the shifted-ladder determinant. -/
theorem tendsto_inPlaneLadderDeterminant
    {ι : Type*} {l : Filter ι}
    {rung : ι → InPlaneCoefficientVector} {rung₀ : InPlaneCoefficientVector}
    (hrung : Tendsto rung l (nhds rung₀)) :
    Tendsto (fun a => inPlaneLadderDeterminant (rung a)) l
      (nhds (inPlaneLadderDeterminant rung₀)) := by
  have hshift :
      Tendsto (inPlaneShiftMatrix ∘ rung) l
        (nhds (inPlaneShiftMatrix rung₀)) :=
    (continuous_inPlaneShiftMatrix.tendsto rung₀).comp hrung
  have hdet :
      Tendsto ((fun M : Matrix (Fin 2) (Fin 2) ℂ => M.det) ∘
        (inPlaneShiftMatrix ∘ rung)) l
        (nhds (inPlaneShiftMatrix rung₀).det) :=
    (continuous_id.matrix_det.tendsto (inPlaneShiftMatrix rung₀)).comp hshift
  simpa only [Function.comp_def, inPlaneShiftMatrix_det] using hdet

/-- Bare `σₓ` source represented as one in-plane coefficient vector. -/
def inPlaneLadderBareXSource : InPlaneCoefficientVector :=
  inPlaneCoefficientVector 1 0

/-- Exact coefficient vector of the bare-`σₓ` ladder fixed point. -/
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
  have hx := (tendsto_pi_nhds.mp hrung) (0 : Fin 2)
  have hy := (tendsto_pi_nhds.mp hrung) (1 : Fin 2)
  have hOne : Tendsto (fun _ : ι => (1 : ℂ)) l (nhds 1) := tendsto_const_nhds
  have hOneMinusX := hOne.sub hx
  have hdetLimit := tendsto_inPlaneLadderDeterminant hrung
  rw [tendsto_pi_nhds]
  intro output
  fin_cases output
  · simpa [inPlaneLadderSolvedVector, inPlaneCoefficientVector, div_eq_mul_inv] using
      hOneMinusX.mul (hdetLimit.inv₀ hdet)
  · simpa [inPlaneLadderSolvedVector, inPlaneCoefficientVector, div_eq_mul_inv] using
      hy.mul (hdetLimit.inv₀ hdet)

/-- The explicit two-component solution is the generic algebraically resummed ladder vertex. -/
theorem inPlaneLadderSolvedVector_eq_resummedLadderVertex
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0) :
    inPlaneLadderSolvedVector rung =
      resummedLadderVertex
        (inPlaneLadderCLM rung) (inPlaneLadderShift_isUnit rung hdet)
        inPlaneLadderBareXSource := by
  have hfixed :
      inPlaneLadderSolvedVector rung =
        inPlaneLadderBareXSource +
          inPlaneLadderCLM rung (inPlaneLadderSolvedVector rung) := by
    funext direction
    fin_cases direction
    · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector,
        inPlaneLadderCLM_apply, inPlaneLadderAction_apply_x]
      field_simp [hdet]
      unfold inPlaneLadderDeterminant
      ring
    · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector,
        inPlaneLadderCLM_apply, inPlaneLadderAction_apply_y]
      field_simp [hdet]
      ring
  exact
    eq_resummedLadderVertex_of_fixedPoint
      (inPlaneLadderCLM rung) (inPlaneLadderShift_isUnit rung hdet)
      inPlaneLadderBareXSource (inPlaneLadderSolvedVector rung) hfixed

/-- The explicit solution remains equal after embedding into the in-plane Pauli-operator subspace. -/
theorem inPlanePauliVertexCLM_solvedVector_eq_resummedLadderVertex
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0) :
    inPlanePauliVertexCLM (inPlaneLadderSolvedVector rung) =
      inPlanePauliVertexCLM
        (resummedLadderVertex
          (inPlaneLadderCLM rung) (inPlaneLadderShift_isUnit rung hdet)
          inPlaneLadderBareXSource) := by
  rw [inPlaneLadderSolvedVector_eq_resummedLadderVertex rung hdet]

/-- The explicit coefficient vector solves `Γ = eₓ + L Γ` as a corollary of the generic resummed
ladder fixed-point theorem. -/
theorem inPlaneLadderSolvedVector_fixedPoint
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0) :
    inPlaneLadderSolvedVector rung =
      inPlaneLadderBareXSource + inPlaneLadderAction rung (inPlaneLadderSolvedVector rung) := by
  have hgeneric :=
    resummedLadderVertex_fixedPoint
      (inPlaneLadderCLM rung) (inPlaneLadderShift_isUnit rung hdet)
      inPlaneLadderBareXSource
  rw [← inPlaneLadderSolvedVector_eq_resummedLadderVertex rung hdet] at hgeneric
  simpa only [inPlaneLadderCLM_apply] using hgeneric

/-- The in-plane fixed point is unique under the same nonzero-determinant hypothesis, by generic
ladder uniqueness. -/
theorem inPlaneLadder_fixedPoint_unique
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0)
    (coefficients : InPlaneCoefficientVector)
    (hfixed : coefficients =
      inPlaneLadderBareXSource + inPlaneLadderAction rung coefficients) :
    coefficients = inPlaneLadderSolvedVector rung := by
  rw [inPlaneLadderSolvedVector_eq_resummedLadderVertex rung hdet]
  exact
    eq_resummedLadderVertex_of_fixedPoint
      (inPlaneLadderCLM rung) (inPlaneLadderShift_isUnit rung hdet)
      inPlaneLadderBareXSource coefficients
      (by simpa only [inPlaneLadderCLM_apply] using hfixed)

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

end QuantumTheory.Transport.Models.MassiveDirac
