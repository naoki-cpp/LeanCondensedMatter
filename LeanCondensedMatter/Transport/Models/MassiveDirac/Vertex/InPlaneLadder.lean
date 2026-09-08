import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option linter.style.header false

/-!
# In-plane massive-Dirac ladder coefficient algebra

This module owns the exact two-component algebra needed once a massive-Dirac retarded-advanced
current rung has been reduced to the in-plane Pauli span. For the repository orientation
`Gᴿ Γ Gᴬ`, supplied complex rung coefficients `X` and `Y` act through the matrix

```text
[[X, -Y], [Y, X]].
```

The bare-`σₓ` fixed point is solved as one `Fin 2 → ℂ` coefficient vector. Coordinate projections
remain available where downstream physics needs a concrete `x` or `y` component, but the fixed-point
and uniqueness statements are vector equations. This file does not define the Born-Dyson momentum
integrals that supply `X` and `Y`, take any broadening/disorder limit, identify a transport lifetime,
or insert the result into conductivity.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter

/-- Entry `(i,j)` of the repository-oriented isotropic in-plane map `[[x,-y],[y,x]]`, with `i`
the output direction and `j` the input/source direction. -/
def inPlaneRotationCoefficient (x y : ℂ) : Direction2 → Direction2 → ℂ
  | .x, .x => x
  | .x, .y => -y
  | .y, .x => y
  | .y, .y => x

/-- Convergence of the two independent isotropic coefficients propagates to every matrix entry. -/
theorem tendsto_inPlaneRotationCoefficient
    {ι : Type*} {l : Filter ι} {x y : ι → ℂ} {x₀ y₀ : ℂ}
    (hx : Tendsto x l (nhds x₀)) (hy : Tendsto y l (nhds y₀))
    (i j : Direction2) :
    Tendsto (fun a => inPlaneRotationCoefficient (x a) (y a) i j) l
      (nhds (inPlaneRotationCoefficient x₀ y₀ i j)) := by
  cases i <;> cases j <;> simp only [inPlaneRotationCoefficient]
  all_goals first | exact hx | exact hy.neg | exact hy

/-- Two complex coefficients in the ordered in-plane basis `(σₓ, σᵧ)`. -/
abbrev InPlaneCoefficientVector := Fin 2 → ℂ

/-- In-plane coefficient vector with ordered entries `(x,y)`. -/
def inPlaneCoefficientVector (x y : ℂ) : InPlaneCoefficientVector :=
  ![x, y]

/-- Repository-oriented isotropic in-plane matrix `[[x,-y],[y,x]]`. -/
def inPlaneRotationMatrix (x y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![x, -y; y, x]

/-- The isotropic in-plane matrix acts simultaneously on both coefficient components. -/
theorem inPlaneRotationMatrix_mulVec_inPlaneCoefficientVector
    (x y alpha beta : ℂ) :
    (inPlaneRotationMatrix x y).mulVec (inPlaneCoefficientVector alpha beta) =
      inPlaneCoefficientVector (x * alpha - y * beta) (y * alpha + x * beta) := by
  funext i
  fin_cases i <;>
    simp [inPlaneRotationMatrix, inPlaneCoefficientVector] <;>
    ring_nf

/-- Repository-oriented in-plane ladder action on the complete coefficient vector. -/
def inPlaneLadderAction
    (x y : ℂ) (coefficients : InPlaneCoefficientVector) : InPlaneCoefficientVector :=
  (inPlaneRotationMatrix x y).mulVec coefficients

/-- Determinant of the shifted two-component ladder equation `I - L`. -/
def inPlaneLadderDeterminant (x y : ℂ) : ℂ :=
  (1 - x) ^ 2 + y ^ 2

/-- Shifted ladder matrix `I - L`. -/
def inPlaneLadderShiftedMatrix (x y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 - x, y; -y, 1 - x]

@[simp]
theorem inPlaneLadderShiftedMatrix_det (x y : ℂ) :
    (inPlaneLadderShiftedMatrix x y).det = inPlaneLadderDeterminant x y := by
  simp [inPlaneLadderShiftedMatrix, inPlaneLadderDeterminant, Matrix.det_fin_two, pow_two]

/-- The shifted ladder matrix is `I - L`. -/
theorem inPlaneLadderShiftedMatrix_eq_one_sub (x y : ℂ) :
    inPlaneLadderShiftedMatrix x y = 1 - inPlaneRotationMatrix x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [inPlaneLadderShiftedMatrix, inPlaneRotationMatrix]

/-- Bare `σₓ` source represented as one in-plane coefficient vector. -/
def inPlaneLadderBareXSource : InPlaneCoefficientVector :=
  inPlaneCoefficientVector 1 0

/-- Exact coefficient vector of the bare-`σₓ` ladder fixed point. -/
def inPlaneLadderSolvedVector (x y : ℂ) : InPlaneCoefficientVector :=
  inPlaneCoefficientVector
    ((1 - x) / inPlaneLadderDeterminant x y)
    (y / inPlaneLadderDeterminant x y)

/-- Longitudinal coordinate projection of the canonical solved vector. -/
def inPlaneLadderSolvedXCoefficient (x y : ℂ) : ℂ :=
  inPlaneLadderSolvedVector x y 0

/-- Transverse coordinate projection of the canonical solved vector. -/
def inPlaneLadderSolvedYCoefficient (x y : ℂ) : ℂ :=
  inPlaneLadderSolvedVector x y 1

/-- Output coordinate of the bare-`σₓ` solved ladder fixed point. -/
def inPlaneLadderSolvedCoefficient
    (output : Direction2) (x y : ℂ) : ℂ :=
  inPlaneRotationCoefficient
    (inPlaneLadderSolvedXCoefficient x y)
    (inPlaneLadderSolvedYCoefficient x y)
    output .x

/-- Convergence of the rung invariants propagates to every output coordinate of the solved ladder
whenever the limiting shifted-ladder determinant is nonzero. -/
theorem tendsto_inPlaneLadderSolvedCoefficient
    {ι : Type*} {l : Filter ι} {x y : ι → ℂ} {x₀ y₀ : ℂ}
    (hx : Tendsto x l (nhds x₀)) (hy : Tendsto y l (nhds y₀))
    (hdet : inPlaneLadderDeterminant x₀ y₀ ≠ 0)
    (output : Direction2) :
    Tendsto
      (fun a => inPlaneLadderSolvedCoefficient output (x a) (y a))
      l (nhds (inPlaneLadderSolvedCoefficient output x₀ y₀)) := by
  have hOne : Tendsto (fun _ : ι => (1 : ℂ)) l (nhds 1) := tendsto_const_nhds
  have hOneMinusX := hOne.sub hx
  have hdetLimit :
      Tendsto (fun a => inPlaneLadderDeterminant (x a) (y a)) l
        (nhds (inPlaneLadderDeterminant x₀ y₀)) := by
    simpa [inPlaneLadderDeterminant, pow_two] using
      (hOneMinusX.mul hOneMinusX).add (hy.mul hy)
  cases output
  · simpa [inPlaneLadderSolvedCoefficient, inPlaneLadderSolvedXCoefficient,
      inPlaneLadderSolvedVector, inPlaneCoefficientVector, inPlaneRotationCoefficient,
      div_eq_mul_inv] using hOneMinusX.mul (hdetLimit.inv₀ hdet)
  · simpa [inPlaneLadderSolvedCoefficient, inPlaneLadderSolvedYCoefficient,
      inPlaneLadderSolvedVector, inPlaneCoefficientVector, inPlaneRotationCoefficient,
      div_eq_mul_inv] using hy.mul (hdetLimit.inv₀ hdet)

/-- The explicit coefficient vector solves `Γ = eₓ + L Γ` whenever `I - L` has nonzero
determinant. -/
theorem inPlaneLadderSolvedVector_fixedPoint
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedVector x y =
      inPlaneLadderBareXSource + inPlaneLadderAction x y (inPlaneLadderSolvedVector x y) := by
  rw [inPlaneLadderAction, inPlaneLadderSolvedVector,
    inPlaneRotationMatrix_mulVec_inPlaneCoefficientVector]
  funext i
  fin_cases i
  · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector]
    field_simp [hdet] <;> ring
  · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector]
    field_simp [hdet] <;> ring

/-- The in-plane fixed point is unique under the same nonzero-determinant hypothesis. -/
theorem inPlaneLadder_fixedPoint_unique
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0)
    (coefficients : InPlaneCoefficientVector)
    (hfixed : coefficients =
      inPlaneLadderBareXSource + inPlaneLadderAction x y coefficients) :
    coefficients = inPlaneLadderSolvedVector x y := by
  have hfixedShift :
      coefficients - inPlaneLadderAction x y coefficients = inPlaneLadderBareXSource := by
    calc
      coefficients - inPlaneLadderAction x y coefficients =
          (inPlaneLadderBareXSource + inPlaneLadderAction x y coefficients) -
            inPlaneLadderAction x y coefficients :=
        congrArg (fun value => value - inPlaneLadderAction x y coefficients) hfixed
      _ = inPlaneLadderBareXSource := by abel
  have hsolvedFixed := inPlaneLadderSolvedVector_fixedPoint x y hdet
  have hsolvedShift :
      inPlaneLadderSolvedVector x y -
          inPlaneLadderAction x y (inPlaneLadderSolvedVector x y) =
        inPlaneLadderBareXSource := by
    calc
      inPlaneLadderSolvedVector x y -
          inPlaneLadderAction x y (inPlaneLadderSolvedVector x y) =
        (inPlaneLadderBareXSource +
            inPlaneLadderAction x y (inPlaneLadderSolvedVector x y)) -
          inPlaneLadderAction x y (inPlaneLadderSolvedVector x y) :=
        congrArg
          (fun value => value - inPlaneLadderAction x y (inPlaneLadderSolvedVector x y))
          hsolvedFixed
      _ = inPlaneLadderBareXSource := by abel
  have hshifted :
      (inPlaneLadderShiftedMatrix x y).mulVec coefficients = inPlaneLadderBareXSource := by
    rw [inPlaneLadderShiftedMatrix_eq_one_sub, Matrix.sub_mulVec, Matrix.one_mulVec]
    simpa [inPlaneLadderAction] using hfixedShift
  have hsolvedShifted :
      (inPlaneLadderShiftedMatrix x y).mulVec (inPlaneLadderSolvedVector x y) =
        inPlaneLadderBareXSource := by
    rw [inPlaneLadderShiftedMatrix_eq_one_sub, Matrix.sub_mulVec, Matrix.one_mulVec]
    simpa [inPlaneLadderAction] using hsolvedShift
  have hunit : IsUnit (inPlaneLadderShiftedMatrix x y) :=
    (Matrix.isUnit_iff_isUnit_det _).2 <| by
      rw [inPlaneLadderShiftedMatrix_det]
      exact isUnit_iff_ne_zero.2 hdet
  exact Matrix.mulVec_injective_iff_isUnit.2 hunit (hshifted.trans hsolvedShifted.symm)

/-- With no transverse rung mixing, the vector solution reduces to the scalar ladder factor in the
longitudinal component and zero in the transverse component. -/
theorem inPlaneLadderSolvedVector_zero_transverse
    (x : ℂ) (hx : 1 - x ≠ 0) :
    inPlaneLadderSolvedVector x 0 = inPlaneCoefficientVector (1 - x)⁻¹ 0 := by
  funext i
  fin_cases i
  · simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector, inPlaneLadderDeterminant]
    field_simp [hx]
  · simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector]

end

end QuantumTheory.Transport.Models.MassiveDirac
