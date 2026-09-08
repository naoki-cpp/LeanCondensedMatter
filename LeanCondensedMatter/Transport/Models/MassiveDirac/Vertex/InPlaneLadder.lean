import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
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

The bare-`σₓ` fixed point is solved as one `Direction2 → ℂ` coefficient vector. Coordinate
projections remain available where downstream physics needs a concrete `x` or `y` component, but
the fixed-point and uniqueness statements are vector equations. This file does not define the
Born-Dyson momentum integrals that supply `X` and `Y`, take any broadening/disorder limit, identify a
transport lifetime, or insert the result into conductivity.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter

private theorem sum_direction2 {M : Type*} [AddCommMonoid M] (f : Direction2 → M) :
    ∑ direction : Direction2, f direction = f .x + f .y := by
  change ∑ direction ∈ ({.x, .y} : Finset Direction2), f direction = _
  simp

/-- Two complex coefficients indexed by the semantic in-plane direction. -/
abbrev InPlaneCoefficientVector := Direction2 → ℂ

/-- In-plane coefficient vector with components `(x,y)`. -/
def inPlaneCoefficientVector (x y : ℂ) : InPlaneCoefficientVector
  | .x => x
  | .y => y

/-- Repository-oriented isotropic in-plane matrix `[[x,-y],[y,x]]`. -/
def inPlaneRotationMatrix (x y : ℂ) : Matrix Direction2 Direction2 ℂ
  | .x, .x => x
  | .x, .y => -y
  | .y, .x => y
  | .y, .y => x

@[simp]
theorem inPlaneRotationMatrix_apply_zero_zero (x y : ℂ) :
    inPlaneRotationMatrix x y .x .x = x := by
  rfl

@[simp]
theorem inPlaneRotationMatrix_apply_zero_one (x y : ℂ) :
    inPlaneRotationMatrix x y .x .y = -y := by
  rfl

@[simp]
theorem inPlaneRotationMatrix_apply_one_zero (x y : ℂ) :
    inPlaneRotationMatrix x y .y .x = y := by
  rfl

@[simp]
theorem inPlaneRotationMatrix_apply_one_one (x y : ℂ) :
    inPlaneRotationMatrix x y .y .y = x := by
  rfl

/-- Entry `(i,j)` of the canonical repository-oriented in-plane matrix, with `i` the output
direction and `j` the input/source direction. -/
def inPlaneRotationCoefficient (x y : ℂ) (i j : Direction2) : ℂ :=
  inPlaneRotationMatrix x y i j

/-- Convergence of the two independent isotropic coefficients propagates to every matrix entry. -/
theorem tendsto_inPlaneRotationCoefficient
    {ι : Type*} {l : Filter ι} {x y : ι → ℂ} {x₀ y₀ : ℂ}
    (hx : Tendsto x l (nhds x₀)) (hy : Tendsto y l (nhds y₀))
    (i j : Direction2) :
    Tendsto (fun a => inPlaneRotationCoefficient (x a) (y a) i j) l
      (nhds (inPlaneRotationCoefficient x₀ y₀ i j)) := by
  cases i <;> cases j
  · simpa [inPlaneRotationCoefficient, inPlaneRotationMatrix] using hx
  · simpa [inPlaneRotationCoefficient, inPlaneRotationMatrix] using hy.neg
  · simpa [inPlaneRotationCoefficient, inPlaneRotationMatrix] using hy
  · simpa [inPlaneRotationCoefficient, inPlaneRotationMatrix] using hx

/-- The isotropic in-plane matrix acts simultaneously on both coefficient components. -/
theorem inPlaneRotationMatrix_mulVec_inPlaneCoefficientVector
    (x y alpha beta : ℂ) :
    (inPlaneRotationMatrix x y).mulVec (inPlaneCoefficientVector alpha beta) =
      inPlaneCoefficientVector (x * alpha - y * beta) (y * alpha + x * beta) := by
  funext direction
  cases direction <;>
    simp [Matrix.mulVec, dotProduct, sum_direction2, inPlaneRotationMatrix,
      inPlaneCoefficientVector] <;>
    ring

/-- Repository-oriented in-plane ladder action on the complete coefficient vector. -/
def inPlaneLadderAction
    (x y : ℂ) (coefficients : InPlaneCoefficientVector) : InPlaneCoefficientVector :=
  (inPlaneRotationMatrix x y).mulVec coefficients

@[simp]
theorem inPlaneLadderAction_apply_x
    (x y : ℂ) (coefficients : InPlaneCoefficientVector) :
    inPlaneLadderAction x y coefficients .x =
      x * coefficients .x - y * coefficients .y := by
  simp [inPlaneLadderAction, Matrix.mulVec, dotProduct, sum_direction2,
    inPlaneRotationMatrix]
  ring

@[simp]
theorem inPlaneLadderAction_apply_y
    (x y : ℂ) (coefficients : InPlaneCoefficientVector) :
    inPlaneLadderAction x y coefficients .y =
      y * coefficients .x + x * coefficients .y := by
  simp [inPlaneLadderAction, Matrix.mulVec, dotProduct, sum_direction2,
    inPlaneRotationMatrix]
  ring

/-- Determinant of the shifted two-component ladder equation `I - L`. -/
def inPlaneLadderDeterminant (x y : ℂ) : ℂ :=
  (1 - x) ^ 2 + y ^ 2

/-- Bare `σₓ` source represented as one in-plane coefficient vector. -/
def inPlaneLadderBareXSource : InPlaneCoefficientVector :=
  inPlaneCoefficientVector 1 0

/-- Exact coefficient vector of the bare-`σₓ` ladder fixed point. -/
def inPlaneLadderSolvedVector (x y : ℂ) : InPlaneCoefficientVector :=
  inPlaneCoefficientVector
    ((1 - x) / inPlaneLadderDeterminant x y)
    (y / inPlaneLadderDeterminant x y)

@[simp]
theorem inPlaneLadderSolvedVector_apply_zero (x y : ℂ) :
    inPlaneLadderSolvedVector x y .x = (1 - x) / inPlaneLadderDeterminant x y := by
  rfl

@[simp]
theorem inPlaneLadderSolvedVector_apply_one (x y : ℂ) :
    inPlaneLadderSolvedVector x y .y = y / inPlaneLadderDeterminant x y := by
  rfl

/-- Longitudinal coordinate projection of the canonical solved vector. -/
def inPlaneLadderSolvedXCoefficient (x y : ℂ) : ℂ :=
  inPlaneLadderSolvedVector x y .x

/-- Transverse coordinate projection of the canonical solved vector. -/
def inPlaneLadderSolvedYCoefficient (x y : ℂ) : ℂ :=
  inPlaneLadderSolvedVector x y .y

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
  have hAlpha :
      Tendsto
        (fun a => inPlaneLadderSolvedXCoefficient (x a) (y a)) l
        (nhds (inPlaneLadderSolvedXCoefficient x₀ y₀)) := by
    simpa [inPlaneLadderSolvedXCoefficient, div_eq_mul_inv] using
      hOneMinusX.mul (hdetLimit.inv₀ hdet)
  have hBeta :
      Tendsto
        (fun a => inPlaneLadderSolvedYCoefficient (x a) (y a)) l
        (nhds (inPlaneLadderSolvedYCoefficient x₀ y₀)) := by
    simpa [inPlaneLadderSolvedYCoefficient, div_eq_mul_inv] using
      hy.mul (hdetLimit.inv₀ hdet)
  simpa [inPlaneLadderSolvedCoefficient] using
    tendsto_inPlaneRotationCoefficient hAlpha hBeta output .x

/-- The explicit coefficient vector solves `Γ = eₓ + L Γ` whenever `I - L` has nonzero
determinant. -/
theorem inPlaneLadderSolvedVector_fixedPoint
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedVector x y =
      inPlaneLadderBareXSource + inPlaneLadderAction x y (inPlaneLadderSolvedVector x y) := by
  rw [inPlaneLadderAction, inPlaneLadderSolvedVector,
    inPlaneRotationMatrix_mulVec_inPlaneCoefficientVector]
  funext direction
  cases direction
  · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector]
    field_simp [hdet]
    unfold inPlaneLadderDeterminant
    ring
  · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector]
    field_simp [hdet]
    ring

/-- The in-plane fixed point is unique under the same nonzero-determinant hypothesis. -/
theorem inPlaneLadder_fixedPoint_unique
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0)
    (coefficients : InPlaneCoefficientVector)
    (hfixed : coefficients =
      inPlaneLadderBareXSource + inPlaneLadderAction x y coefficients) :
    coefficients = inPlaneLadderSolvedVector x y := by
  have hxFixed := congrArg (fun values : InPlaneCoefficientVector => values .x) hfixed
  have hyFixed := congrArg (fun values : InPlaneCoefficientVector => values .y) hfixed
  simp [inPlaneLadderBareXSource, inPlaneCoefficientVector] at hxFixed hyFixed
  have hxLinear :
      (1 - x) * coefficients .x + y * coefficients .y = 1 := by
    calc
      (1 - x) * coefficients .x + y * coefficients .y =
          coefficients .x - (x * coefficients .x - y * coefficients .y) := by ring
      _ = 1 := by rw [hxFixed]; ring
  have hyLinear :
      -y * coefficients .x + (1 - x) * coefficients .y = 0 := by
    calc
      -y * coefficients .x + (1 - x) * coefficients .y =
          coefficients .y - (y * coefficients .x + x * coefficients .y) := by ring
      _ = 0 := by rw [hyFixed]; ring
  have hxDet :
      inPlaneLadderDeterminant x y * coefficients .x = 1 - x := by
    calc
      inPlaneLadderDeterminant x y * coefficients .x =
          (1 - x) * ((1 - x) * coefficients .x + y * coefficients .y) -
            y * (-y * coefficients .x + (1 - x) * coefficients .y) := by
              unfold inPlaneLadderDeterminant
              ring
      _ = 1 - x := by rw [hxLinear, hyLinear]; ring
  have hyDet :
      inPlaneLadderDeterminant x y * coefficients .y = y := by
    calc
      inPlaneLadderDeterminant x y * coefficients .y =
          y * ((1 - x) * coefficients .x + y * coefficients .y) +
            (1 - x) * (-y * coefficients .x + (1 - x) * coefficients .y) := by
              unfold inPlaneLadderDeterminant
              ring
      _ = y := by rw [hxLinear, hyLinear]; ring
  funext direction
  cases direction
  · rw [inPlaneLadderSolvedVector_apply_zero]
    apply (eq_div_iff hdet).2
    simpa [mul_comm] using hxDet
  · rw [inPlaneLadderSolvedVector_apply_one]
    apply (eq_div_iff hdet).2
    simpa [mul_comm] using hyDet

/-- With no transverse rung mixing, the vector solution reduces to the scalar ladder factor in the
longitudinal component and zero in the transverse component. -/
theorem inPlaneLadderSolvedVector_zero_transverse
    (x : ℂ) (hx : 1 - x ≠ 0) :
    inPlaneLadderSolvedVector x 0 = inPlaneCoefficientVector (1 - x)⁻¹ 0 := by
  funext direction
  cases direction
  · simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector, inPlaneLadderDeterminant]
    field_simp [hx]
  · simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector]

end

end QuantumTheory.Transport.Models.MassiveDirac
