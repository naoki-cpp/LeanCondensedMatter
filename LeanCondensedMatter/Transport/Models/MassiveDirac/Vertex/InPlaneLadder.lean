import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
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
the canonical action, determinant, fixed-point, and convergence statements consume the complete
vector. This file does not define the Born-Dyson momentum integrals that supply the rung, take any
broadening/disorder limit, identify a transport lifetime, or insert the result into conductivity.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter

/-- Two complex coefficients indexed by the in-plane Cartesian directions. -/
abbrev InPlaneCoefficientVector := Direction2 → ℂ

/-- In-plane coefficient vector with components `(x,y)`. -/
def inPlaneCoefficientVector (x y : ℂ) : InPlaneCoefficientVector := ![x, y]

/-- Repository-oriented isotropic in-plane matrix derived from a rung vector `(X,Y)`. -/
def inPlaneRotationMatrix (rung : InPlaneCoefficientVector) : Matrix Direction2 Direction2 ℂ :=
  !![rung .x, -(rung .y); rung .y, rung .x]

@[simp] theorem inPlaneRotationMatrix_apply_x_x (rung : InPlaneCoefficientVector) :
    inPlaneRotationMatrix rung .x .x = rung .x := by
  simp [inPlaneRotationMatrix, Direction2.x]

@[simp] theorem inPlaneRotationMatrix_apply_x_y (rung : InPlaneCoefficientVector) :
    inPlaneRotationMatrix rung .x .y = -(rung .y) := by
  simp [inPlaneRotationMatrix, Direction2.x, Direction2.y]

@[simp] theorem inPlaneRotationMatrix_apply_y_x (rung : InPlaneCoefficientVector) :
    inPlaneRotationMatrix rung .y .x = rung .y := by
  simp [inPlaneRotationMatrix, Direction2.x, Direction2.y]

@[simp] theorem inPlaneRotationMatrix_apply_y_y (rung : InPlaneCoefficientVector) :
    inPlaneRotationMatrix rung .y .y = rung .x := by
  simp [inPlaneRotationMatrix, Direction2.x, Direction2.y]

/-- Repository-oriented in-plane ladder action on the complete coefficient vector. -/
def inPlaneLadderAction
    (rung coefficients : InPlaneCoefficientVector) : InPlaneCoefficientVector :=
  (inPlaneRotationMatrix rung).mulVec coefficients

@[simp]
theorem inPlaneLadderAction_apply_x
    (rung coefficients : InPlaneCoefficientVector) :
    inPlaneLadderAction rung coefficients .x =
      rung .x * coefficients .x - rung .y * coefficients .y := by
  simp [inPlaneLadderAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    inPlaneRotationMatrix, Direction2.x, Direction2.y, sub_eq_add_neg]

@[simp]
theorem inPlaneLadderAction_apply_y
    (rung coefficients : InPlaneCoefficientVector) :
    inPlaneLadderAction rung coefficients .y =
      rung .y * coefficients .x + rung .x * coefficients .y := by
  simp [inPlaneLadderAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    inPlaneRotationMatrix, Direction2.x, Direction2.y]

/-- Convergence of rung and coefficient vectors propagates to the complete ladder action. -/
theorem tendsto_inPlaneLadderAction
    {ι : Type*} {l : Filter ι} {rung coefficients : ι → InPlaneCoefficientVector}
    {rung₀ coefficients₀ : InPlaneCoefficientVector} (hrung : Tendsto rung l (nhds rung₀))
    (hcoefficients : Tendsto coefficients l (nhds coefficients₀)) :
    Tendsto (fun a => inPlaneLadderAction (rung a) (coefficients a)) l
      (nhds (inPlaneLadderAction rung₀ coefficients₀)) := by
  have hrx := tendsto_pi_nhds.mp hrung .x
  have hry := tendsto_pi_nhds.mp hrung .y
  have hcx := tendsto_pi_nhds.mp hcoefficients .x
  have hcy := tendsto_pi_nhds.mp hcoefficients .y
  rw [tendsto_pi_nhds]
  intro output
  fin_cases output
  · simpa only [inPlaneLadderAction_apply_x] using (hrx.mul hcx).sub (hry.mul hcy)
  · simpa only [inPlaneLadderAction_apply_y] using (hry.mul hcx).add (hrx.mul hcy)

/-- Determinant of the shifted two-component ladder equation `I - L`. -/
def inPlaneLadderDeterminant (rung : InPlaneCoefficientVector) : ℂ :=
  (1 - rung .x) ^ 2 + (rung .y) ^ 2

/-- Convergence of rung vectors propagates to the shifted-ladder determinant. -/
theorem tendsto_inPlaneLadderDeterminant
    {ι : Type*} {l : Filter ι}
    {rung : ι → InPlaneCoefficientVector} {rung₀ : InPlaneCoefficientVector}
    (hrung : Tendsto rung l (nhds rung₀)) :
    Tendsto (fun a => inPlaneLadderDeterminant (rung a)) l
      (nhds (inPlaneLadderDeterminant rung₀)) := by
  have hx := (tendsto_pi_nhds.mp hrung) .x
  have hy := (tendsto_pi_nhds.mp hrung) .y
  have hOne : Tendsto (fun _ : ι => (1 : ℂ)) l (nhds 1) := tendsto_const_nhds
  have hOneMinusX := hOne.sub hx
  simpa [inPlaneLadderDeterminant, pow_two] using
    (hOneMinusX.mul hOneMinusX).add (hy.mul hy)

/-- Bare `σₓ` source represented as one in-plane coefficient vector. -/
def inPlaneLadderBareXSource : InPlaneCoefficientVector :=
  inPlaneCoefficientVector 1 0

/-- Exact coefficient vector of the bare-`σₓ` ladder fixed point. -/
def inPlaneLadderSolvedVector (rung : InPlaneCoefficientVector) : InPlaneCoefficientVector :=
  inPlaneCoefficientVector
    ((1 - rung .x) / inPlaneLadderDeterminant rung)
    (rung .y / inPlaneLadderDeterminant rung)

@[simp] theorem inPlaneLadderSolvedVector_apply_x (rung : InPlaneCoefficientVector) :
    inPlaneLadderSolvedVector rung .x =
      (1 - rung .x) / inPlaneLadderDeterminant rung := by
  simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector, Direction2.x]

@[simp] theorem inPlaneLadderSolvedVector_apply_y (rung : InPlaneCoefficientVector) :
    inPlaneLadderSolvedVector rung .y = rung .y / inPlaneLadderDeterminant rung := by
  simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector, Direction2.y]

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
  have hx := (tendsto_pi_nhds.mp hrung) .x
  have hy := (tendsto_pi_nhds.mp hrung) .y
  have hOne : Tendsto (fun _ : ι => (1 : ℂ)) l (nhds 1) := tendsto_const_nhds
  have hOneMinusX := hOne.sub hx
  have hdetLimit := tendsto_inPlaneLadderDeterminant hrung
  rw [tendsto_pi_nhds]
  intro output
  fin_cases output
  · simpa [inPlaneLadderSolvedVector, inPlaneCoefficientVector, div_eq_mul_inv, Direction2.x] using
      hOneMinusX.mul (hdetLimit.inv₀ hdet)
  · simpa [inPlaneLadderSolvedVector, inPlaneCoefficientVector, div_eq_mul_inv, Direction2.y] using
      hy.mul (hdetLimit.inv₀ hdet)

/-- The explicit coefficient vector solves `Γ = eₓ + L Γ` whenever `I - L` has nonzero
determinant. -/
theorem inPlaneLadderSolvedVector_fixedPoint
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0) :
    inPlaneLadderSolvedVector rung =
      inPlaneLadderBareXSource + inPlaneLadderAction rung (inPlaneLadderSolvedVector rung) := by
  funext direction
  fin_cases direction
  · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector, Direction2.x,
      inPlaneLadderAction_apply_x]
    field_simp [hdet]
    unfold inPlaneLadderDeterminant
    ring
  · simp [inPlaneLadderBareXSource, inPlaneCoefficientVector, Direction2.y,
      inPlaneLadderAction_apply_y]
    field_simp [hdet]
    ring

/-- The in-plane fixed point is unique under the same nonzero-determinant hypothesis. -/
theorem inPlaneLadder_fixedPoint_unique
    (rung : InPlaneCoefficientVector) (hdet : inPlaneLadderDeterminant rung ≠ 0)
    (coefficients : InPlaneCoefficientVector)
    (hfixed : coefficients =
      inPlaneLadderBareXSource + inPlaneLadderAction rung coefficients) :
    coefficients = inPlaneLadderSolvedVector rung := by
  have hxFixed :
      coefficients .x =
        1 + (rung .x * coefficients .x - rung .y * coefficients .y) := by
    simpa [inPlaneLadderBareXSource, inPlaneCoefficientVector, Direction2.x] using
      congrArg (fun values : InPlaneCoefficientVector => values .x) hfixed
  have hyFixed :
      coefficients .y = rung .y * coefficients .x + rung .x * coefficients .y := by
    simpa [inPlaneLadderBareXSource, inPlaneCoefficientVector, Direction2.y] using
      congrArg (fun values : InPlaneCoefficientVector => values .y) hfixed
  have hxLinear :
      (1 - rung .x) * coefficients .x + rung .y * coefficients .y = 1 := by
    linear_combination hxFixed
  have hyLinear :
      -(rung .y) * coefficients .x + (1 - rung .x) * coefficients .y = 0 := by
    linear_combination hyFixed
  have hxDet :
      inPlaneLadderDeterminant rung * coefficients .x = 1 - rung .x := by
    calc
      inPlaneLadderDeterminant rung * coefficients .x =
          (1 - rung .x) *
              ((1 - rung .x) * coefficients .x + rung .y * coefficients .y) -
            rung .y *
              (-(rung .y) * coefficients .x + (1 - rung .x) * coefficients .y) := by
              unfold inPlaneLadderDeterminant
              ring
      _ = 1 - rung .x := by rw [hxLinear, hyLinear]; ring
  have hyDet :
      inPlaneLadderDeterminant rung * coefficients .y = rung .y := by
    calc
      inPlaneLadderDeterminant rung * coefficients .y =
          rung .y * ((1 - rung .x) * coefficients .x + rung .y * coefficients .y) +
            (1 - rung .x) *
              (-(rung .y) * coefficients .x + (1 - rung .x) * coefficients .y) := by
              unfold inPlaneLadderDeterminant
              ring
      _ = rung .y := by rw [hxLinear, hyLinear]; ring
  funext direction
  fin_cases direction
  · rw [inPlaneLadderSolvedVector_apply_x]
    apply (eq_div_iff hdet).2
    simpa [mul_comm] using hxDet
  · rw [inPlaneLadderSolvedVector_apply_y]
    apply (eq_div_iff hdet).2
    simpa [mul_comm] using hyDet

/-- With no transverse rung mixing, the vector solution reduces to the scalar ladder factor in the
longitudinal component and zero in the transverse component. -/
theorem inPlaneLadderSolvedVector_zero_transverse
    (x : ℂ) (hx : 1 - x ≠ 0) :
    inPlaneLadderSolvedVector (inPlaneCoefficientVector x 0) =
      inPlaneCoefficientVector (1 - x)⁻¹ 0 := by
  funext direction
  fin_cases direction
  · simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector, inPlaneLadderDeterminant,
      Direction2.x]
    field_simp [hx]
  · simp [inPlaneLadderSolvedVector, inPlaneCoefficientVector, Direction2.y]

end

end QuantumTheory.Transport.Models.MassiveDirac
