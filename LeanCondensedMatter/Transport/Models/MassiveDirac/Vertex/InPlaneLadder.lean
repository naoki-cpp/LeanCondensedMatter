import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# In-plane massive-Dirac ladder coefficient algebra

This module owns only the exact two-component algebra needed once a massive-Dirac retarded-advanced
current rung has been reduced to the in-plane Pauli span.  For the repository orientation
`Gᴿ Γ Gᴬ`, supplied complex rung coefficients `X` and `Y` act as

```text
L(α σₓ + β σᵧ)
  = (X α - Y β) σₓ + (Y α + X β) σᵧ.
```

The fixed point is solved for an arbitrary in-plane source `a σₓ + b σᵧ` under the visible
nonzero-determinant hypothesis.  The bare longitudinal and transverse sources are then canonical
specializations.  This file does not define the Born-Dyson momentum integrals that supply `X` and
`Y`, take any broadening/disorder limit, identify a transport lifetime, or insert the result into
conductivity.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- `σₓ` coefficient of the repository-oriented in-plane ladder action. -/
def inPlaneLadderXCoefficient
    (x y alpha beta : ℂ) : ℂ :=
  x * alpha - y * beta

/-- `σᵧ` coefficient of the repository-oriented in-plane ladder action. -/
def inPlaneLadderYCoefficient
    (x y alpha beta : ℂ) : ℂ :=
  y * alpha + x * beta

/-- Bounded-operator realization of the in-plane ladder action with supplied rung coefficients.
The sign of the transverse mixing is tied to the repository orientation `Gᴿ Γ Gᴬ`. -/
noncomputable def inPlaneLadderOperatorAction
    (x y alpha beta : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneLadderXCoefficient x y alpha beta • matrixOperator sigmaX +
    inPlaneLadderYCoefficient x y alpha beta • matrixOperator sigmaY

/-- Determinant of the shifted two-component ladder equation `I - L`. -/
def inPlaneLadderDeterminant (x y : ℂ) : ℂ :=
  (1 - x) ^ 2 + y ^ 2

/-- Exact `σₓ` coefficient of the ladder fixed point for an arbitrary in-plane source. -/
def inPlaneLadderSolvedXCoefficientForSource
    (x y sourceX sourceY : ℂ) : ℂ :=
  ((1 - x) * sourceX - y * sourceY) / inPlaneLadderDeterminant x y

/-- Exact `σᵧ` coefficient of the ladder fixed point for an arbitrary in-plane source. -/
def inPlaneLadderSolvedYCoefficientForSource
    (x y sourceX sourceY : ℂ) : ℂ :=
  (y * sourceX + (1 - x) * sourceY) / inPlaneLadderDeterminant x y

/-- Exact `σₓ` coefficient of the bare-`σₓ` ladder fixed point. -/
def inPlaneLadderSolvedXCoefficient (x y : ℂ) : ℂ :=
  inPlaneLadderSolvedXCoefficientForSource x y 1 0

/-- Exact orientation-sensitive `σᵧ` coefficient of the bare-`σₓ` ladder fixed point. -/
def inPlaneLadderSolvedYCoefficient (x y : ℂ) : ℂ :=
  inPlaneLadderSolvedYCoefficientForSource x y 1 0

/-- The solved longitudinal coefficient for a supplied source satisfies its scalar fixed-point
equation. -/
theorem inPlaneLadderSolvedXCoefficientForSource_fixedPoint
    (x y sourceX sourceY : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY =
      sourceX + inPlaneLadderXCoefficient x y
        (inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY)
        (inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY) := by
  unfold inPlaneLadderSolvedXCoefficientForSource
    inPlaneLadderSolvedYCoefficientForSource inPlaneLadderXCoefficient
  unfold inPlaneLadderDeterminant at hdet ⊢
  field_simp [hdet]
  ring

/-- The solved transverse coefficient for a supplied source satisfies its scalar fixed-point
equation. -/
theorem inPlaneLadderSolvedYCoefficientForSource_fixedPoint
    (x y sourceX sourceY : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY =
      sourceY + inPlaneLadderYCoefficient x y
        (inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY)
        (inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY) := by
  unfold inPlaneLadderSolvedXCoefficientForSource
    inPlaneLadderSolvedYCoefficientForSource inPlaneLadderYCoefficient
  unfold inPlaneLadderDeterminant at hdet ⊢
  field_simp [hdet]
  ring

/-- The solved longitudinal coefficient satisfies the bare-`σₓ` fixed-point equation. -/
theorem inPlaneLadderSolvedXCoefficient_fixedPoint
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedXCoefficient x y =
      1 + inPlaneLadderXCoefficient x y
        (inPlaneLadderSolvedXCoefficient x y)
        (inPlaneLadderSolvedYCoefficient x y) := by
  simpa [inPlaneLadderSolvedXCoefficient, inPlaneLadderSolvedYCoefficient] using
    inPlaneLadderSolvedXCoefficientForSource_fixedPoint x y 1 0 hdet

/-- The solved transverse coefficient satisfies the bare-`σₓ` fixed-point equation. -/
theorem inPlaneLadderSolvedYCoefficient_fixedPoint
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedYCoefficient x y =
      inPlaneLadderYCoefficient x y
        (inPlaneLadderSolvedXCoefficient x y)
        (inPlaneLadderSolvedYCoefficient x y) := by
  simpa [inPlaneLadderSolvedXCoefficient, inPlaneLadderSolvedYCoefficient] using
    inPlaneLadderSolvedYCoefficientForSource_fixedPoint x y 1 0 hdet

/-- Bounded in-plane Pauli vertex corresponding to the exact solved coefficients for an arbitrary
in-plane source. -/
noncomputable def inPlaneLadderSolvedVertexForSource
    (x y sourceX sourceY : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY • matrixOperator sigmaX +
    inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY • matrixOperator sigmaY

/-- Bounded in-plane Pauli vertex for a bare `σₓ` source. -/
noncomputable def inPlaneLadderSolvedVertex
    (x y : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneLadderSolvedVertexForSource x y 1 0

/-- Bounded in-plane Pauli vertex for a bare `σᵧ` source. -/
noncomputable def inPlaneLadderSolvedTransverseVertex
    (x y : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneLadderSolvedVertexForSource x y 0 1

/-- The explicit in-plane vertex solves `Γ = Γ₀ + L(Γ)` for an arbitrary source whenever `I - L`
has nonzero coefficient determinant. -/
theorem inPlaneLadderSolvedVertexForSource_fixedPoint
    (x y sourceX sourceY : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedVertexForSource x y sourceX sourceY =
      sourceX • matrixOperator sigmaX + sourceY • matrixOperator sigmaY +
        inPlaneLadderOperatorAction x y
          (inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY)
          (inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY) := by
  have hX := inPlaneLadderSolvedXCoefficientForSource_fixedPoint
    x y sourceX sourceY hdet
  have hY := inPlaneLadderSolvedYCoefficientForSource_fixedPoint
    x y sourceX sourceY hdet
  have hXsmul := congrArg
    (fun coefficient : ℂ => coefficient • matrixOperator sigmaX) hX
  have hYsmul := congrArg
    (fun coefficient : ℂ => coefficient • matrixOperator sigmaY) hY
  unfold inPlaneLadderSolvedVertexForSource inPlaneLadderOperatorAction
  calc
    inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY • matrixOperator sigmaX +
        inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY • matrixOperator sigmaY =
      (sourceX + inPlaneLadderXCoefficient x y
          (inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY)
          (inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY)) • matrixOperator sigmaX +
        (sourceY + inPlaneLadderYCoefficient x y
          (inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY)
          (inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY)) • matrixOperator sigmaY := by
      rw [hXsmul, hYsmul]
    _ = sourceX • matrixOperator sigmaX + sourceY • matrixOperator sigmaY +
        (inPlaneLadderXCoefficient x y
            (inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY)
            (inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY) • matrixOperator sigmaX +
          inPlaneLadderYCoefficient x y
            (inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY)
            (inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY) • matrixOperator sigmaY) := by
      module

/-- The explicit bare-`σₓ` vertex solves `Γ = σₓ + L(Γ)` exactly whenever `I - L` has nonzero
coefficient determinant. -/
theorem inPlaneLadderSolvedVertex_fixedPoint
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedVertex x y =
      matrixOperator sigmaX +
        inPlaneLadderOperatorAction x y
          (inPlaneLadderSolvedXCoefficient x y)
          (inPlaneLadderSolvedYCoefficient x y) := by
  simpa [inPlaneLadderSolvedVertex, inPlaneLadderSolvedXCoefficient,
    inPlaneLadderSolvedYCoefficient] using
    inPlaneLadderSolvedVertexForSource_fixedPoint x y 1 0 hdet

/-- The coefficient representation of the arbitrary-source in-plane fixed point is unique under
the same determinant hypothesis. -/
theorem inPlaneLadder_fixedPoint_coefficientsForSource_unique
    (x y sourceX sourceY alpha beta : ℂ)
    (hdet : inPlaneLadderDeterminant x y ≠ 0)
    (hX : alpha = sourceX + inPlaneLadderXCoefficient x y alpha beta)
    (hY : beta = sourceY + inPlaneLadderYCoefficient x y alpha beta) :
    alpha = inPlaneLadderSolvedXCoefficientForSource x y sourceX sourceY ∧
      beta = inPlaneLadderSolvedYCoefficientForSource x y sourceX sourceY := by
  unfold inPlaneLadderXCoefficient at hX
  unfold inPlaneLadderYCoefficient at hY
  have hxlin : (1 - x) * alpha + y * beta = sourceX := by
    linear_combination hX
  have hylin : -y * alpha + (1 - x) * beta = sourceY := by
    linear_combination hY
  have halphaRaw :
      ((1 - x) ^ 2 + y ^ 2) * alpha = (1 - x) * sourceX - y * sourceY := by
    linear_combination (1 - x) * hxlin - y * hylin
  have hbetaRaw :
      ((1 - x) ^ 2 + y ^ 2) * beta = y * sourceX + (1 - x) * sourceY := by
    linear_combination y * hxlin + (1 - x) * hylin
  have halpha :
      inPlaneLadderDeterminant x y * alpha = (1 - x) * sourceX - y * sourceY := by
    simpa [inPlaneLadderDeterminant] using halphaRaw
  have hbeta :
      inPlaneLadderDeterminant x y * beta = y * sourceX + (1 - x) * sourceY := by
    simpa [inPlaneLadderDeterminant] using hbetaRaw
  constructor
  · unfold inPlaneLadderSolvedXCoefficientForSource
    apply (eq_div_iff hdet).2
    simpa [mul_comm] using halpha
  · unfold inPlaneLadderSolvedYCoefficientForSource
    apply (eq_div_iff hdet).2
    simpa [mul_comm] using hbeta

/-- The coefficient representation of the bare-`σₓ` fixed point is unique under the same determinant
hypothesis. -/
theorem inPlaneLadder_fixedPoint_coefficients_unique
    (x y alpha beta : ℂ)
    (hdet : inPlaneLadderDeterminant x y ≠ 0)
    (hX : alpha = 1 + inPlaneLadderXCoefficient x y alpha beta)
    (hY : beta = inPlaneLadderYCoefficient x y alpha beta) :
    alpha = inPlaneLadderSolvedXCoefficient x y ∧
      beta = inPlaneLadderSolvedYCoefficient x y := by
  simpa [inPlaneLadderSolvedXCoefficient, inPlaneLadderSolvedYCoefficient] using
    inPlaneLadder_fixedPoint_coefficientsForSource_unique
      x y 1 0 alpha beta hdet hX (by simpa using hY)

@[simp] theorem inPlaneLadderSolvedYCoefficient_zero
    (x : ℂ) :
    inPlaneLadderSolvedYCoefficient x 0 = 0 := by
  simp [inPlaneLadderSolvedYCoefficient, inPlaneLadderSolvedYCoefficientForSource]

@[simp] theorem inPlaneLadderSolvedTransverseVertex_zero_rung :
    inPlaneLadderSolvedTransverseVertex 0 0 = matrixOperator sigmaY := by
  simp [inPlaneLadderSolvedTransverseVertex, inPlaneLadderSolvedVertexForSource,
    inPlaneLadderSolvedXCoefficientForSource, inPlaneLadderSolvedYCoefficientForSource,
    inPlaneLadderDeterminant]

/-- With no transverse rung mixing, the two-component solution reduces to the familiar scalar
ladder factor `(1 - X)⁻¹`. -/
theorem inPlaneLadderSolvedXCoefficient_zero
    (x : ℂ) (hx : 1 - x ≠ 0) :
    inPlaneLadderSolvedXCoefficient x 0 = (1 - x)⁻¹ := by
  unfold inPlaneLadderSolvedXCoefficient inPlaneLadderSolvedXCoefficientForSource
    inPlaneLadderDeterminant
  field_simp [hx]
  ring

end

end AnomalousHall.MassiveDirac
