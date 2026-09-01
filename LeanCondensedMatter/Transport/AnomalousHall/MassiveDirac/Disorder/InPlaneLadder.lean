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

The bare-`σₓ` fixed point is solved explicitly under the visible nonzero-determinant hypothesis.
This file does not define the Born-Dyson momentum integrals that supply `X` and `Y`, take any
broadening/disorder limit, identify a transport lifetime, or insert the result into conductivity.
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

@[simp] theorem inPlaneLadderOperatorAction_sigmaX
    (x y : ℂ) :
    inPlaneLadderOperatorAction x y 1 0 =
      x • matrixOperator sigmaX + y • matrixOperator sigmaY := by
  simp [inPlaneLadderOperatorAction, inPlaneLadderXCoefficient,
    inPlaneLadderYCoefficient]

@[simp] theorem inPlaneLadderOperatorAction_sigmaY
    (x y : ℂ) :
    inPlaneLadderOperatorAction x y 0 1 =
      (-y) • matrixOperator sigmaX + x • matrixOperator sigmaY := by
  simp [inPlaneLadderOperatorAction, inPlaneLadderXCoefficient,
    inPlaneLadderYCoefficient]

/-- Determinant of the shifted two-component ladder equation `I - L`. -/
def inPlaneLadderDeterminant (x y : ℂ) : ℂ :=
  (1 - x) ^ 2 + y ^ 2

/-- Exact `σₓ` coefficient of the bare-`σₓ` ladder fixed point. -/
def inPlaneLadderSolvedXCoefficient (x y : ℂ) : ℂ :=
  (1 - x) / inPlaneLadderDeterminant x y

/-- Exact orientation-sensitive `σᵧ` coefficient of the bare-`σₓ` ladder fixed point. -/
def inPlaneLadderSolvedYCoefficient (x y : ℂ) : ℂ :=
  y / inPlaneLadderDeterminant x y

/-- The solved longitudinal coefficient satisfies the first scalar fixed-point equation. -/
theorem inPlaneLadderSolvedXCoefficient_fixedPoint
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedXCoefficient x y =
      1 + inPlaneLadderXCoefficient x y
        (inPlaneLadderSolvedXCoefficient x y)
        (inPlaneLadderSolvedYCoefficient x y) := by
  unfold inPlaneLadderSolvedXCoefficient inPlaneLadderSolvedYCoefficient
    inPlaneLadderXCoefficient
  unfold inPlaneLadderDeterminant at hdet ⊢
  field_simp [hdet]
  ring

/-- The solved transverse coefficient satisfies the second scalar fixed-point equation. -/
theorem inPlaneLadderSolvedYCoefficient_fixedPoint
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedYCoefficient x y =
      inPlaneLadderYCoefficient x y
        (inPlaneLadderSolvedXCoefficient x y)
        (inPlaneLadderSolvedYCoefficient x y) := by
  unfold inPlaneLadderSolvedXCoefficient inPlaneLadderSolvedYCoefficient
    inPlaneLadderYCoefficient
  unfold inPlaneLadderDeterminant at hdet ⊢
  field_simp [hdet]
  ring

/-- Bounded in-plane Pauli vertex corresponding to the exact solved coefficient pair. -/
noncomputable def inPlaneLadderSolvedVertex
    (x y : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneLadderSolvedXCoefficient x y • matrixOperator sigmaX +
    inPlaneLadderSolvedYCoefficient x y • matrixOperator sigmaY

/-- The explicit in-plane vertex solves `Γ = σₓ + L(Γ)` exactly whenever `I - L` has nonzero
coefficient determinant. -/
theorem inPlaneLadderSolvedVertex_fixedPoint
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    inPlaneLadderSolvedVertex x y =
      matrixOperator sigmaX +
        inPlaneLadderOperatorAction x y
          (inPlaneLadderSolvedXCoefficient x y)
          (inPlaneLadderSolvedYCoefficient x y) := by
  have hX := inPlaneLadderSolvedXCoefficient_fixedPoint x y hdet
  have hY := inPlaneLadderSolvedYCoefficient_fixedPoint x y hdet
  have hXsmul := congrArg
    (fun coefficient : ℂ => coefficient • matrixOperator sigmaX) hX
  have hYsmul := congrArg
    (fun coefficient : ℂ => coefficient • matrixOperator sigmaY) hY
  unfold inPlaneLadderSolvedVertex inPlaneLadderOperatorAction
  calc
    inPlaneLadderSolvedXCoefficient x y • matrixOperator sigmaX +
        inPlaneLadderSolvedYCoefficient x y • matrixOperator sigmaY =
      (1 + inPlaneLadderXCoefficient x y
          (inPlaneLadderSolvedXCoefficient x y)
          (inPlaneLadderSolvedYCoefficient x y)) • matrixOperator sigmaX +
        inPlaneLadderYCoefficient x y
          (inPlaneLadderSolvedXCoefficient x y)
          (inPlaneLadderSolvedYCoefficient x y) • matrixOperator sigmaY := by
      rw [hXsmul, hYsmul]
    _ = matrixOperator sigmaX +
        (inPlaneLadderXCoefficient x y
            (inPlaneLadderSolvedXCoefficient x y)
            (inPlaneLadderSolvedYCoefficient x y) • matrixOperator sigmaX +
          inPlaneLadderYCoefficient x y
            (inPlaneLadderSolvedXCoefficient x y)
            (inPlaneLadderSolvedYCoefficient x y) • matrixOperator sigmaY) := by
      module

/-- Any scalar coefficient pair satisfying the same two fixed-point equations has the solved
longitudinal coefficient. -/
theorem eq_inPlaneLadderSolvedXCoefficient_of_fixedPoint
    (x y alpha beta : ℂ)
    (hdet : inPlaneLadderDeterminant x y ≠ 0)
    (hX : alpha = 1 + inPlaneLadderXCoefficient x y alpha beta)
    (hY : beta = inPlaneLadderYCoefficient x y alpha beta) :
    alpha = inPlaneLadderSolvedXCoefficient x y := by
  unfold inPlaneLadderXCoefficient at hX
  unfold inPlaneLadderYCoefficient at hY
  have hxlin : (1 - x) * alpha + y * beta = 1 := by
    linear_combination hX
  have hylin : -y * alpha + (1 - x) * beta = 0 := by
    linear_combination hY
  have halphaRaw : ((1 - x) ^ 2 + y ^ 2) * alpha = 1 - x := by
    linear_combination (1 - x) * hxlin - y * hylin
  have halpha : inPlaneLadderDeterminant x y * alpha = 1 - x := by
    simpa [inPlaneLadderDeterminant] using halphaRaw
  unfold inPlaneLadderSolvedXCoefficient
  apply (eq_div_iff hdet).2
  simpa [mul_comm] using halpha

/-- Any scalar coefficient pair satisfying the same two fixed-point equations has the solved
orientation-sensitive transverse coefficient. -/
theorem eq_inPlaneLadderSolvedYCoefficient_of_fixedPoint
    (x y alpha beta : ℂ)
    (hdet : inPlaneLadderDeterminant x y ≠ 0)
    (hX : alpha = 1 + inPlaneLadderXCoefficient x y alpha beta)
    (hY : beta = inPlaneLadderYCoefficient x y alpha beta) :
    beta = inPlaneLadderSolvedYCoefficient x y := by
  unfold inPlaneLadderXCoefficient at hX
  unfold inPlaneLadderYCoefficient at hY
  have hxlin : (1 - x) * alpha + y * beta = 1 := by
    linear_combination hX
  have hylin : -y * alpha + (1 - x) * beta = 0 := by
    linear_combination hY
  have hbetaRaw : ((1 - x) ^ 2 + y ^ 2) * beta = y := by
    linear_combination y * hxlin + (1 - x) * hylin
  have hbeta : inPlaneLadderDeterminant x y * beta = y := by
    simpa [inPlaneLadderDeterminant] using hbetaRaw
  unfold inPlaneLadderSolvedYCoefficient
  apply (eq_div_iff hdet).2
  simpa [mul_comm] using hbeta

/-- The coefficient representation of the in-plane fixed point is unique under the same determinant
hypothesis. -/
theorem inPlaneLadder_fixedPoint_coefficients_unique
    (x y alpha beta : ℂ)
    (hdet : inPlaneLadderDeterminant x y ≠ 0)
    (hX : alpha = 1 + inPlaneLadderXCoefficient x y alpha beta)
    (hY : beta = inPlaneLadderYCoefficient x y alpha beta) :
    alpha = inPlaneLadderSolvedXCoefficient x y ∧
      beta = inPlaneLadderSolvedYCoefficient x y := by
  exact ⟨eq_inPlaneLadderSolvedXCoefficient_of_fixedPoint x y alpha beta hdet hX hY,
    eq_inPlaneLadderSolvedYCoefficient_of_fixedPoint x y alpha beta hdet hX hY⟩

@[simp] theorem inPlaneLadderSolvedYCoefficient_zero
    (x : ℂ) :
    inPlaneLadderSolvedYCoefficient x 0 = 0 := by
  simp [inPlaneLadderSolvedYCoefficient]

/-- With no transverse rung mixing, the two-component solution reduces to the familiar scalar
ladder factor `(1 - X)⁻¹`. -/
theorem inPlaneLadderSolvedXCoefficient_zero
    (x : ℂ) (hx : 1 - x ≠ 0) :
    inPlaneLadderSolvedXCoefficient x 0 = (1 - x)⁻¹ := by
  unfold inPlaneLadderSolvedXCoefficient inPlaneLadderDeterminant
  field_simp [hx]
  ring

end

end AnomalousHall.MassiveDirac
