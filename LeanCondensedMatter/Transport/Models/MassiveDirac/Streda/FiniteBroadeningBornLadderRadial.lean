import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.PauliRung
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial reduction of the finite-broadening dressed surface

This module reduces pair-indexed finite-cutoff finite-`η` Born-Dyson Středa surface responses to the
shared polar-Pauli rung coefficients. Both the measured-current and source directions remain indexed
through the angular reduction and radial integrand.

The pair-indexed coefficient keeps the RA dressed contribution and the bare-source RR/AA same-side
remainder in one canonical expression. Rotational closure of the in-plane rung then proves the
isotropic tensor relations `yx = -xy` and `yy = xx` after angular reduction. The Středa values and
explicit coefficient are total algebraic candidates; ladder regularity separately governs the
fixed-point interpretation of the solved vertex coefficients.

No radial antiderivative, conductivity normalization, disorder/broadening limit, ultraviolet
removal, mechanism label, or exact-disorder-average claim is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory QuantumTheory.Transport
open scoped Interval

private abbrev DiracOperator := DiracHilbert →L[ℂ] DiracHilbert

private theorem continuous_matrixOperator :
    Continuous (matrixOperator : Matrix2 → DiracOperator) := by
  let linearMatrixOperator : Matrix2 →ₗ[ℂ] DiracOperator :=
    { toFun := matrixOperator
      map_add' := by
        intro A B
        simp [matrixOperator]
      map_smul' := by
        intro c A
        simp [matrixOperator] }
  exact linearMatrixOperator.continuous_of_finiteDimensional

/-- Continuity of the shared polar Pauli operator as a function of its angle. -/
private theorem continuous_polarPauliOperator (a b d : ℂ) :
    Continuous (fun θ : ℝ => polarPauliOperator a b d θ) := by
  unfold polarPauliOperator
  apply continuous_matrixOperator.comp
  unfold polarPauliMatrix
  fun_prop

private theorem intervalIntegrable_polarPauli_rung
    (aL aR bL bR dL dR : ℂ) (coefficients : InPlaneCoefficientVector) :
    IntervalIntegrable
      (fun θ : ℝ =>
        polarPauliOperator aL bL dL θ *
          (coefficients .x • matrixOperator sigmaX +
            coefficients .y • matrixOperator sigmaY) *
          polarPauliOperator aR bR dR θ)
      volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  exact
    ((continuous_polarPauliOperator aL bL dL).mul continuous_const).mul
      (continuous_polarPauliOperator aR bR dR)

private theorem intervalIntegrable_polarPauli_directionTrace
    (measured : Direction2) (q aL aR bL bR dL dR : ℂ)
    (coefficients : InPlaneCoefficientVector) :
    IntervalIntegrable
      (fun θ : ℝ =>
        finiteDimensionalOperatorTrace
          ((q • matrixOperator (directionPauli measured)) *
            polarPauliOperator aL bL dL θ *
            (coefficients .x • matrixOperator sigmaX +
              coefficients .y • matrixOperator sigmaY) *
            polarPauliOperator aR bR dR θ))
      volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  exact (finiteDimensionalOperatorTrace (H := DiracHilbert)).continuous.comp
    (((continuous_const.mul (continuous_polarPauliOperator aL bL dL)).mul
      continuous_const).mul (continuous_polarPauliOperator aR bR dR))

/-- Full-angle trace of a polar Pauli rung with a measured in-plane Pauli vertex. -/
private theorem integral_polarPauli_directionTrace_eq
    (measured : Direction2) (q aL aR bL bR dL dR : ℂ)
    (coefficients : InPlaneCoefficientVector) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      finiteDimensionalOperatorTrace
        ((q • matrixOperator (directionPauli measured)) *
          polarPauliOperator aL bL dL θ *
          (coefficients .x • matrixOperator sigmaX +
            coefficients .y • matrixOperator sigmaY) *
          polarPauliOperator aR bR dR θ)) =
      2 * q *
        inPlaneLadderAction
          (pauliRungAngularCoefficient aL aR dL dR) coefficients measured := by
  let rung : ℝ → DiracOperator := fun θ =>
    polarPauliOperator aL bL dL θ *
      (coefficients .x • matrixOperator sigmaX +
        coefficients .y • matrixOperator sigmaY) *
      polarPauliOperator aR bR dR θ
  have hrungIntegrable : IntervalIntegrable rung volume 0 (2 * Real.pi) := by
    simpa [rung] using
      intervalIntegrable_polarPauli_rung aL aR bL bR dL dR coefficients
  let L : DiracOperator →L[ℂ] ℂ :=
    finiteDimensionalOperatorTrace.comp
      ((ContinuousLinearMap.mulLeftRight ℂ DiracOperator)
        (q • matrixOperator (directionPauli measured)) 1)
  have hoperator (c : InPlaneCoefficientVector) :
      inPlanePauliVertexOperator c =
        c .x • matrixOperator sigmaX + c .y • matrixOperator sigmaY := rfl
  have hfun :
      (fun θ : ℝ =>
        finiteDimensionalOperatorTrace
          ((q • matrixOperator (directionPauli measured)) *
            polarPauliOperator aL bL dL θ *
            (coefficients .x • matrixOperator sigmaX +
              coefficients .y • matrixOperator sigmaY) *
            polarPauliOperator aR bR dR θ)) =
        fun θ : ℝ => L (rung θ) := by
    funext θ
    simp [L, rung, mul_assoc]
  rw [hfun]
  rw [L.intervalIntegral_comp_comm hrungIntegrable]
  let coefficientsRung := pauliRungAngularCoefficient aL aR dL dR
  let x : ℂ := inPlaneLadderAction coefficientsRung coefficients .x
  let y : ℂ := inPlaneLadderAction coefficientsRung coefficients .y
  have hrungIntegral :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), rung θ) =
        x • matrixOperator sigmaX + y • matrixOperator sigmaY := by
    simpa [x, y, coefficientsRung, rung, hoperator] using
      (integral_polarPauliOperator_inPlane_eq aL aR bL bR dL dR coefficients)
  rw [hrungIntegral]
  cases measured
  · change finiteDimensionalOperatorTrace
        ((q • matrixOperator sigmaX) *
          (x • matrixOperator sigmaX + y • matrixOperator sigmaY)) = 2 * q * x
    have hop :
        (q • matrixOperator sigmaX) *
            (x • matrixOperator sigmaX + y • matrixOperator sigmaY) =
          matrixOperator ((q • sigmaX) * (x • sigmaX + y • sigmaY)) := by
      simp [matrixOperator]
    rw [hop, matrixOperator, finiteDimensionalOperatorTrace_toEuclideanCLM]
    simpa [InternalSpace.pauliCombination, sigmaX, sigmaY, mul_assoc] using
      (InternalSpace.trace_pauliCombination_mul_pauliCombination
        (fun | .x => q | .y => 0 | .z => 0)
        (fun | .x => x | .y => y | .z => 0))
  · change finiteDimensionalOperatorTrace
        ((q • matrixOperator sigmaY) *
          (x • matrixOperator sigmaX + y • matrixOperator sigmaY)) = 2 * q * y
    have hop :
        (q • matrixOperator sigmaY) *
            (x • matrixOperator sigmaX + y • matrixOperator sigmaY) =
          matrixOperator ((q • sigmaY) * (x • sigmaX + y • sigmaY)) := by
      simp [matrixOperator]
    rw [hop, matrixOperator, finiteDimensionalOperatorTrace_toEuclideanCLM]
    simpa [InternalSpace.pauliCombination, sigmaX, sigmaY, mul_assoc] using
      (InternalSpace.trace_pauliCombination_mul_pauliCombination
        (fun | .x => 0 | .y => q | .z => 0)
        (fun | .x => x | .y => y | .z => 0))

/-- Explicit pair-indexed radial coefficient of the finite-`η` RA-dressed Středa angular trace. The
RA and same-side rungs act on complete dressed and bare in-plane source vectors; the requested
measured-current direction is the final projection. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
    (measured source : Direction2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  let dressed := Matrix.transpose (inPlaneRotationMatrix solved) source
  let bare := Matrix.transpose (inPlaneRotationMatrix inPlaneLadderBareXSource) source
  let aR := finiteCutoffContinuumBornDysonScalarCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aA := finiteCutoffContinuumBornDysonScalarCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let raRung := pauliRungAngularCoefficient aR aA dR dA
  let rrRung := pauliRungAngularCoefficient aR aR dR dR
  let aaRung := pauliRungAngularCoefficient aA aA dA dA
  2 * q ^ 2 *
    (inPlaneLadderAction raRung dressed measured -
      (1 / 2 : ℂ) *
        (inPlaneLadderAction rrRung bare measured +
          inPlaneLadderAction aaRung bare measured))

/-- Every pair-indexed finite-`η` dressed Středa angular trace equals the same canonical radial
coefficient as an unconditional algebraic identity. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral_eq_radialCoefficient
    (measured source : Direction2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral
        measured source e v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        measured source e v m p probeEnergy broadening disorderStrength hbar pMax := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  let dressed := Matrix.transpose (inPlaneRotationMatrix solved) source
  let bare := Matrix.transpose (inPlaneRotationMatrix inPlaneLadderBareXSource) source
  let aR := finiteCutoffContinuumBornDysonScalarCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aA := finiteCutoffContinuumBornDysonScalarCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  have hmeasured : currentOperator measured e v =
      q • matrixOperator (directionPauli measured) := by
    cases measured <;>
      simp [q, currentOperator, current, velocity, directionPauli, matrixOperator, smul_smul]
  have hsource :
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
          source e v m probeEnergy broadening disorderStrength hbar pMax =
        (q • dressed) .x • matrixOperator sigmaX +
          (q • dressed) .y • matrixOperator sigmaY := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
    rw [inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]
    simp [q, solved, dressed, inPlanePauliVertexOperator, smul_add, smul_smul]
  have hbareInPlane :
      currentOperator source e v = inPlaneCurrentOperator e v bare := by
    cases source <;>
      simp [bare, inPlaneLadderBareXSource, Matrix.transpose, inPlaneRotationMatrix,
        inPlaneCoefficientVector, inPlaneCurrentOperator]
  have hbare :
      currentOperator source e v =
        (q • bare) .x • matrixOperator sigmaX +
          (q • bare) .y • matrixOperator sigmaY := by
    rw [hbareInPlane,
      inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]
    simp [q, inPlanePauliVertexOperator, smul_add, smul_smul]
  let ra : ℝ → ℂ := fun θ =>
    finiteDimensionalOperatorTrace
      ((q • matrixOperator (directionPauli measured)) * polarPauliOperator aR bR dR θ *
        ((q • dressed) .x • matrixOperator sigmaX +
          (q • dressed) .y • matrixOperator sigmaY) *
        polarPauliOperator aA bA dA θ)
  let rr : ℝ → ℂ := fun θ =>
    finiteDimensionalOperatorTrace
      ((q • matrixOperator (directionPauli measured)) * polarPauliOperator aR bR dR θ *
        ((q • bare) .x • matrixOperator sigmaX +
          (q • bare) .y • matrixOperator sigmaY) *
        polarPauliOperator aR bR dR θ)
  let aa : ℝ → ℂ := fun θ =>
    finiteDimensionalOperatorTrace
      ((q • matrixOperator (directionPauli measured)) * polarPauliOperator aA bA dA θ *
        ((q • bare) .x • matrixOperator sigmaX +
          (q • bare) .y • matrixOperator sigmaY) *
        polarPauliOperator aA bA dA θ)
  have hbridge :
      (fun θ : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
          measured source e v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax) =
        fun θ : ℝ => ra θ - (1 / 2 : ℂ) * (rr θ + aa θ) := by
    funext θ
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
      retardedAdvancedVertexTraceKernel sameSideVertexTraceRemainder twoGreenVertexTraceKernel
    rw [hmeasured, hsource, hbare]
    rw [finiteCutoffContinuumBornDysonGreenOperator_polar_eq,
      finiteCutoffContinuumBornDysonGreenOperator_polar_eq]
    have hcyclic :
        finiteDimensionalOperatorTrace
          (((q • bare) .x • matrixOperator sigmaX +
              (q • bare) .y • matrixOperator sigmaY) *
            polarPauliOperator aA bA dA θ *
            (q • matrixOperator (directionPauli measured)) *
            polarPauliOperator aA bA dA θ) =
          finiteDimensionalOperatorTrace
            ((q • matrixOperator (directionPauli measured)) *
              polarPauliOperator aA bA dA θ *
              ((q • bare) .x • matrixOperator sigmaX +
                (q • bare) .y • matrixOperator sigmaY) *
              polarPauliOperator aA bA dA θ) := by
      simpa [mul_assoc] using
        (finiteDimensionalOperatorTrace_mul_comm
          (((q • bare) .x • matrixOperator sigmaX +
              (q • bare) .y • matrixOperator sigmaY) *
            polarPauliOperator aA bA dA θ)
          ((q • matrixOperator (directionPauli measured)) * polarPauliOperator aA bA dA θ))
    rw [hcyclic]
  have hraIntegrable : IntervalIntegrable ra volume 0 (2 * Real.pi) := by
    simpa [ra] using intervalIntegrable_polarPauli_directionTrace
      measured q aR aA bR bA dR dA (q • dressed)
  have hrrIntegrable : IntervalIntegrable rr volume 0 (2 * Real.pi) := by
    simpa [rr] using intervalIntegrable_polarPauli_directionTrace
      measured q aR aR bR bR dR dR (q • bare)
  have haaIntegrable : IntervalIntegrable aa volume 0 (2 * Real.pi) := by
    simpa [aa] using intervalIntegrable_polarPauli_directionTrace
      measured q aA aA bA bA dA dA (q • bare)
  have hra := integral_polarPauli_directionTrace_eq
    measured q aR aA bR bA dR dA (q • dressed)
  have hrr := integral_polarPauli_directionTrace_eq
    measured q aR aR bR bR dR dR (q • bare)
  have haa := integral_polarPauli_directionTrace_eq
    measured q aA aA bA bA dA dA (q • bare)
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral
  rw [hbridge]
  rw [intervalIntegral.integral_sub hraIntegrable
    ((hrrIntegrable.add haaIntegrable).const_mul (1 / 2 : ℂ))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hrrIntegrable haaIntegrable, hra, hrr, haa]
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  simp [q, solved, dressed, bare, aR, aA, dR, dA, inPlaneLadderBareXSource]
  ring

/-- The pair-indexed finite-`η` radial integrand is the polar Jacobian `p` multiplying the canonical
angularly reduced coefficient. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient
    (measured source : Direction2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        measured source e v m p probeEnergy broadening disorderStrength hbar pMax =
      (p : ℂ) *
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
          measured source e v m p probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral_eq_radialCoefficient]

/-- Rotational closure makes the ordered `yx` radial coefficient the negative of `xy`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_yx_eq_neg_xy
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        .y .x e v m p probeEnergy broadening disorderStrength hbar pMax =
      -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        .x .y e v m p probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  dsimp only
  simp only [Matrix.transpose_apply, inPlaneLadderAction_apply_x,
    inPlaneLadderAction_apply_y, inPlaneRotationMatrix_apply_x_x,
    inPlaneRotationMatrix_apply_x_y, inPlaneRotationMatrix_apply_y_x,
    inPlaneRotationMatrix_apply_y_y, inPlaneLadderBareXSource, inPlaneCoefficientVector]
  ring

/-- Rotational closure makes the two diagonal radial coefficients equal. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_yy_eq_xx
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        .y .y e v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        .x .x e v m p probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  dsimp only
  simp only [Matrix.transpose_apply, inPlaneLadderAction_apply_x,
    inPlaneLadderAction_apply_y, inPlaneRotationMatrix_apply_x_x,
    inPlaneRotationMatrix_apply_x_y, inPlaneRotationMatrix_apply_y_x,
    inPlaneRotationMatrix_apply_y_y, inPlaneLadderBareXSource, inPlaneCoefficientVector]
  ring

/-- The finite-`η` ordered `yx` radial Středa response is the negative of `xy`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_yx_eq_neg_xy
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        .y .x e v m p probeEnergy broadening disorderStrength hbar pMax =
      -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        .x .y e v m p probeEnergy broadening disorderStrength hbar pMax := by
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_yx_eq_neg_xy]
  ring

/-- The two finite-`η` diagonal radial Středa responses are equal. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_yy_eq_xx
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        .y .y e v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        .x .x e v m p probeEnergy broadening disorderStrength hbar pMax := by
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_yy_eq_xx]

/-- After radial integration, the finite-`η` ordered `yx` Středa response is the negative of `xy`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yx_eq_neg_xy
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        .y .x e v m probeEnergy broadening disorderStrength hbar pMax =
      -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        .x .y e v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  calc
    (∫ p in (0 : ℝ)..pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        .y .x e v m p probeEnergy broadening disorderStrength hbar pMax) =
      ∫ p in (0 : ℝ)..pMax,
        -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          .x .y e v m p probeEnergy broadening disorderStrength hbar pMax := by
        apply intervalIntegral.integral_congr
        intro p _
        exact finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_yx_eq_neg_xy
          e v m p probeEnergy broadening disorderStrength hbar pMax
    _ = -∫ p in (0 : ℝ)..pMax,
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          .x .y e v m p probeEnergy broadening disorderStrength hbar pMax := by
        change (∫ p in (0 : ℝ)..pMax,
          (-1 : ℂ) * finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
            .x .y e v m p probeEnergy broadening disorderStrength hbar pMax) = _
        rw [intervalIntegral.integral_const_mul]
        ring

/-- After radial integration, the two finite-`η` diagonal Středa responses are equal. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yy_eq_xx
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        .y .y e v m probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        .x .x e v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  apply intervalIntegral.integral_congr
  intro p _
  exact finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_yy_eq_xx
    e v m p probeEnergy broadening disorderStrength hbar pMax

end

end QuantumTheory.Transport.Models.MassiveDirac
