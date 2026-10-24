import LeanCondensedMatter.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderIntegral
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexResponse
import LeanCondensedMatter.Models.MassiveDirac.Vertex.PauliRung
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

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open MeasureTheory
open ContinuousLinearMap
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
          (coefficients 0 • matrixOperator sigmaX +
            coefficients 1 • matrixOperator sigmaY) *
          polarPauliOperator aR bR dR θ)
      volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  exact
    ((continuous_polarPauliOperator aL bL dL).mul continuous_const).mul
      (continuous_polarPauliOperator aR bR dR)

private theorem intervalIntegrable_polarPauli_directionTrace
    (measured : Fin 2) (q aL aR bL bR dL dR : ℂ)
    (coefficients : InPlaneCoefficientVector) :
    IntervalIntegrable
      (fun θ : ℝ =>
        finiteDimensionalOperatorTrace
          ((q • matrixOperator (directionPauli measured)) *
            polarPauliOperator aL bL dL θ *
            (coefficients 0 • matrixOperator sigmaX +
              coefficients 1 • matrixOperator sigmaY) *
            polarPauliOperator aR bR dR θ))
      volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  exact (finiteDimensionalOperatorTrace (H := DiracHilbert)).continuous.comp
    (((continuous_const.mul (continuous_polarPauliOperator aL bL dL)).mul
      continuous_const).mul (continuous_polarPauliOperator aR bR dR))

/-- Hilbert--Schmidt orthogonality of the Hermitian Pauli basis projects an in-plane
operator onto its measured coefficient; the scalar `q` multiplies the trace rather
than occupying the conjugate-linear slot of the Hilbert--Schmidt pairing. -/
private theorem trace_directionPauli_inPlane_eq
    (measured : Fin 2) (q : ℂ) (coefficients : InPlaneCoefficientVector) :
    finiteDimensionalOperatorTrace
        ((q • matrixOperator (directionPauli measured)) *
          inPlanePauliVertexOperator coefficients) =
      2 * q * coefficients measured := by
  let u : PauliAxis → ℂ
    | .x => coefficients 0
    | .y => coefficients 1
    | .z => 0
  have hmatrix :
      inPlanePauliVertexOperator coefficients =
        matrixOperator (InternalSpace.pauliCombination u) := by
    simp [inPlanePauliVertexOperator, matrixOperator,
      InternalSpace.pauliCombination_eq_components, sigmaX, sigmaY, u]
  rw [hmatrix]
  have hop :
      (q • matrixOperator (directionPauli measured)) *
          matrixOperator (InternalSpace.pauliCombination u) =
        matrixOperator
          ((q • directionPauli measured) * InternalSpace.pauliCombination u) := by
    simp [matrixOperator]
  rw [hop, matrixOperator, finiteDimensionalOperatorTrace_toEuclideanCLM]
  rw [smul_mul_assoc, Matrix.trace_smul]
  change
    q * Matrix.trace
        (InternalSpace.pauliBasis (inPlanePauliAxis measured) *
          InternalSpace.pauliCombination u) = _
  rw [InternalSpace.trace_pauliBasis_mul_pauliCombination]
  have hcomponent : u (inPlanePauliAxis measured) = coefficients measured := by
    fin_cases measured <;> simp [u, inPlanePauliAxis]
  rw [hcomponent]
  ring

/-- Full-angle trace of a polar Pauli rung with a measured in-plane Pauli vertex. -/
private theorem integral_polarPauli_directionTrace_eq
    (measured : Fin 2) (q aL aR bL bR dL dR : ℂ)
    (coefficients : InPlaneCoefficientVector) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      finiteDimensionalOperatorTrace
        ((q • matrixOperator (directionPauli measured)) *
          polarPauliOperator aL bL dL θ *
          (coefficients 0 • matrixOperator sigmaX +
            coefficients 1 • matrixOperator sigmaY) *
          polarPauliOperator aR bR dR θ)) =
      2 * q *
        inPlaneLadderAction
          (pauliRungAngularCoefficient aL aR dL dR) coefficients measured := by
  let rung : ℝ → DiracOperator := fun θ =>
    polarPauliOperator aL bL dL θ *
      (coefficients 0 • matrixOperator sigmaX +
        coefficients 1 • matrixOperator sigmaY) *
      polarPauliOperator aR bR dR θ
  have hrungIntegrable : IntervalIntegrable rung volume 0 (2 * Real.pi) := by
    simpa [rung] using
      intervalIntegrable_polarPauli_rung aL aR bL bR dL dR coefficients
  let L : DiracOperator →L[ℂ] ℂ :=
    finiteDimensionalOperatorTrace.comp
      ((ContinuousLinearMap.mulLeftRight ℂ DiracOperator)
        (q • matrixOperator (directionPauli measured)) 1)
  have hfun :
      (fun θ : ℝ =>
        finiteDimensionalOperatorTrace
          ((q • matrixOperator (directionPauli measured)) *
            polarPauliOperator aL bL dL θ *
            (coefficients 0 • matrixOperator sigmaX +
              coefficients 1 • matrixOperator sigmaY) *
            polarPauliOperator aR bR dR θ)) =
        fun θ : ℝ => L (rung θ) := by
    funext θ
    simp [L, rung, mul_assoc]
  rw [hfun]
  rw [L.intervalIntegral_comp_comm hrungIntegrable]
  have hrungIntegral :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), rung θ) =
        inPlanePauliVertexOperator
          (inPlaneLadderAction
            (pauliRungAngularCoefficient aL aR dL dR) coefficients) := by
    simpa only [rung, inPlanePauliVertexOperator] using
      (integral_polarPauliOperator_inPlane_eq aL aR bL bR dL dR coefficients)
  rw [hrungIntegral]
  change
    finiteDimensionalOperatorTrace
        ((q • matrixOperator (directionPauli measured)) *
          inPlanePauliVertexOperator
            (inPlaneLadderAction
              (pauliRungAngularCoefficient aL aR dL dR) coefficients)) =
      2 * q * inPlaneLadderAction
        (pauliRungAngularCoefficient aL aR dL dR) coefficients measured
  exact trace_directionPauli_inPlane_eq measured q
    (inPlaneLadderAction (pauliRungAngularCoefficient aL aR dL dR) coefficients)

/-- Explicit pair-indexed radial coefficient of the finite-`η` RA-dressed Středa angular trace. The
RA and same-side rungs act on complete dressed and bare in-plane source vectors; the requested
measured-current direction is the final projection. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
    (measured source : Fin 2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let dressed :=
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector
      source v m probeEnergy broadening disorderStrength hbar pMax
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
    (measured source : Fin 2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral
        measured source e v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        measured source e v m p probeEnergy broadening disorderStrength hbar pMax := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let dressed :=
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector
      source v m probeEnergy broadening disorderStrength hbar pMax
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
    rw [currentOperator_eq_charge_smul_velocityOperator]
    unfold velocityOperator velocity matrixOperator
    rw [map_smul]
    dsimp [q]
    module
  have hsource :
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
          source e v m probeEnergy broadening disorderStrength hbar pMax =
        (q • dressed) 0 • matrixOperator sigmaX +
          (q • dressed) 1 • matrixOperator sigmaY := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
    rw [inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]
    simp [q, dressed, inPlanePauliVertexOperator, smul_add, smul_smul]
  have hbareInPlane :
      currentOperator source e v = inPlaneCurrentOperator e v bare := by
    fin_cases source <;>
      simp [bare, inPlaneLadderBareXSource, Matrix.transpose, inPlaneRotationMatrix,
        inPlaneCoefficientVector, inPlaneCurrentOperator]
  have hbare :
      currentOperator source e v =
        (q • bare) 0 • matrixOperator sigmaX +
          (q • bare) 1 • matrixOperator sigmaY := by
    rw [hbareInPlane,
      inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]
    simp [q, inPlanePauliVertexOperator, smul_add, smul_smul]
  let angularTrace (aL aR bL bR dL dR : ℂ)
      (coefficients : InPlaneCoefficientVector) : ℝ → ℂ :=
    fun θ =>
      finiteDimensionalOperatorTrace
        ((q • matrixOperator (directionPauli measured)) *
          polarPauliOperator aL bL dL θ *
          (coefficients 0 • matrixOperator sigmaX +
            coefficients 1 • matrixOperator sigmaY) *
          polarPauliOperator aR bR dR θ)
  let ra := angularTrace aR aA bR bA dR dA (q • dressed)
  let rr := angularTrace aR aR bR bR dR dR (q • bare)
  let aa := angularTrace aA aA bA bA dA dA (q • bare)
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
    have hcyclic (J B A : DiracOperator) :
        finiteDimensionalOperatorTrace (B * A * J * A) =
          finiteDimensionalOperatorTrace (J * A * B * A) := by
      simpa only [mul_assoc] using
        (finiteDimensionalOperatorTrace_mul_comm (B * A) (J * A))
    rw [hcyclic
      (q • matrixOperator (directionPauli measured))
      ((q • bare) 0 • matrixOperator sigmaX +
        (q • bare) 1 • matrixOperator sigmaY)
      (polarPauliOperator aA bA dA θ)]
  have hraIntegrable : IntervalIntegrable ra volume 0 (2 * Real.pi) := by
    simpa [ra, angularTrace] using intervalIntegrable_polarPauli_directionTrace
      measured q aR aA bR bA dR dA (q • dressed)
  have hrrIntegrable : IntervalIntegrable rr volume 0 (2 * Real.pi) := by
    simpa [rr, angularTrace] using intervalIntegrable_polarPauli_directionTrace
      measured q aR aR bR bR dR dR (q • bare)
  have haaIntegrable : IntervalIntegrable aa volume 0 (2 * Real.pi) := by
    simpa [aa, angularTrace] using intervalIntegrable_polarPauli_directionTrace
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
  fin_cases measured <;>
    simp [q, dressed, bare, aR, aA, dR, dA, inPlaneLadderBareXSource,
      inPlaneLadderAction_apply_x, inPlaneLadderAction_apply_y] <;>
    ring

/-- The pair-indexed finite-`η` radial integrand is the polar Jacobian `p` multiplying the canonical
angularly reduced coefficient. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient
    (measured source : Fin 2)
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
        1 0 e v m p probeEnergy broadening disorderStrength hbar pMax =
      -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        0 1 e v m p probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  dsimp only
  simp only [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector_x,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector_y,
    Matrix.transpose_apply, inPlaneLadderAction_apply_x,
    inPlaneLadderAction_apply_y, inPlaneRotationMatrix_apply_x_x,
    inPlaneRotationMatrix_apply_x_y, inPlaneRotationMatrix_apply_y_x,
    inPlaneRotationMatrix_apply_y_y, inPlaneLadderBareXSource, inPlaneCoefficientVector,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Rotational closure makes the two diagonal radial coefficients equal. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_yy_eq_xx
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        1 1 e v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        0 0 e v m p probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  dsimp only
  simp only [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector_x,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector_y,
    Matrix.transpose_apply, inPlaneLadderAction_apply_x,
    inPlaneLadderAction_apply_y, inPlaneRotationMatrix_apply_x_x,
    inPlaneRotationMatrix_apply_x_y, inPlaneRotationMatrix_apply_y_x,
    inPlaneRotationMatrix_apply_y_y, inPlaneLadderBareXSource, inPlaneCoefficientVector,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The finite-`η` ordered `yx` radial Středa response is the negative of `xy`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_yx_eq_neg_xy
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        1 0 e v m p probeEnergy broadening disorderStrength hbar pMax =
      -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        0 1 e v m p probeEnergy broadening disorderStrength hbar pMax := by
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_yx_eq_neg_xy]
  ring

/-- The two finite-`η` diagonal radial Středa responses are equal. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_yy_eq_xx
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        1 1 e v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        0 0 e v m p probeEnergy broadening disorderStrength hbar pMax := by
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_yy_eq_xx]

/-- After radial integration, the finite-`η` ordered `yx` Středa response is the negative of `xy`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yx_eq_neg_xy
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        1 0 e v m probeEnergy broadening disorderStrength hbar pMax =
      -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        0 1 e v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  calc
    (∫ p in (0 : ℝ)..pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        1 0 e v m p probeEnergy broadening disorderStrength hbar pMax) =
      ∫ p in (0 : ℝ)..pMax,
        -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          0 1 e v m p probeEnergy broadening disorderStrength hbar pMax := by
        apply intervalIntegral.integral_congr
        intro p _
        exact finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_yx_eq_neg_xy
          e v m p probeEnergy broadening disorderStrength hbar pMax
    _ = -∫ p in (0 : ℝ)..pMax,
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          0 1 e v m p probeEnergy broadening disorderStrength hbar pMax := by
        rw [intervalIntegral.integral_neg]

/-- After radial integration, the two finite-`η` diagonal Středa responses are equal. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yy_eq_xx
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        1 1 e v m probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        0 0 e v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  apply intervalIntegral.integral_congr
  intro p _
  exact finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_yy_eq_xx
    e v m p probeEnergy broadening disorderStrength hbar pMax

end

end QuantumTheory.Models.MassiveDirac
