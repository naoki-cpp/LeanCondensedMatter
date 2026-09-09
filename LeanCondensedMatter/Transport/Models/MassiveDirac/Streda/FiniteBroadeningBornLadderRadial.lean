import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.PauliRung
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial reduction of the finite-broadening dressed surface

This module reduces source-indexed finite-cutoff finite-`η` Born-Dyson Středa surface responses to
the shared polar-Pauli rung coefficients. The measured channel is the physical `jₓ`, while the
source direction remains indexed through the angular reduction and radial integrand.

The source-indexed coefficient keeps the RA dressed contribution and the bare-source RR/AA
same-side remainder in one canonical expression. For source `.y` the same-side contribution
vanishes algebraically; for source `.x` it remains. Both the Středa values and the explicit
coefficient are total algebraic candidates; ladder regularity separately governs the fixed-point
interpretation of the solved vertex coefficients.

No radial antiderivative, conductivity normalization, disorder/broadening limit, ultraviolet
removal, Hall antisymmetrization, mechanism label, or exact-disorder-average claim is introduced
here.
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

private theorem intervalIntegrable_polarPauli_xyTrace
    (q aL aR bL bR dL dR : ℂ) (coefficients : InPlaneCoefficientVector) :
    IntervalIntegrable
      (fun θ : ℝ =>
        finiteDimensionalOperatorTrace
          ((q • matrixOperator sigmaX) *
            polarPauliOperator aL bL dL θ *
            (coefficients .x • matrixOperator sigmaX +
              coefficients .y • matrixOperator sigmaY) *
            polarPauliOperator aR bR dR θ))
      volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  exact (finiteDimensionalOperatorTrace (H := DiracHilbert)).continuous.comp
    (((continuous_const.mul (continuous_polarPauliOperator aL bL dL)).mul
      continuous_const).mul (continuous_polarPauliOperator aR bR dR))

/-- Full-angle trace of a polar Pauli rung with a measured `q σₓ` vertex. -/
private theorem integral_polarPauli_xyTrace_eq
    (q aL aR bL bR dL dR : ℂ) (coefficients : InPlaneCoefficientVector) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      finiteDimensionalOperatorTrace
        ((q • matrixOperator sigmaX) *
          polarPauliOperator aL bL dL θ *
          (coefficients .x • matrixOperator sigmaX +
            coefficients .y • matrixOperator sigmaY) *
          polarPauliOperator aR bR dR θ)) =
      2 * q *
        inPlaneLadderAction
          (pauliRungAngularCoefficient aL aR dL dR) coefficients .x := by
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
        (q • matrixOperator sigmaX) 1)
  have hsource :
      matrixOperator (coefficients .x • sigmaX + coefficients .y • sigmaY) =
        coefficients .x • matrixOperator sigmaX +
          coefficients .y • matrixOperator sigmaY := by
    simp [matrixOperator]
  have hfun :
      (fun θ : ℝ =>
        finiteDimensionalOperatorTrace
          ((q • matrixOperator sigmaX) *
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
    simpa [x, y, coefficientsRung, rung, hsource] using
      (integral_polarPauliOperator_inPlane_eq
        aL aR bL bR dL dR (coefficients .x) (coefficients .y))
  rw [hrungIntegral]
  change L (x • matrixOperator sigmaX + y • matrixOperator sigmaY) = 2 * q * x
  have hop :
      (q • matrixOperator sigmaX) *
          (x • matrixOperator sigmaX + y • matrixOperator sigmaY) =
        matrixOperator ((q • sigmaX) * (x • sigmaX + y • sigmaY)) := by
    simp [matrixOperator]
  calc
    L (x • matrixOperator sigmaX + y • matrixOperator sigmaY) =
        finiteDimensionalOperatorTrace
          ((q • matrixOperator sigmaX) *
            (x • matrixOperator sigmaX + y • matrixOperator sigmaY)) := by
      simp [L]
    _ = finiteDimensionalOperatorTrace
          (matrixOperator ((q • sigmaX) * (x • sigmaX + y • sigmaY))) := by
      rw [hop]
    _ = Matrix.trace ((q • sigmaX) * (x • sigmaX + y • sigmaY)) := by
      rw [matrixOperator, finiteDimensionalOperatorTrace_toEuclideanCLM]
    _ = 2 * q * x := by
      simpa [InternalSpace.pauliCombination, sigmaX, sigmaY, mul_assoc] using
        (InternalSpace.trace_pauliCombination_mul_pauliCombination
          (fun | .x => q | .y => 0 | .z => 0)
          (fun | .x => x | .y => y | .z => 0))

/-- Explicit source-indexed radial coefficient of the finite-`η` RA-dressed Středa angular trace.
The RA and same-side rungs act on complete dressed and bare in-plane source vectors; the measured
`jₓ` channel is the final `.x` projection. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
    (source : Direction2)
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
    (inPlaneLadderAction raRung dressed .x -
      (1 / 2 : ℂ) *
        (inPlaneLadderAction rrRung bare .x +
          inPlaneLadderAction aaRung bare .x))

/-- Every source-indexed finite-`η` dressed Středa angular trace equals the same canonical radial
coefficient as an unconditional algebraic identity. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral_eq_radialCoefficient
    (source : Direction2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral
        source e v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        source e v m p probeEnergy broadening disorderStrength hbar pMax := by
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
  have hjx : currentOperator .x e v = q • matrixOperator sigmaX := by
    dsimp [q]
    unfold currentOperator current velocity directionPauli matrixOperator
    rw [map_smul, map_smul]
    push_cast
    module
  have hsource :
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
          source e v m probeEnergy broadening disorderStrength hbar pMax =
        (q • dressed) .x • matrixOperator sigmaX +
          (q • dressed) .y • matrixOperator sigmaY := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
    rw [inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]
    simp [q, solved, dressed, inPlanePauliVertexOperator, smul_add, smul_smul]
  have hbareInPlane :
      currentOperator source e v = inPlaneCurrentOperator e v (bare .x) (bare .y) := by
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
      ((q • matrixOperator sigmaX) * polarPauliOperator aR bR dR θ *
        ((q • dressed) .x • matrixOperator sigmaX +
          (q • dressed) .y • matrixOperator sigmaY) *
        polarPauliOperator aA bA dA θ)
  let rr : ℝ → ℂ := fun θ =>
    finiteDimensionalOperatorTrace
      ((q • matrixOperator sigmaX) * polarPauliOperator aR bR dR θ *
        ((q • bare) .x • matrixOperator sigmaX +
          (q • bare) .y • matrixOperator sigmaY) *
        polarPauliOperator aR bR dR θ)
  let aa : ℝ → ℂ := fun θ =>
    finiteDimensionalOperatorTrace
      ((q • matrixOperator sigmaX) * polarPauliOperator aA bA dA θ *
        ((q • bare) .x • matrixOperator sigmaX +
          (q • bare) .y • matrixOperator sigmaY) *
        polarPauliOperator aA bA dA θ)
  have hbridge :
      (fun θ : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
          source e v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax) =
        fun θ : ℝ => ra θ - (1 / 2 : ℂ) * (rr θ + aa θ) := by
    funext θ
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
      retardedAdvancedVertexTraceKernel sameSideVertexTraceRemainder twoGreenVertexTraceKernel
    rw [hjx, hsource, hbare]
    rw [finiteCutoffContinuumBornDysonGreenOperator_polar_eq,
      finiteCutoffContinuumBornDysonGreenOperator_polar_eq]
    have hcyclic :
        finiteDimensionalOperatorTrace
          (((q • bare) .x • matrixOperator sigmaX +
              (q • bare) .y • matrixOperator sigmaY) *
            polarPauliOperator aA bA dA θ *
            (q • matrixOperator sigmaX) *
            polarPauliOperator aA bA dA θ) =
          finiteDimensionalOperatorTrace
            ((q • matrixOperator sigmaX) *
              polarPauliOperator aA bA dA θ *
              ((q • bare) .x • matrixOperator sigmaX +
                (q • bare) .y • matrixOperator sigmaY) *
              polarPauliOperator aA bA dA θ) := by
      simpa [mul_assoc] using
        (finiteDimensionalOperatorTrace_mul_comm
          (((q • bare) .x • matrixOperator sigmaX +
              (q • bare) .y • matrixOperator sigmaY) *
            polarPauliOperator aA bA dA θ)
          ((q • matrixOperator sigmaX) * polarPauliOperator aA bA dA θ))
    rw [hcyclic]
  have hraIntegrable : IntervalIntegrable ra volume 0 (2 * Real.pi) := by
    simpa [ra] using intervalIntegrable_polarPauli_xyTrace
      q aR aA bR bA dR dA (q • dressed)
  have hrrIntegrable : IntervalIntegrable rr volume 0 (2 * Real.pi) := by
    simpa [rr] using intervalIntegrable_polarPauli_xyTrace
      q aR aR bR bR dR dR (q • bare)
  have haaIntegrable : IntervalIntegrable aa volume 0 (2 * Real.pi) := by
    simpa [aa] using intervalIntegrable_polarPauli_xyTrace
      q aA aA bA bA dA dA (q • bare)
  have hra := integral_polarPauli_xyTrace_eq
    q aR aA bR bA dR dA (q • dressed)
  have hrr := integral_polarPauli_xyTrace_eq
    q aR aR bR bR dR dR (q • bare)
  have haa := integral_polarPauli_xyTrace_eq
    q aA aA bA bA dA dA (q • bare)
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral
  rw [hbridge]
  rw [intervalIntegral.integral_sub hraIntegrable
    ((hrrIntegrable.add haaIntegrable).const_mul (1 / 2 : ℂ))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hrrIntegrable haaIntegrable, hra, hrr, haa]
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  simp [q, solved, dressed, bare, aR, aA, dR, dA, inPlaneLadderBareXSource]
  ring

/-- The source-indexed finite-`η` radial integrand is the polar Jacobian `p` multiplying the
canonical angularly reduced coefficient. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient
    (source : Direction2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        source e v m p probeEnergy broadening disorderStrength hbar pMax =
      (p : ℂ) *
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
          source e v m p probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral_eq_radialCoefficient]

end

end QuantumTheory.Transport.Models.MassiveDirac
