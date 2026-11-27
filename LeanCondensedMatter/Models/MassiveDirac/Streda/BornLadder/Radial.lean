import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.RadialIntegrand
import LeanCondensedMatter.Transport.Disorder.InPlaneLadder
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

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

/-- Continuity of the shared polar Pauli operator as a function of its angle. -/
private theorem continuous_polarPauliOperator (a b d : ℂ) :
    Continuous (fun θ : ℝ => polarPauliOperator a b d θ) := by
  let L := (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] DiracOperator).toAlgEquiv.toLinearEquiv.toLinearMap
  change Continuous (fun θ : ℝ => L (polarPauliMatrix a b d θ))
  apply L.continuous_of_finiteDimensional.comp
  unfold polarPauliMatrix
  fun_prop

private theorem intervalIntegrable_polarPauli_directionTrace
    (measured : Fin 2) (q aL aR bL bR dL dR : ℂ)
    (coefficients : InPlaneCoefficientVector) :
    IntervalIntegrable
      (fun θ : ℝ =>
        finiteDimensionalOperatorTrace
          ((q • matrixOperator (directionPauli measured)) *
            polarPauliOperator aL bL dL θ *
            inPlanePauliVertexOperator coefficients *
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
    rw [inPlanePauliVertexOperator_eq_matrixOperator]
    simp [InternalSpace.pauliCombination_eq_components, sigmaX, sigmaY, u]
  rw [hmatrix]
  unfold matrixOperator
  rw [← map_smul, ← map_mul, finiteDimensionalOperatorTrace_toEuclideanCLM]
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
          inPlanePauliVertexOperator coefficients *
          polarPauliOperator aR bR dR θ)) =
      2 * q *
        inPlaneLadderAction
          (pauliRungAngularCoefficient aL aR dL dR) coefficients measured := by
  let rung : ℝ → DiracOperator := fun θ =>
    polarPauliOperator aL bL dL θ *
      inPlanePauliVertexOperator coefficients *
      polarPauliOperator aR bR dR θ
  have hrungIntegrable : IntervalIntegrable rung volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact ((continuous_polarPauliOperator aL bL dL).mul continuous_const).mul
      (continuous_polarPauliOperator aR bR dR)
  let L : DiracOperator →L[ℂ] ℂ :=
    finiteDimensionalOperatorTrace.comp
      (ContinuousLinearMap.mul ℂ DiracOperator (q • matrixOperator (directionPauli measured)))
  trans (∫ θ in (0 : ℝ)..(2 * Real.pi), L (rung θ))
  · apply intervalIntegral.integral_congr
    intro θ _
    simp only [L, rung, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', mul_assoc]
  rw [L.intervalIntegral_comp_comm hrungIntegrable]
  dsimp only [rung]
  rw [integral_polarPauliOperator_inPlane_eq]
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
    simp only [currentOperator_eq_charge_smul_velocityOperator, velocityOperator,
      velocity, matrixOperator, map_smul, smul_smul, q]
  have hcurrent (coefficients : InPlaneCoefficientVector) :
      inPlaneCurrentOperator e v coefficients =
        inPlanePauliVertexOperator (q • coefficients) := by
    rw [inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]
    exact (inPlanePauliVertexCLM.map_smul q coefficients).symm
  have hbareInPlane :
      currentOperator source e v = inPlaneCurrentOperator e v bare := by
    fin_cases source <;>
      simp [bare, inPlaneLadderBareXSource, Matrix.transpose, inPlaneRotationMatrix,
        inPlaneCoefficientVector, inPlaneCurrentOperator]
  let angularTrace (aL aR bL bR dL dR : ℂ)
      (coefficients : InPlaneCoefficientVector) : ℝ → ℂ :=
    fun θ =>
      finiteDimensionalOperatorTrace
        ((q • matrixOperator (directionPauli measured)) *
          polarPauliOperator aL bL dL θ *
          inPlanePauliVertexOperator coefficients *
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
    rw [hmeasured, hbareInPlane]
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
    simp only [hcurrent]
    rw [finiteCutoffContinuumBornDysonGreenOperator_polar_eq,
      finiteCutoffContinuumBornDysonGreenOperator_polar_eq]
    have hcyclic (J B A : DiracOperator) :
        finiteDimensionalOperatorTrace (B * A * J * A) =
          finiteDimensionalOperatorTrace (J * A * B * A) := by
      simpa only [mul_assoc] using
        (finiteDimensionalOperatorTrace_mul_comm (B * A) (J * A))
    rw [hcyclic
      (q • matrixOperator (directionPauli measured))
      (inPlanePauliVertexOperator (q • bare))
      (polarPauliOperator aA bA dA θ)]
  have hraIntegrable : IntervalIntegrable ra volume 0 (2 * Real.pi) :=
    intervalIntegrable_polarPauli_directionTrace measured q aR aA bR bA dR dA (q • dressed)
  have hrrIntegrable : IntervalIntegrable rr volume 0 (2 * Real.pi) :=
    intervalIntegrable_polarPauli_directionTrace measured q aR aR bR bR dR dR (q • bare)
  have haaIntegrable : IntervalIntegrable aa volume 0 (2 * Real.pi) :=
    intervalIntegrable_polarPauli_directionTrace measured q aA aA bA bA dA dA (q • bare)
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
  dsimp only
  simp only [← inPlaneLadderCLM_apply, map_smul, Pi.smul_apply, smul_eq_mul]
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

/-- Rotational closure gives the two in-plane tensor symmetries of the radial coefficient. -/
private theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_symmetry
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        1 0 e v m p probeEnergy broadening disorderStrength hbar pMax =
      -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        0 1 e v m p probeEnergy broadening disorderStrength hbar pMax) ∧
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        1 1 e v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        0 0 e v m p probeEnergy broadening disorderStrength hbar pMax) := by
  constructor <;>
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient <;>
    dsimp only <;>
    simp only [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector,
      Matrix.transpose_apply, inPlaneLadderAction_apply_x,
      inPlaneLadderAction_apply_y, inPlaneRotationMatrix_apply_x_x,
      inPlaneRotationMatrix_apply_x_y, inPlaneRotationMatrix_apply_y_x,
      inPlaneRotationMatrix_apply_y_y, inPlaneLadderBareXSource, inPlaneCoefficientVector,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring

/-- After radial integration, the finite-`η` ordered `yx` Středa response is the negative of `xy`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yx_eq_neg_xy
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        1 0 e v m probeEnergy broadening disorderStrength hbar pMax =
      -finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        0 1 e v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro p _
  simp only [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_symmetry
      e v m p probeEnergy broadening disorderStrength hbar pMax).1,
    mul_neg]

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
  simp only [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_symmetry
      e v m p probeEnergy broadening disorderStrength hbar pMax).2]

end

end QuantumTheory.Models.MassiveDirac
