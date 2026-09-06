import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.PauliRung
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial reduction of the finite-broadening dressed Hall surface

This module reduces the full polar-angle trace introduced by the finite-cutoff finite-`η`
Born-Dyson Hall-surface conductivity bridge to the existing shared polar-Pauli rung coefficients.
The measured channel is the physical `jₓ`, while the retarded-advanced source is the solved rotated
`jᵧ` ladder vertex.

The explicit RR/AA same-side remainder is not discarded by approximation: for an isotropic
same-side polar propagator its orientation-sensitive rung coefficient is identically zero, so both
same-side ordered `xy` traces vanish after the full angular integral. The surviving radial
coefficient is therefore the RA contribution expressed through the already-owned finite-broadening
`X/Y` rung coefficients and solved ladder coefficients.

No radial antiderivative, disorder/broadening limit, ultraviolet removal, Hall antisymmetrization,
mechanism label, or exact-disorder-average claim is introduced here.
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

@[simp] private theorem finiteTrace_smul_sigmaX_mul_inPlane
    (q x y : ℂ) :
    finiteDimensionalOperatorTrace
        ((q • matrixOperator sigmaX) *
          (x • matrixOperator sigmaX + y • matrixOperator sigmaY)) =
      2 * q * x := by
  have hop :
      (q • matrixOperator sigmaX) *
          (x • matrixOperator sigmaX + y • matrixOperator sigmaY) =
        matrixOperator ((q • sigmaX) * (x • sigmaX + y • sigmaY)) := by
    simp [matrixOperator]
  rw [hop]
  unfold matrixOperator
  rw [finiteDimensionalOperatorTrace_toEuclideanCLM]
  simp [Matrix.trace, sigmaX, sigmaY]
  ring

private theorem intervalIntegrable_polarPauli_rung
    (aL aR bL bR dL dR alpha beta : ℂ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        polarPauliOperator aL bL dL θ *
          (alpha • matrixOperator sigmaX + beta • matrixOperator sigmaY) *
          polarPauliOperator aR bR dR θ)
      volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  exact
    ((continuous_polarPauliOperator aL bL dL).mul continuous_const).mul
      (continuous_polarPauliOperator aR bR dR)

private theorem intervalIntegrable_polarPauli_xyTrace
    (q aL aR bL bR dL dR alpha beta : ℂ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        finiteDimensionalOperatorTrace
          ((q • matrixOperator sigmaX) *
            polarPauliOperator aL bL dL θ *
            (alpha • matrixOperator sigmaX + beta • matrixOperator sigmaY) *
            polarPauliOperator aR bR dR θ))
      volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  exact (finiteDimensionalOperatorTrace (H := DiracHilbert)).continuous.comp
    (((continuous_const.mul (continuous_polarPauliOperator aL bL dL)).mul
      continuous_const).mul (continuous_polarPauliOperator aR bR dR))

/-- Full-angle trace of a polar Pauli rung with a measured `q σₓ` vertex. -/
private theorem integral_polarPauli_xyTrace_eq
    (q aL aR bL bR dL dR alpha beta : ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      finiteDimensionalOperatorTrace
        ((q • matrixOperator sigmaX) *
          polarPauliOperator aL bL dL θ *
          (alpha • matrixOperator sigmaX + beta • matrixOperator sigmaY) *
          polarPauliOperator aR bR dR θ)) =
      2 * q *
        (pauliRungAngularXCoefficient aL aR dL dR * alpha -
          pauliRungAngularYCoefficient aL aR dL dR * beta) := by
  let rung : ℝ → DiracOperator := fun θ =>
    polarPauliOperator aL bL dL θ *
      (alpha • matrixOperator sigmaX + beta • matrixOperator sigmaY) *
      polarPauliOperator aR bR dR θ
  have hrungIntegrable : IntervalIntegrable rung volume 0 (2 * Real.pi) := by
    simpa [rung] using
      intervalIntegrable_polarPauli_rung aL aR bL bR dL dR alpha beta
  let L : DiracOperator →L[ℂ] ℂ :=
    finiteDimensionalOperatorTrace.comp
      ((ContinuousLinearMap.mulLeftRight ℂ DiracOperator)
        (q • matrixOperator sigmaX) 1)
  have hsource :
      matrixOperator (alpha • sigmaX + beta • sigmaY) =
        alpha • matrixOperator sigmaX + beta • matrixOperator sigmaY := by
    simp [matrixOperator]
  have hfun :
      (fun θ : ℝ =>
        finiteDimensionalOperatorTrace
          ((q • matrixOperator sigmaX) *
            polarPauliOperator aL bL dL θ *
            (alpha • matrixOperator sigmaX + beta • matrixOperator sigmaY) *
            polarPauliOperator aR bR dR θ)) =
        fun θ : ℝ => L (rung θ) := by
    funext θ
    simp [L, rung, mul_assoc]
  rw [hfun]
  rw [L.intervalIntegral_comp_comm hrungIntegrable]
  have hrungIntegral :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), rung θ) =
        (pauliRungAngularXCoefficient aL aR dL dR * alpha -
          pauliRungAngularYCoefficient aL aR dL dR * beta) • matrixOperator sigmaX +
        (pauliRungAngularYCoefficient aL aR dL dR * alpha +
          pauliRungAngularXCoefficient aL aR dL dR * beta) • matrixOperator sigmaY := by
    simpa [rung, hsource] using
      (integral_polarPauliOperator_inPlane_eq
        aL aR bL bR dL dR alpha beta)
  rw [hrungIntegral]
  simpa [L] using
    (finiteTrace_smul_sigmaX_mul_inPlane q
      (pauliRungAngularXCoefficient aL aR dL dR * alpha -
        pauliRungAngularYCoefficient aL aR dL dR * beta)
      (pauliRungAngularYCoefficient aL aR dL dR * alpha +
        pauliRungAngularXCoefficient aL aR dL dR * beta))

/-- For equal left/right polar propagators, the full-angle ordered `xy` trace vanishes exactly. -/
private theorem integral_polarPauli_sameSideXYTrace_eq_zero
    (q a b d : ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      finiteDimensionalOperatorTrace
        ((q • matrixOperator sigmaX) *
          polarPauliOperator a b d θ *
          (q • matrixOperator sigmaY) *
          polarPauliOperator a b d θ)) = 0 := by
  have h := integral_polarPauli_xyTrace_eq q a a b b d d 0 q
  simpa [pauliRungAngularYCoefficient] using h

/-- Explicit radial coefficient of the finite-`η` RA-dressed ordered `xy` Hall-surface trace after
the full polar-angle integral. -/
def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let alpha := finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
    v m probeEnergy broadening disorderStrength hbar pMax
  let beta := finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
    v m probeEnergy broadening disorderStrength hbar pMax
  let x := finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
    v m p probeEnergy broadening disorderStrength hbar pMax
  let y := finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
    v m p probeEnergy broadening disorderStrength hbar pMax
  (2 : ℂ) * q ^ 2 * (-(x * beta + y * alpha))

/-- The full finite-`η` dressed Hall-surface angular trace is exactly the explicit radial
coefficient built from the existing `X/Y` rung coefficients and solved ladder coefficients. -/
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceIntegral_eq_radialCoefficient
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceIntegral
        e v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        e v m p probeEnergy broadening disorderStrength hbar pMax := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let alpha := finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
    v m probeEnergy broadening disorderStrength hbar pMax
  let beta := finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
    v m probeEnergy broadening disorderStrength hbar pMax
  let aR := finiteCutoffContinuumBornDysonScalarCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR := finiteCutoffContinuumBornDysonXCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR := finiteCutoffContinuumBornDysonZCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aA := finiteCutoffContinuumBornDysonScalarCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA := finiteCutoffContinuumBornDysonXCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA := finiteCutoffContinuumBornDysonZCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  have hjx : currentOperator .x e v = q • matrixOperator sigmaX := by
    dsimp [q]
    unfold currentOperator current velocity directionPauli matrixOperator
    rw [map_smul, map_smul]
    push_cast
    module
  have hjy : currentOperator .y e v = q • matrixOperator sigmaY := by
    dsimp [q]
    unfold currentOperator current velocity directionPauli matrixOperator
    rw [map_smul, map_smul]
    push_cast
    module
  have hsource :
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator
          e v m probeEnergy broadening disorderStrength hbar pMax =
        (q * (-beta)) • matrixOperator sigmaX +
          (q * alpha) • matrixOperator sigmaY := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator
      inPlaneCurrentOperator
    rw [hjx, hjy]
    module
  let ra : ℝ → ℂ := fun θ =>
    finiteDimensionalOperatorTrace
      ((q • matrixOperator sigmaX) *
        polarPauliOperator aR bR dR θ *
        ((q * (-beta)) • matrixOperator sigmaX +
          (q * alpha) • matrixOperator sigmaY) *
        polarPauliOperator aA bA dA θ)
  let rr : ℝ → ℂ := fun θ =>
    finiteDimensionalOperatorTrace
      ((q • matrixOperator sigmaX) *
        polarPauliOperator aR bR dR θ *
        (q • matrixOperator sigmaY) *
        polarPauliOperator aR bR dR θ)
  let aa : ℝ → ℂ := fun θ =>
    finiteDimensionalOperatorTrace
      ((q • matrixOperator sigmaX) *
        polarPauliOperator aA bA dA θ *
        (q • matrixOperator sigmaY) *
        polarPauliOperator aA bA dA θ)
  have hbridge :
      (fun θ : ℝ =>
        finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceTraceBridge
          e v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax) =
        fun θ : ℝ => ra θ - (1 / 2 : ℂ) * (rr θ + aa θ) := by
    funext θ
    unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceTraceBridge
      retardedAdvancedVertexTraceKernel sameSideVertexTraceRemainder twoGreenVertexTraceKernel
    rw [hjx, hjy, hsource]
    rw [finiteCutoffContinuumBornDysonGreenOperator_polar_eq,
      finiteCutoffContinuumBornDysonGreenOperator_polar_eq]
    have hcyclic :
        finiteDimensionalOperatorTrace
          ((q • matrixOperator sigmaY) * polarPauliOperator aA bA dA θ *
            (q • matrixOperator sigmaX) * polarPauliOperator aA bA dA θ) =
        finiteDimensionalOperatorTrace
          ((q • matrixOperator sigmaX) * polarPauliOperator aA bA dA θ *
            (q • matrixOperator sigmaY) * polarPauliOperator aA bA dA θ) := by
      simpa [mul_assoc] using
        (finiteDimensionalOperatorTrace_mul_comm
          ((q • matrixOperator sigmaY) * polarPauliOperator aA bA dA θ)
          ((q • matrixOperator sigmaX) * polarPauliOperator aA bA dA θ))
    rw [hcyclic]
  have hraIntegrable : IntervalIntegrable ra volume 0 (2 * Real.pi) := by
    simpa [ra] using
      intervalIntegrable_polarPauli_xyTrace
        q aR aA bR bA dR dA (q * (-beta)) (q * alpha)
  have hrrIntegrable : IntervalIntegrable rr volume 0 (2 * Real.pi) := by
    simpa [rr] using
      intervalIntegrable_polarPauli_xyTrace q aR aR bR bR dR dR 0 q
  have haaIntegrable : IntervalIntegrable aa volume 0 (2 * Real.pi) := by
    simpa [aa] using
      intervalIntegrable_polarPauli_xyTrace q aA aA bA bA dA dA 0 q
  have hra :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ra θ) =
        2 * q *
          (pauliRungAngularXCoefficient aR aA dR dA * (q * (-beta)) -
            pauliRungAngularYCoefficient aR aA dR dA * (q * alpha)) := by
    simpa [ra] using
      (integral_polarPauli_xyTrace_eq
        q aR aA bR bA dR dA (q * (-beta)) (q * alpha))
  have hrr : (∫ θ in (0 : ℝ)..(2 * Real.pi), rr θ) = 0 := by
    simpa [rr] using integral_polarPauli_sameSideXYTrace_eq_zero q aR bR dR
  have haa : (∫ θ in (0 : ℝ)..(2 * Real.pi), aa θ) = 0 := by
    simpa [aa] using integral_polarPauli_sameSideXYTrace_eq_zero q aA bA dA
  unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceIntegral
  rw [hbridge]
  rw [intervalIntegral.integral_sub hraIntegrable
    ((hrrIntegrable.add haaIntegrable).const_mul (1 / 2 : ℂ))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hrrIntegrable haaIntegrable, hra, hrr, haa]
  simp only [add_zero, mul_zero, sub_zero]
  unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  simp only [q, alpha, beta, aR, aA, dR, dA,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient]
  ring

/-- The #2011 radial integrand is the polar Jacobian `p` multiplying the explicit angularly reduced
Hall-surface coefficient. -/
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand
        e v m p probeEnergy broadening disorderStrength hbar pMax =
      (p : ℂ) *
        finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
          e v m p probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand
  rw [finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceIntegral_eq_radialCoefficient]

end

end QuantumTheory.Transport.Models.MassiveDirac
