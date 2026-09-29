import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import LeanCondensedMatter.Transport.Models.RashbaExchange.Operator
import LeanCondensedMatter.Transport.Streda.ConductivityNormalization
import LeanCondensedMatter.Transport.Streda.TraceRepresentation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite Rashba-exchange anomalous-Hall response

The physical clean finite-broadening path uses the canonical traced Kubo–Bastin energy integral at
each momentum and integrates each ordered measured/source component over the explicit finite
physical-momentum disk. The stored continuum-measure normalization is attached exactly once, and
the common static Bastin–Středa trace prefactor is attached only when constructing the full physical
`ConductivityTensor`. Its Hall response is then the canonical antisymmetric
`ConductivityTensor.hallComponent` projection of that completed tensor.

A separate supplied-Green Středa surface primitive `RA - (RR + AA)/2` is retained as the
response/vertex seam for future disorder dressing and as a diagnostic object; it is not promoted to
the physical Hall tensor by itself. No phenomenological broadening factor is attached to the Berry
curvature, which remains independent clean-band data in `Model`. No cutoff-removal,
zero-broadening, weak-disorder, or universal-Hall-value statement is made here.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- The explicit momentum normalization equals the canonical physical-momentum measure. -/
def UsesCanonicalMomentumMeasure (params : Parameters) : Prop :=
  params.momentumMeasureNormalization = momentumMeasurePrefactor params.hbar

/-- Supplied-Green Středa-surface response seam. Disorder code may replace either Green operator
and the source vertex without reconstructing the Rashba Hamiltonian or measured charge-current
vertex. This seam covers the surface channel only; no full disorder-dressed Bastin energy integral
is asserted here. -/
noncomputable def suppliedSurfaceHallPointKernel
    (params : Parameters) (measured : Fin 2) (px py : ℝ)
    (retardedGreen sourceVertex advancedGreen :
      EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) : ℂ :=
  suppliedGreenStredaSurfacePrimitiveTraceKernel
    (currentBoundedOperator params measured px py)
    retardedGreen sourceVertex advancedGreen

/-- Exact clean finite-broadening Středa point kernel. -/
noncomputable def cleanSurfaceHallPointKernel
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) : ℂ :=
  suppliedSurfaceHallPointKernel params measured px py
    (greenOperator .retarded params px py)
    (currentBoundedOperator params source px py)
    (greenOperator .advanced params px py)

/-- The disorder/vertex seam specialized to clean resolvents and the bare charge-current source
vertex is definitionally the clean surface kernel. -/
theorem suppliedSurfaceHallPointKernel_bare_eq_clean
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) :
    suppliedSurfaceHallPointKernel params measured px py
        (greenOperator .retarded params px py)
        (currentBoundedOperator params source px py)
        (greenOperator .advanced params px py) =
      cleanSurfaceHallPointKernel params measured source px py := by
  rfl

/-- The clean point kernel is exactly the generic regularized Středa surface primitive. -/
theorem cleanSurfaceHallPointKernel_eq_regularized
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) :
    cleanSurfaceHallPointKernel params measured source px py =
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator params px py)
        (currentBoundedOperator params measured px py)
        (currentBoundedOperator params source px py)
        params.chemicalPotential params.broadening := by
  symm
  simpa [cleanSurfaceHallPointKernel, suppliedSurfaceHallPointKernel, greenOperator] using
    (regularizedStredaSurfacePrimitiveTrace_eq_suppliedGreen
      (hamiltonianOperator params px py)
      (currentBoundedOperator params measured px py)
      (currentBoundedOperator params source px py)
      params.chemicalPotential params.broadening)

private theorem regularizedBastinOperatorIntegrand_scalarCurrent_swap
    (hamiltonian : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    (a b : ℂ) (energy broadening : ℝ) :
    regularizedBastinOperatorIntegrand
        hamiltonian
        (a • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
        (b • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
        energy broadening =
      regularizedBastinOperatorIntegrand
        hamiltonian
        (b • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
        (a • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
        energy broadening := by
  unfold regularizedBastinOperatorIntegrand
  simp [smul_smul, mul_comm]

private theorem regularizedBastinTraceIntegrand_scalarCurrent_swap
    (hamiltonian : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    (a b : ℂ) (energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        hamiltonian
        (a • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
        (b • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
        energy broadening =
      regularizedBastinTraceIntegrand
        hamiltonian
        (b • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
        (a • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
        energy broadening := by
  unfold regularizedBastinTraceIntegrand
  rw [regularizedBastinOperatorIntegrand_scalarCurrent_swap]

/-- Full finite-broadening Bastin response at one momentum point over an explicit finite energy
window. Unlike the surface primitive above, this is the complete canonical traced Bastin energy
integral and therefore retains both the surface-derivative and residual-sea contributions. -/
noncomputable def cleanBastinPointResponse
    (params : Parameters) (measured source : Fin 2) (px py : ℝ)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : ℂ :=
  regularizedTracedBastinEnergyIntegral
    (hamiltonianOperator params px py)
    (currentBoundedOperator params measured px py)
    (currentBoundedOperator params source px py)
    params.broadening lowerEnergy upperEnergy occupation

/-- Ordered Hall projection of the full finite-broadening Bastin response. -/
noncomputable def antisymmetricCleanBastinPointResponse
    (params : Parameters) (measured source : Fin 2) (px py : ℝ)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (cleanBastinPointResponse params measured source px py lowerEnergy upperEnergy occupation -
      cleanBastinPointResponse params source measured px py lowerEnergy upperEnergy occupation)

theorem antisymmetricCleanBastinPointResponse_swap
    (params : Parameters) (measured source : Fin 2) (px py : ℝ)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) :
    antisymmetricCleanBastinPointResponse params source measured px py
        lowerEnergy upperEnergy occupation =
      -antisymmetricCleanBastinPointResponse params measured source px py
        lowerEnergy upperEnergy occupation := by
  unfold antisymmetricCleanBastinPointResponse
  ring

/-- With zero Rashba coupling the two current vertices are scalar identity operators, so exchanging
the measured and source directions leaves the full finite-broadening Bastin response unchanged. -/
theorem cleanBastinPointResponse_rashba_zero_swap
    (params : Parameters) (measured source : Fin 2) (px py : ℝ)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (hAlpha : params.rashbaVelocity = 0) :
    cleanBastinPointResponse params measured source px py
        lowerEnergy upperEnergy occupation =
      cleanBastinPointResponse params source measured px py
        lowerEnergy upperEnergy occupation := by
  unfold cleanBastinPointResponse regularizedTracedBastinEnergyIntegral
  rw [currentBoundedOperator_rashba_zero params measured px py hAlpha,
    currentBoundedOperator_rashba_zero params source px py hAlpha]
  apply intervalIntegral.integral_congr
  intro energy _
  apply congrArg (fun z : ℂ => occupation energy * z)
  exact regularizedBastinTraceIntegrand_scalarCurrent_swap
    (hamiltonianOperator params px py)
    (((params.signedCharge *
      (if measured = 0 then px / params.effectiveMass else py / params.effectiveMass) : ℝ) : ℂ))
    (((params.signedCharge *
      (if source = 0 then px / params.effectiveMass else py / params.effectiveMass) : ℝ) : ℂ))
    energy params.broadening

/-- The full finite-broadening Hall projection vanishes pointwise when the Rashba coupling is zero. -/
@[simp] theorem antisymmetricCleanBastinPointResponse_rashba_zero
    (params : Parameters) (measured source : Fin 2) (px py : ℝ)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (hAlpha : params.rashbaVelocity = 0) :
    antisymmetricCleanBastinPointResponse params measured source px py
        lowerEnergy upperEnergy occupation = 0 := by
  unfold antisymmetricCleanBastinPointResponse
  rw [cleanBastinPointResponse_rashba_zero_swap
    params measured source px py lowerEnergy upperEnergy occupation hAlpha]
  ring

/-- Ordered Hall projection of the clean point response. Antisymmetry is algebraic and therefore
does not assume a rotational symmetry or a limiting procedure. -/
noncomputable def antisymmetricCleanSurfaceHallPointKernel
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
    (cleanSurfaceHallPointKernel params measured source px py -
      cleanSurfaceHallPointKernel params source measured px py)

theorem antisymmetricCleanSurfaceHallPointKernel_swap
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) :
    antisymmetricCleanSurfaceHallPointKernel params source measured px py =
      -antisymmetricCleanSurfaceHallPointKernel params measured source px py := by
  unfold antisymmetricCleanSurfaceHallPointKernel
  ring

@[simp] theorem antisymmetricCleanSurfaceHallPointKernel_self
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    antisymmetricCleanSurfaceHallPointKernel params direction direction px py = 0 := by
  simp [antisymmetricCleanSurfaceHallPointKernel]

/-- Restrict a point kernel to the explicit finite circular momentum domain. -/
noncomputable def finiteDiskSurfaceHallIntegrand
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) : ℂ := by
  classical
  exact if inMomentumDomain params px py then
    antisymmetricCleanSurfaceHallPointKernel params measured source px py
  else 0

/-- Finite-cutoff raw Hall response over the bounding square, with the disk restriction enforced
pointwise. The physical-momentum measure normalization is attached exactly once. -/
noncomputable def finiteCutoffSurfaceHallResponseComponent
    (params : Parameters) (measured source : Fin 2) : ℂ :=
  ((params.momentumMeasureNormalization : ℝ) : ℂ) *
    ∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
      ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        finiteDiskSurfaceHallIntegrand params measured source px py

theorem finiteDiskSurfaceHallIntegrand_swap
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) :
    finiteDiskSurfaceHallIntegrand params source measured px py =
      -finiteDiskSurfaceHallIntegrand params measured source px py := by
  classical
  unfold finiteDiskSurfaceHallIntegrand
  split
  · exact antisymmetricCleanSurfaceHallPointKernel_swap params measured source px py
  · simp

theorem finiteCutoffSurfaceHallResponseComponent_swap
    (params : Parameters) (measured source : Fin 2) :
    finiteCutoffSurfaceHallResponseComponent params source measured =
      -finiteCutoffSurfaceHallResponseComponent params measured source := by
  unfold finiteCutoffSurfaceHallResponseComponent
  have hinner (px : ℝ) :
      (∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        finiteDiskSurfaceHallIntegrand params source measured px py) =
        -(∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
          finiteDiskSurfaceHallIntegrand params measured source px py) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro py _
    exact finiteDiskSurfaceHallIntegrand_swap params measured source px py
  have houter :
      (∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
          finiteDiskSurfaceHallIntegrand params source measured px py) =
        -(∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
          ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
            finiteDiskSurfaceHallIntegrand params measured source px py) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro px _
    exact hinner px
  rw [houter]
  ring

/-- Restrict one ordered full Bastin point response to the explicit finite circular momentum
domain. No Hall projection is taken at this stage. -/
noncomputable def finiteDiskBastinIntegrand
    (params : Parameters) (measured source : Fin 2) (px py : ℝ)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : ℂ := by
  classical
  exact if inMomentumDomain params px py then
    cleanBastinPointResponse params measured source px py
      lowerEnergy upperEnergy occupation
  else 0

/-- At zero Rashba coupling the ordered finite-disk Bastin integrand is symmetric under exchange of
the measured and source directions. -/
theorem finiteDiskBastinIntegrand_rashba_zero_swap
    (params : Parameters) (measured source : Fin 2) (px py : ℝ)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (hAlpha : params.rashbaVelocity = 0) :
    finiteDiskBastinIntegrand params source measured px py
        lowerEnergy upperEnergy occupation =
      finiteDiskBastinIntegrand params measured source px py
        lowerEnergy upperEnergy occupation := by
  classical
  unfold finiteDiskBastinIntegrand
  split
  · exact cleanBastinPointResponse_rashba_zero_swap
      params source measured px py lowerEnergy upperEnergy occupation hAlpha
  · rfl

/-- Finite-cutoff ordered Bastin response component before physical conductivity normalization. -/
noncomputable def finiteCutoffBastinResponseComponent
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : ℂ :=
  ((params.momentumMeasureNormalization : ℝ) : ℂ) *
    ∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
      ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        finiteDiskBastinIntegrand params measured source px py
          lowerEnergy upperEnergy occupation

/-- Zero Rashba coupling makes the complete finite-cutoff ordered Bastin response symmetric. -/
theorem finiteCutoffBastinResponseComponent_rashba_zero_swap
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (hAlpha : params.rashbaVelocity = 0) :
    finiteCutoffBastinResponseComponent params source measured
        lowerEnergy upperEnergy occupation =
      finiteCutoffBastinResponseComponent params measured source
        lowerEnergy upperEnergy occupation := by
  unfold finiteCutoffBastinResponseComponent
  apply congrArg (fun z : ℂ => ((params.momentumMeasureNormalization : ℝ) : ℂ) * z)
  apply intervalIntegral.integral_congr
  intro px _
  apply intervalIntegral.integral_congr
  intro py _
  exact finiteDiskBastinIntegrand_rashba_zero_swap
    params measured source px py lowerEnergy upperEnergy occupation hAlpha

/-- Derived finite-cutoff Hall response, defined only after the ordered response components have
been assembled. -/
noncomputable def finiteCutoffBastinHallResponseComponent
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (finiteCutoffBastinResponseComponent params measured source
        lowerEnergy upperEnergy occupation -
      finiteCutoffBastinResponseComponent params source measured
        lowerEnergy upperEnergy occupation)

theorem finiteCutoffBastinHallResponseComponent_swap
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) :
    finiteCutoffBastinHallResponseComponent params source measured
        lowerEnergy upperEnergy occupation =
      -finiteCutoffBastinHallResponseComponent params measured source
        lowerEnergy upperEnergy occupation := by
  unfold finiteCutoffBastinHallResponseComponent
  ring

/-- The finite-cutoff Hall response vanishes when the Rashba coupling is zero. -/
@[simp] theorem finiteCutoffBastinHallResponseComponent_rashba_zero
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (hAlpha : params.rashbaVelocity = 0) :
    finiteCutoffBastinHallResponseComponent params measured source
        lowerEnergy upperEnergy occupation = 0 := by
  unfold finiteCutoffBastinHallResponseComponent
  rw [finiteCutoffBastinResponseComponent_rashba_zero_swap
    params measured source lowerEnergy upperEnergy occupation hAlpha]
  ring

/-- Physical finite-cutoff ordered conductivity component obtained only after the full Bastin
energy response and finite momentum integral have both been assembled. -/
noncomputable def finiteCutoffBastinConductivityComponent
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : ℂ :=
  ((bastinStredaTraceConductivityPrefactor params.hbar : ℝ) : ℂ) *
    finiteCutoffBastinResponseComponent params measured source
      lowerEnergy upperEnergy occupation

/-- Full finite-cutoff, finite-broadening conductivity tensor. Hall projection remains downstream
through `ConductivityTensor.hallComponent`. -/
noncomputable def finiteCutoffBastinConductivityTensor
    (params : Parameters) (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) :
    ConductivityTensor (Fin 2) where
  component := fun measured source =>
    finiteCutoffBastinConductivityComponent params measured source
      lowerEnergy upperEnergy occupation

@[simp] theorem finiteCutoffBastinConductivityTensor_component
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) :
    (finiteCutoffBastinConductivityTensor params lowerEnergy upperEnergy occupation).component
        measured source =
      finiteCutoffBastinConductivityComponent params measured source
        lowerEnergy upperEnergy occupation := rfl

/-- The Hall projection of the completed conductivity tensor is exactly the conductivity prefactor
times the derived finite-cutoff Hall response. -/
theorem finiteCutoffBastinConductivityTensor_hallComponent_eq
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) :
    (finiteCutoffBastinConductivityTensor params lowerEnergy upperEnergy occupation).hallComponent
        measured source =
      ((bastinStredaTraceConductivityPrefactor params.hbar : ℝ) : ℂ) *
        finiteCutoffBastinHallResponseComponent params measured source
          lowerEnergy upperEnergy occupation := by
  unfold ConductivityTensor.hallComponent finiteCutoffBastinConductivityTensor
    finiteCutoffBastinConductivityComponent finiteCutoffBastinHallResponseComponent
  ring

/-- The physical Hall conductivity vanishes at zero Rashba coupling. -/
@[simp] theorem finiteCutoffBastinConductivityTensor_hallComponent_rashba_zero
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (hAlpha : params.rashbaVelocity = 0) :
    (finiteCutoffBastinConductivityTensor params lowerEnergy upperEnergy occupation).hallComponent
        measured source = 0 := by
  rw [finiteCutoffBastinConductivityTensor_hallComponent_eq]
  simp [finiteCutoffBastinHallResponseComponent_rashba_zero
    params measured source lowerEnergy upperEnergy occupation hAlpha]

/-- Surface-projected normalized diagnostic. The common trace prefactor is useful for comparison,
but this object deliberately remains outside `ConductivityTensor`: the Středa surface primitive
at the chemical potential is not, by itself, the full Bastin Hall conductivity. -/
noncomputable def finiteCutoffSurfaceDiagnosticComponent
    (params : Parameters) (measured source : Fin 2) : ℂ :=
  ((bastinStredaTraceConductivityPrefactor params.hbar : ℝ) : ℂ) *
    finiteCutoffSurfaceHallResponseComponent params measured source

theorem finiteCutoffSurfaceDiagnosticComponent_swap
    (params : Parameters) (measured source : Fin 2) :
    finiteCutoffSurfaceDiagnosticComponent params source measured =
      -finiteCutoffSurfaceDiagnosticComponent params measured source := by
  rw [finiteCutoffSurfaceDiagnosticComponent, finiteCutoffSurfaceDiagnosticComponent,
    finiteCutoffSurfaceHallResponseComponent_swap]
  ring

end
end QuantumTheory.Transport.Models.RashbaExchange
