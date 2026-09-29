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

The physical clean finite-broadening Hall path uses the canonical traced Kubo–Bastin energy
integral at each momentum, takes its antisymmetric measured/source projection, and then integrates
that response over the explicit finite physical-momentum disk. The stored continuum-measure
normalization is attached exactly once, and the common static Bastin–Středa trace prefactor is
attached only when constructing a physical `ConductivityTensor`.

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

/-- Supplied-Green response seam. Disorder code may replace either Green operator and the source
vertex without reconstructing the Rashba Hamiltonian or measured charge-current vertex. -/
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

/-- Restrict the antisymmetric full Bastin point response to the explicit finite
circular momentum domain. -/
noncomputable def finiteDiskBastinHallIntegrand
    (params : Parameters) (measured source : Fin 2) (px py : ℝ)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : ℂ := by
  classical
  exact if inMomentumDomain params px py then
    antisymmetricCleanBastinPointResponse params measured source px py
      lowerEnergy upperEnergy occupation
  else 0

theorem finiteDiskBastinHallIntegrand_swap
    (params : Parameters) (measured source : Fin 2) (px py : ℝ)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) :
    finiteDiskBastinHallIntegrand params source measured px py
        lowerEnergy upperEnergy occupation =
      -finiteDiskBastinHallIntegrand params measured source px py
        lowerEnergy upperEnergy occupation := by
  classical
  unfold finiteDiskBastinHallIntegrand
  split
  · exact antisymmetricCleanBastinPointResponse_swap
      params measured source px py lowerEnergy upperEnergy occupation
  · simp

/-- Complete finite-cutoff, finite-broadening clean Hall response. The energy integral is the
canonical traced Bastin response; the outer momentum integral is restricted to the finite disk and
receives the explicit physical-momentum measure normalization exactly once. -/
noncomputable def finiteCutoffBastinHallResponseComponent
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : ℂ :=
  ((params.momentumMeasureNormalization : ℝ) : ℂ) *
    ∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
      ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        finiteDiskBastinHallIntegrand params measured source px py
          lowerEnergy upperEnergy occupation

theorem finiteCutoffBastinHallResponseComponent_swap
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) :
    finiteCutoffBastinHallResponseComponent params source measured
        lowerEnergy upperEnergy occupation =
      -finiteCutoffBastinHallResponseComponent params measured source
        lowerEnergy upperEnergy occupation := by
  unfold finiteCutoffBastinHallResponseComponent
  have hinner (px : ℝ) :
      (∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        finiteDiskBastinHallIntegrand params source measured px py
          lowerEnergy upperEnergy occupation) =
        -(∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
          finiteDiskBastinHallIntegrand params measured source px py
            lowerEnergy upperEnergy occupation) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro py _
    exact finiteDiskBastinHallIntegrand_swap params measured source px py
      lowerEnergy upperEnergy occupation
  have houter :
      (∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
          finiteDiskBastinHallIntegrand params source measured px py
            lowerEnergy upperEnergy occupation) =
        -(∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
          ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
            finiteDiskBastinHallIntegrand params measured source px py
              lowerEnergy upperEnergy occupation) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro px _
    exact hinner px
  rw [houter]
  ring

/-- Physical finite-cutoff Hall conductivity obtained only after the full Bastin energy response
and finite momentum integral have both been assembled. -/
noncomputable def finiteCutoffBastinHallConductivityComponent
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : ℂ :=
  ((bastinStredaTraceConductivityPrefactor params.hbar : ℝ) : ℂ) *
    finiteCutoffBastinHallResponseComponent params measured source
      lowerEnergy upperEnergy occupation

/-- Full finite-cutoff, finite-broadening anomalous-Hall conductivity tensor. -/
noncomputable def finiteCutoffBastinHallConductivityTensor
    (params : Parameters) (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) :
    ConductivityTensor (Fin 2) where
  component := fun measured source =>
    finiteCutoffBastinHallConductivityComponent params measured source
      lowerEnergy upperEnergy occupation

theorem finiteCutoffBastinHallConductivityComponent_swap
    (params : Parameters) (measured source : Fin 2)
    (lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) :
    finiteCutoffBastinHallConductivityComponent params source measured
        lowerEnergy upperEnergy occupation =
      -finiteCutoffBastinHallConductivityComponent params measured source
        lowerEnergy upperEnergy occupation := by
  rw [finiteCutoffBastinHallConductivityComponent,
    finiteCutoffBastinHallConductivityComponent,
    finiteCutoffBastinHallResponseComponent_swap]
  ring

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
