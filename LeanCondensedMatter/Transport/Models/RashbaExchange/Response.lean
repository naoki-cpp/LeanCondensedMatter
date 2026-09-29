import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import LeanCondensedMatter.Transport.Models.RashbaExchange.Operator
import LeanCondensedMatter.Transport.Streda.ConductivityNormalization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite Rashba-exchange anomalous-Hall response

The clean finite-broadening response is routed through the canonical supplied-Green Středa surface
primitive `RA - (RR + AA)/2`. No phenomenological broadening factor is attached to the Berry
curvature. The latter remains independent clean-band data in `Model`.

The raw response integrates the point kernel over the explicit finite physical-momentum disk and
attaches the stored continuum-measure normalization exactly once. Only the subsequent conductivity
boundary attaches the common static Bastin–Středa trace prefactor. No cutoff-removal,
zero-broadening, weak-disorder, or universal-Hall-value statement is made here.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

def UsesCanonicalMomentumMeasure (params : Parameters) : Prop :=
  params.momentumMeasureNormalization = momentumMeasurePrefactor params.hbar

/-- Supplied-Green response seam. Disorder code may replace either Green operator and the source
vertex without reconstructing the Rashba Hamiltonian or measured charge-current vertex. -/
noncomputable def suppliedHallPointKernel
    (params : Parameters) (measured : Fin 2) (px py : ℝ)
    (retardedGreen sourceVertex advancedGreen :
      RashbaHilbert →L[ℂ] RashbaHilbert) : ℂ :=
  suppliedGreenStredaSurfacePrimitiveTraceKernel
    (currentBoundedOperator params measured px py)
    retardedGreen sourceVertex advancedGreen

/-- Exact clean finite-broadening Středa point kernel. -/
noncomputable def cleanHallPointKernel
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) : ℂ :=
  suppliedHallPointKernel params measured px py
    (greenOperator .retarded params px py)
    (currentBoundedOperator params source px py)
    (greenOperator .advanced params px py)

/-- The clean point kernel is exactly the generic regularized Středa surface primitive. -/
theorem cleanHallPointKernel_eq_regularized
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) :
    cleanHallPointKernel params measured source px py =
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator params px py)
        (currentBoundedOperator params measured px py)
        (currentBoundedOperator params source px py)
        params.chemicalPotential params.broadening := by
  symm
  simpa [cleanHallPointKernel, suppliedHallPointKernel, greenOperator] using
    (regularizedStredaSurfacePrimitiveTrace_eq_suppliedGreen
      (hamiltonianOperator params px py)
      (currentBoundedOperator params measured px py)
      (currentBoundedOperator params source px py)
      params.chemicalPotential params.broadening)

/-- Ordered Hall projection of the clean point response. Antisymmetry is algebraic and therefore
does not assume a rotational symmetry or a limiting procedure. -/
noncomputable def antisymmetricCleanHallPointKernel
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
    (cleanHallPointKernel params measured source px py -
      cleanHallPointKernel params source measured px py)

theorem antisymmetricCleanHallPointKernel_swap
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) :
    antisymmetricCleanHallPointKernel params source measured px py =
      -antisymmetricCleanHallPointKernel params measured source px py := by
  unfold antisymmetricCleanHallPointKernel
  ring

@[simp] theorem antisymmetricCleanHallPointKernel_self
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    antisymmetricCleanHallPointKernel params direction direction px py = 0 := by
  simp [antisymmetricCleanHallPointKernel]

/-- Restrict a point kernel to the explicit finite circular momentum domain. -/
noncomputable def finiteDiskHallIntegrand
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) : ℂ := by
  classical
  exact if inMomentumDomain params px py then
    antisymmetricCleanHallPointKernel params measured source px py
  else 0

/-- Finite-cutoff raw Hall response over the bounding square, with the disk restriction enforced
pointwise. The physical-momentum measure normalization is attached exactly once. -/
noncomputable def finiteCutoffHallResponseComponent
    (params : Parameters) (measured source : Fin 2) : ℂ :=
  ((params.momentumMeasureNormalization : ℝ) : ℂ) *
    ∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
      ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        finiteDiskHallIntegrand params measured source px py

theorem finiteDiskHallIntegrand_swap
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) :
    finiteDiskHallIntegrand params source measured px py =
      -finiteDiskHallIntegrand params measured source px py := by
  classical
  unfold finiteDiskHallIntegrand
  split
  · exact antisymmetricCleanHallPointKernel_swap params measured source px py
  · simp

theorem finiteCutoffHallResponseComponent_swap
    (params : Parameters) (measured source : Fin 2) :
    finiteCutoffHallResponseComponent params source measured =
      -finiteCutoffHallResponseComponent params measured source := by
  unfold finiteCutoffHallResponseComponent
  have hinner (px : ℝ) :
      (∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        finiteDiskHallIntegrand params source measured px py) =
        -(∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
          finiteDiskHallIntegrand params measured source px py) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro py _
    exact finiteDiskHallIntegrand_swap params measured source px py
  have houter :
      (∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
        ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
          finiteDiskHallIntegrand params source measured px py) =
        -(∫ px : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
          ∫ py : ℝ in (-params.momentumCutoff)..params.momentumCutoff,
            finiteDiskHallIntegrand params measured source px py) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro px _
    exact hinner px
  rw [houter]
  ring

/-- Physical conductivity component: the finite raw response receives the common static
Bastin–Středa trace prefactor only at this boundary. -/
noncomputable def finiteCutoffHallConductivityComponent
    (params : Parameters) (measured source : Fin 2) : ℂ :=
  ((bastinStredaTraceConductivityPrefactor params.hbar : ℝ) : ℂ) *
    finiteCutoffHallResponseComponent params measured source

noncomputable def finiteCutoffHallConductivityTensor
    (params : Parameters) : ConductivityTensor (Fin 2) where
  component := finiteCutoffHallConductivityComponent params

theorem finiteCutoffHallConductivityComponent_swap
    (params : Parameters) (measured source : Fin 2) :
    finiteCutoffHallConductivityComponent params source measured =
      -finiteCutoffHallConductivityComponent params measured source := by
  rw [finiteCutoffHallConductivityComponent, finiteCutoffHallConductivityComponent,
    finiteCutoffHallResponseComponent_swap]
  ring

end
end QuantumTheory.Transport.Models.RashbaExchange
