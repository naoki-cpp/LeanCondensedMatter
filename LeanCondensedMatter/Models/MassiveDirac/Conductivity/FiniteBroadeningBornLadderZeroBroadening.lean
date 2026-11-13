import LeanCondensedMatter.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadder
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadderLongitudinalZeroBroadening
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.Radial
import LeanCondensedMatter.Models.MassiveDirac.TransportDomain

set_option linter.style.header false

/-!
# Zero-broadening massive-Dirac conductivity tensor

This module owns the physical `ConductivityTensor (Fin 2)` seam after the componentwise
zero-broadening boundary has been formed. The ordered `xx` and `xy` scalar boundaries remain
owned by their component modules; this layer completes the tensor using rotational closure and
propagates the common broadening limit to every component.

The Hall projection is deliberately downstream. It consumes this neutral tensor seam rather than
owning the tensor boundary itself.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open Filter QuantumTheory.Transport

/-- The finite-broadening dressed Středa conductivity tensor has the planar-isotropic
component structure proved by the angular and radial response identities. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_isPlanarIsotropic
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
      e v m probeEnergy broadening disorderStrength hbar pMax).IsPlanarIsotropic := by
  constructor
  · simp [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yy_eq_xx]
  · simp [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yx_eq_neg_xy]

/-- Physical fixed-cutoff conductivity tensor after the componentwise `η → 0⁺` boundary has been
formed at fixed positive disorder. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) : ConductivityTensor (Fin 2) where
  component :=
    let xx :=
      finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
        e v m probeEnergy disorderStrength hbar pMax
    let xy :=
      finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
        e v m probeEnergy disorderStrength hbar pMax
    !![xx, xy; -xy, xx]

/-- Every finite-`η` conductivity tensor component converges to the corresponding entry of the
physical zero-broadening conductivity tensor. The off-diagonal `yx` and diagonal `yy` cases are
obtained from the finite-`η` rotational identities rather than assigned independently. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_broadening_zero
    (measured source : Fin 2)
    (e : ℝ) (regime : FixedCutoffMetallicBornRegime)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
          e regime.v regime.m regime.probeEnergy broadening regime.disorderStrength regime.hbar
          regime.pMax).component measured source)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
          e regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax).component
          measured source)) := by
  have hxx :=
    tendsto_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivity_broadening_zero
      e regime hrenorm hdet
  have hxy :=
    tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivity_broadening_zero
      e regime hrenorm hdet
  have hiso (broadening : ℝ) :=
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_isPlanarIsotropic
      e regime.v regime.m regime.probeEnergy broadening regime.disorderStrength regime.hbar
        regime.pMax
  fin_cases measured <;> fin_cases source
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary] using hxx
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary] using hxy
  · apply Tendsto.congr' ?_ hxy.neg
    filter_upwards with broadening
    exact (hiso broadening).2.symm
  · apply Tendsto.congr' ?_ hxx
    filter_upwards with broadening
    exact (hiso broadening).1.symm

end

end QuantumTheory.Models.MassiveDirac
