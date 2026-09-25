import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadderLongitudinalZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.TransportDomain
import Mathlib.Tactic

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

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Finite-`η` rotational closure makes the physically normalized ordered `yx` tensor component the
negative of ordered `xy`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_yx_eq_neg_xy
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
        e v m probeEnergy broadening disorderStrength hbar pMax).component 1 0 =
      -(finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
        e v m probeEnergy broadening disorderStrength hbar pMax).component 0 1 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yx_eq_neg_xy]

/-- Finite-`η` rotational closure makes the two physically normalized diagonal tensor components
equal. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_yy_eq_xx
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
        e v m probeEnergy broadening disorderStrength hbar pMax).component 1 1 =
      (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
        e v m probeEnergy broadening disorderStrength hbar pMax).component 0 0 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yy_eq_xx]

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
  rcases regime with ⟨v, m, probeEnergy, disorderStrength, hbar, pMax, hpMax, hvelocity, hhbar,
    hdisorder, hmetal, hcutoff⟩
  have hxx :=
    tendsto_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivity_broadening_zero
      e v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  have hxy :=
    tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivity_broadening_zero
      e v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  fin_cases measured <;> fin_cases source
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary] using hxx
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary] using hxy
  · apply Tendsto.congr' ?_ hxy.neg
    filter_upwards with broadening
    exact (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_yx_eq_neg_xy
      e v m probeEnergy broadening disorderStrength hbar pMax).symm
  · apply Tendsto.congr' ?_ hxx
    filter_upwards with broadening
    exact (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_yy_eq_xx
      e v m probeEnergy broadening disorderStrength hbar pMax).symm

end

end QuantumTheory.Transport.Models.MassiveDirac
