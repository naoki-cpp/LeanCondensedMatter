import LeanCondensedMatter.Transport.Core.ConductivityTensor
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderIntegral

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson Středa conductivity tensor

This module is the physical-normalization boundary for the finite-cutoff finite-`η` massive-Dirac
Středa surface response with measured-current and source directions indexed by `Direction2`. The
upstream Středa layer owns the pair-indexed pointwise trace and polar momentum integration; this layer
attaches the common static Bastin/Středa conductivity prefactor and physical two-dimensional
momentum-measure normalization exactly once and packages the ordered components in the canonical
`ConductivityTensor Direction2` representation.

The value is a total Born-Dyson candidate; ladder regularity is a separate condition for interpreting
the solved vertex coefficients as the physical fixed point. No disorder, broadening, ultraviolet,
thermodynamic, or simultaneous limit is taken, and the candidate is not identified with an exact
disorder average.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Physically normalized finite-cutoff finite-`η` Středa surface conductivity tensor. The upstream
angle integral already supplies the angular measure, so `momentumMeasurePrefactor hbar` is attached
without an additional `2π` factor. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    ConductivityTensor Direction2 where
  component := fun measured source =>
    ((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        measured source e v m probeEnergy broadening disorderStrength hbar pMax

end

end QuantumTheory.Transport.Models.MassiveDirac
