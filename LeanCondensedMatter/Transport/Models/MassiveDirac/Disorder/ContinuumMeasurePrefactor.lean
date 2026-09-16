import LeanCondensedMatter.Transport.Core.ContinuumMeasure

set_option linter.style.header false

/-!
# Massive-Dirac continuum disorder-measure prefactor

This module owns the shared external scalar-disorder-line factor multiplying a continuum radial
kernel after its full polar-angle integration has already been performed. The generic
physical-momentum measure remains owned by `Transport.Core.ContinuumMeasure`; this file only binds
that measure to the massive-Dirac continuum Born disorder parameter.

No angular reduction, propagator, ladder, response, or conductivity normalization is introduced
here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- External scalar-disorder line and one physical-momentum measure factor for an angular-reduced
continuum Born kernel. Any full-angle `2π` factor belongs to the upstream angular coefficient. -/
def continuumBornRetardedAdvancedCurrentRungPrefactor
    (disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength * momentumMeasurePrefactor hbar

end

end QuantumTheory.Transport.Models.MassiveDirac
