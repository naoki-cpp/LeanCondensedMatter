import LeanCondensedMatter.Transport.Core.ContinuumMeasure

set_option linter.style.header false

/-!
# Massive-Dirac continuum disorder-measure prefactor

This module owns the shared external scalar-disorder-line factor multiplying one physical-momentum
continuum measure. The generic measure itself remains owned by `Transport.Core.ContinuumMeasure`;
this file only binds that measure to the massive-Dirac continuum Born disorder parameter.

Consumers may place angular reduction before or after this factor according to their kernel
representation. No angular reduction, propagator, ladder, response, or conductivity normalization
is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- One continuum Born scalar-disorder line together with exactly one physical-momentum measure
factor. Angular factors are supplied separately by the representation that performs the reduction. -/
def continuumBornDisorderMeasurePrefactor
    (disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength * momentumMeasurePrefactor hbar

/-- RA current-rung specialization of the canonical continuum Born disorder-measure factor.
The name records that the full angular factor is already carried by the rung coefficient. -/
abbrev continuumBornRetardedAdvancedCurrentRungPrefactor :=
  continuumBornDisorderMeasurePrefactor

end

end QuantumTheory.Transport.Models.MassiveDirac
