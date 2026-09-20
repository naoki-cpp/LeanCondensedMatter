import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure

set_option linter.style.header false

/-!
# Massive-Dirac continuum disorder-measure prefactor

This module binds one continuum Born scalar-disorder line to exactly one two-dimensional physical-momentum
measure. Angular reduction and response/conductivity normalization remain downstream responsibilities.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- One continuum Born scalar-disorder line with one physical-momentum measure factor. -/
def continuumBornDisorderMeasurePrefactor
    (disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength * momentumMeasurePrefactor hbar

end

end QuantumTheory.Transport.Models.MassiveDirac
