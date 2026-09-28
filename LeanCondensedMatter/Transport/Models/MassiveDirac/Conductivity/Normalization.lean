import LeanCondensedMatter.Transport.Streda.ConductivityNormalization

set_option linter.style.header false

/-!
# Massive-Dirac conductivity constants

Static Bastin–Středa trace and continuum-measure normalization is model-independent and owned by
`Transport.Streda.ConductivityNormalization`. This module retains only the massive-Dirac-facing
Planck-constant notation used by closed conductivity formulas.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Planck's constant expressed through the reduced Planck constant, `h = 2πℏ`. -/
def planckFromReduced (hbar : ℝ) : ℝ :=
  2 * Real.pi * hbar

end

end QuantumTheory.Transport.Models.MassiveDirac
