import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.header false

/-!
# Static Bastin–Středa conductivity normalization

This module owns scalar conductivity normalizations that depend only on the static
Bastin–Středa representation and an explicitly supplied measure normalization, not on a concrete
Hamiltonian, spatial dimension, particle statistics, disorder model, or current realization.

Current vertices are assumed to carry their physical charge normalization already. With that
convention, the traced static response receives the standard factor `ℏ/(2π)`; see Bastin et al.,
*J. Phys. Chem. Solids* **32**, 1811–1824 (1971),
[doi:10.1016/S0022-3697(71)80147-6](https://doi.org/10.1016/S0022-3697(71)80147-6), and the
Smrčka–Středa/Středa formulation cited in `notes/references.md`. Continuum measure normalization
is attached separately so response layers can make its provenance explicit and avoid
double-counting it. Dimension-specific continuum conventions deliberately live outside this
generic Středa module.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Trace normalization for a static Bastin–Středa response before any continuum momentum measure
is attached. The current operators are assumed to include their physical charge factors. -/
def bastinStredaTraceConductivityPrefactor (hbar : ℝ) : ℝ :=
  hbar / (2 * Real.pi)

/-- Combined normalization for a static Bastin–Středa response with an explicitly supplied
measure normalization. No spatial dimension or particular continuum measure is selected here. -/
def bastinStredaConductivityNormalization
    (hbar measureNormalization : ℝ) : ℝ :=
  bastinStredaTraceConductivityPrefactor hbar * measureNormalization

end

end Transport
end QuantumTheory
