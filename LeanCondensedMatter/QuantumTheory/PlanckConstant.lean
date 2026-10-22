import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.header false

/-!
# Planck-constant conversion

The relation `h = 2πℏ` is independent of any particular Hamiltonian, model, or
transport formalism. This module owns the conversion shared by physical models.
-/

namespace QuantumTheory

/-- Planck's constant `h` expressed through the reduced Planck constant `ℏ`. -/
noncomputable def planckConstantFromReduced (hbar : ℝ) : ℝ :=
  2 * Real.pi * hbar

end QuantumTheory
