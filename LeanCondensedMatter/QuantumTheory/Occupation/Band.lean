import Mathlib.Basic.Real.Basic

set_option linter.style.header false

/-!
# Band occupation derived from a spectral energy law

This module owns the model-independent composition of an arbitrary energy occupation law with a
band-energy function. It is independent of transport response, zero-temperature filling predicates,
and Fermi-edge integral analysis.
-/

namespace QuantumTheory

noncomputable section

variable {Band K : Type*}

/-- Occupation assigned to one band state by composing an energy occupation law with the spectrum. -/
def bandStateOccupation
    (occupation : ℝ → ℝ) (energy : Band → K → ℝ) (band : Band) (k : K) : ℝ :=
  occupation (energy band k)

end
end QuantumTheory
