import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Generic band-state occupation

This module owns the model-independent composition of an arbitrary energy occupation law with a
band-energy function. It contains no zero-temperature filling predicates or Fermi-edge analysis, so
finite-temperature and other arbitrary-occupation consumers can depend on this layer alone.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {Band K : Type*}

/-- Occupation assigned to one band state by composing an energy occupation law with the spectrum. -/
def bandStateOccupation
    (occupation : ℝ → ℝ) (energy : Band → K → ℝ) (band : Band) (k : K) : ℝ :=
  occupation (energy band k)

end
end Transport
end QuantumTheory
