import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Transport relaxation-time input

This module owns the minimal positive time-scale datum used by phenomenological longitudinal
transport approximations.  A `PositiveTransportLifetime` is a current-relaxation time supplied to a
transport formula; it is deliberately distinct from a single-particle lifetime extracted from a
self-energy.

No microscopic scattering model, Born approximation, vertex correction, or conductivity formula is
encoded here.  Downstream derivations may later prove that a disorder calculation produces this
transport lifetime.
-/

namespace QuantumTheory
namespace Transport

/-- Positive transport relaxation time `τ_tr`.  Unless a downstream theorem derives it from a
microscopic collision or vertex problem, this datum is an explicit phenomenological input. -/
structure PositiveTransportLifetime where
  /-- Transport relaxation time. -/
  lifetime : ℝ
  lifetime_pos : 0 < lifetime

end Transport
end QuantumTheory
