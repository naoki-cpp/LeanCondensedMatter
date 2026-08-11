import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Positive finite physical volume

This module owns the minimal finite-volume datum shared by transport systems and intensive response
normalizations. Physical volume is independent of Hilbert-space dimension and of any particular
Hamiltonian, current, trace, or model representation.
-/

namespace QuantumTheory
namespace Transport

/-- A positive finite physical volume, independent of the system or model carrying it. -/
structure PositiveVolume where
  /-- Physical volume of the finite sample. -/
  volume : ℝ
  volume_pos : 0 < volume

end Transport
end QuantumTheory
