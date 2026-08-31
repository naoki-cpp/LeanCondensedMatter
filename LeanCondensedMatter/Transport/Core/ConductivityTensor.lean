import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# Conductivity tensors

This module owns the representation-independent tensor structure of electrical conductivity. It does
not assume a Kubo, Bastin, Středa, Boltzmann, or other representation. Concrete transport formalisms
must supply the physical normalization needed to construct this tensor from their response data.

Longitudinal and Hall components are projections of the completed conductivity tensor rather than
properties of any one representation.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Coordinate-indexed physical conductivity tensor, independent of how its components were
derived. -/
structure ConductivityTensor (ι : Type*) where
  /-- Conductivity component for one ordered measured/source coordinate pair. -/
  component : ι → ι → ℂ

namespace ConductivityTensor

variable {ι : Type*}

/-- Longitudinal conductivity along one selected coordinate. -/
noncomputable def longitudinal
    (conductivity : ConductivityTensor ι) (i : ι) : ℂ :=
  conductivity.component i i

/-- Hall conductivity component, defined as the antisymmetric part of the full conductivity tensor. -/
noncomputable def hallComponent
    (conductivity : ConductivityTensor ι) (i j : ι) : ℂ :=
  (conductivity.component i j - conductivity.component j i) / 2

/-- The Hall projection vanishes on the diagonal. -/
@[simp]
theorem hallComponent_self
    (conductivity : ConductivityTensor ι) (i : ι) :
    conductivity.hallComponent i i = 0 := by
  simp [hallComponent]

end ConductivityTensor

end
end Transport
end QuantumTheory
