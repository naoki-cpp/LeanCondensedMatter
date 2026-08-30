import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# Static Středa conductivity matrices

A static conductivity tensor should be represented before selecting a longitudinal or Hall channel.
This file contains only the matrix-level data and projections needed for that boundary. Construction
from Kubo/Středa analytic data belongs downstream, where common physical provenance can be kept
explicit.

The surface/sea split is not identified here with an intrinsic/extrinsic mechanism split.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Coordinate-indexed static conductivity data after a regularized Středa decomposition. -/
structure StaticStredaConductivityMatrix (ι : Type*) where
  /-- Regularized Fermi-surface conductivity contribution. -/
  fermiSurface : ι → ι → ℂ
  /-- Regularized Fermi-sea conductivity contribution. -/
  fermiSea : ι → ι → ℂ

namespace StaticStredaConductivityMatrix

variable {ι : Type*}

/-- Complete static conductivity matrix. -/
noncomputable def total (conductivity : StaticStredaConductivityMatrix ι) : ι → ι → ℂ :=
  fun i j => conductivity.fermiSurface i j + conductivity.fermiSea i j

/-- Longitudinal conductivity along one selected coordinate. -/
noncomputable def longitudinal
    (conductivity : StaticStredaConductivityMatrix ι) (i : ι) : ℂ :=
  conductivity.total i i

/-- Hall conductivity component, defined as the antisymmetric part of the complete conductivity
matrix. An off-diagonal entry equals this Hall component only under the corresponding antisymmetry
hypothesis. -/
noncomputable def hallComponent
    (conductivity : StaticStredaConductivityMatrix ι) (i j : ι) : ℂ :=
  (conductivity.total i j - conductivity.total j i) / 2

/-- The Hall component vanishes on the diagonal. -/
@[simp]
theorem hallComponent_self
    (conductivity : StaticStredaConductivityMatrix ι) (i : ι) :
    conductivity.hallComponent i i = 0 := by
  simp [hallComponent]

/-- If the total conductivity is antisymmetric in a coordinate pair, its off-diagonal entry is
already the Hall component for that pair. -/
theorem hallComponent_eq_total_of_antisymmetric
    (conductivity : StaticStredaConductivityMatrix ι) (i j : ι)
    (hantisym : conductivity.total j i = -conductivity.total i j) :
    conductivity.hallComponent i j = conductivity.total i j := by
  simp [hallComponent, hantisym]

end StaticStredaConductivityMatrix

end
end Transport
end QuantumTheory
