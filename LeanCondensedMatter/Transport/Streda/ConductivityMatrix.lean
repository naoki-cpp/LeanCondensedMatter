import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# Regularized surface/sea conductivity matrices

This file contains only coordinate-indexed conductivity data split into the regularized surface and
residual-sea contributions supplied by the current Středa integration layer. It deliberately does
not identify the residual sea term with the conventional Smrčka–Středa II contribution.

Consequently no sea antisymmetry or vanishing diagonal is assumed here. A physical Středa I/II
matrix should be introduced only after those properties are proved under the necessary hypotheses.
The surface/sea split is also not identified with an intrinsic/extrinsic mechanism split.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Coordinate-indexed conductivity data with regularized surface and residual-sea contributions. -/
structure RegularizedSurfaceSeaConductivityMatrix (ι : Type*) where
  /-- Regularized Fermi-surface conductivity contribution. -/
  fermiSurface : ι → ι → ℂ
  /-- Regularized residual Fermi-sea conductivity contribution. -/
  fermiSea : ι → ι → ℂ

namespace RegularizedSurfaceSeaConductivityMatrix

variable {ι : Type*}

/-- Complete conductivity matrix represented by the surface/sea split. -/
noncomputable def total
    (conductivity : RegularizedSurfaceSeaConductivityMatrix ι) : ι → ι → ℂ :=
  fun i j => conductivity.fermiSurface i j + conductivity.fermiSea i j

/-- Diagonal conductivity along one selected coordinate. No claim that the residual sea part
vanishes is made here. -/
noncomputable def longitudinal
    (conductivity : RegularizedSurfaceSeaConductivityMatrix ι) (i : ι) : ℂ :=
  conductivity.total i i

/-- Antisymmetric part of the complete conductivity matrix. This becomes the Hall conductivity when
the corresponding physical identification has been established. -/
noncomputable def antisymmetricComponent
    (conductivity : RegularizedSurfaceSeaConductivityMatrix ι) (i j : ι) : ℂ :=
  (conductivity.total i j - conductivity.total j i) / 2

/-- The antisymmetric component vanishes on the diagonal. -/
@[simp]
theorem antisymmetricComponent_self
    (conductivity : RegularizedSurfaceSeaConductivityMatrix ι) (i : ι) :
    conductivity.antisymmetricComponent i i = 0 := by
  simp [antisymmetricComponent]

end RegularizedSurfaceSeaConductivityMatrix

end
end Transport
end QuantumTheory
