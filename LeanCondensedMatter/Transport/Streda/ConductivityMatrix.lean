import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Static Středa conductivity matrices

A static Středa conductivity matrix consists of its Fermi-surface and Fermi-sea contributions,
with the sea contribution antisymmetric under exchange of measured-current and source-field
coordinates. The antisymmetry makes the sea contribution vanish on the diagonal, so longitudinal
conductivity is the diagonal Fermi-surface contribution.

This analytic surface/sea split is not identified here with an intrinsic/extrinsic mechanism split.
Construction from concrete Kubo/Středa data is intentionally kept separate so that its physical
provenance remains explicit.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Coordinate-indexed static Středa conductivity data. The sea contribution carries its defining
antisymmetry as an invariant rather than as a convention on off-diagonal entries. -/
structure StaticStredaConductivityMatrix (ι : Type*) where
  /-- Fermi-surface conductivity contribution. -/
  fermiSurface : ι → ι → ℂ
  /-- Fermi-sea conductivity contribution. -/
  fermiSea : ι → ι → ℂ
  /-- The Středa sea contribution is antisymmetric in its current/source indices. -/
  fermiSea_swap : ∀ i j, fermiSea i j = -fermiSea j i

namespace StaticStredaConductivityMatrix

variable {ι : Type*}

/-- Complete static conductivity matrix. -/
noncomputable def total (conductivity : StaticStredaConductivityMatrix ι) : ι → ι → ℂ :=
  fun i j => conductivity.fermiSurface i j + conductivity.fermiSea i j

/-- The Fermi-sea contribution vanishes on the diagonal. -/
@[simp]
theorem fermiSea_self
    (conductivity : StaticStredaConductivityMatrix ι) (i : ι) :
    conductivity.fermiSea i i = 0 := by
  have hsum :
      conductivity.fermiSea i i + conductivity.fermiSea i i = 0 := by
    calc
      conductivity.fermiSea i i + conductivity.fermiSea i i =
          -conductivity.fermiSea i i + conductivity.fermiSea i i := by
        rw [conductivity.fermiSea_swap i i]
      _ = 0 := neg_add_cancel _
  have htwo : (2 : ℂ) * conductivity.fermiSea i i = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Longitudinal conductivity along one selected coordinate. -/
noncomputable def longitudinal
    (conductivity : StaticStredaConductivityMatrix ι) (i : ι) : ℂ :=
  conductivity.total i i

/-- The longitudinal conductivity is entirely the diagonal Fermi-surface contribution. -/
theorem longitudinal_eq_fermiSurface
    (conductivity : StaticStredaConductivityMatrix ι) (i : ι) :
    conductivity.longitudinal i = conductivity.fermiSurface i i := by
  simp [longitudinal, total]

/-- Hall conductivity component, defined as the antisymmetric part of the complete conductivity
matrix rather than as an arbitrary off-diagonal entry. -/
noncomputable def hallComponent
    (conductivity : StaticStredaConductivityMatrix ι) (i j : ι) : ℂ :=
  (conductivity.total i j - conductivity.total j i) / 2

/-- The Hall component vanishes on the diagonal. -/
@[simp]
theorem hallComponent_self
    (conductivity : StaticStredaConductivityMatrix ι) (i : ι) :
    conductivity.hallComponent i i = 0 := by
  simp [hallComponent]

end StaticStredaConductivityMatrix

end
end Transport
end QuantumTheory
