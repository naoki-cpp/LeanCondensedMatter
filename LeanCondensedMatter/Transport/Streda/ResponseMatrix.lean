import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Static Středa response matrices

A static Středa response matrix consists of its Fermi-surface and Fermi-sea contributions, with the
sea contribution antisymmetric under exchange of measured-current and source coordinates. The
antisymmetry makes the sea contribution vanish on the diagonal.

These entries are regularized response contributions. This module does not identify them with a
physical conductivity before the required physical normalization or continuum integration is
supplied downstream. The analytic surface/sea split is also not identified with an
intrinsic/extrinsic mechanism split.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Coordinate-indexed static Středa response data. The sea contribution carries its defining
antisymmetry as an invariant rather than as a convention on off-diagonal entries. -/
structure StaticStredaResponseMatrix (ι : Type*) where
  /-- Fermi-surface response contribution. -/
  fermiSurface : ι → ι → ℂ
  /-- Fermi-sea response contribution. -/
  fermiSea : ι → ι → ℂ
  /-- The Středa sea contribution is antisymmetric in its current/source indices. -/
  fermiSea_swap : ∀ i j, fermiSea i j = -fermiSea j i

namespace StaticStredaResponseMatrix

variable {ι : Type*}

/-- Complete static Středa response matrix. -/
noncomputable def total (response : StaticStredaResponseMatrix ι) : ι → ι → ℂ :=
  fun i j => response.fermiSurface i j + response.fermiSea i j

/-- The Fermi-sea contribution vanishes on the diagonal. -/
@[simp]
theorem fermiSea_self
    (response : StaticStredaResponseMatrix ι) (i : ι) :
    response.fermiSea i i = 0 :=
  CharZero.eq_neg_self_iff.mp (response.fermiSea_swap i i)

/-- A diagonal total response is entirely the diagonal Fermi-surface contribution. -/
theorem total_self_eq_fermiSurface
    (response : StaticStredaResponseMatrix ι) (i : ι) :
    response.total i i = response.fermiSurface i i := by
  simp [total]

end StaticStredaResponseMatrix

end
end Transport
end QuantumTheory
