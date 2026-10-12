import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Geometry of a single-particle lattice

Positions, oriented bond displacements, and scalar coordinates are independent of exchange
statistics and Fock-space realizations. Statistics-specific lattice-current constructions
consume this shared one-particle geometry.
-/

namespace QuantumMechanics.SingleParticle

/-- Positions of lattice sites in a real vector space. -/
structure LatticeGeometry (Site E : Type*) where
  /-- Position of each site. -/
  position : Site → E

namespace LatticeGeometry

variable {Site E : Type*} [AddCommGroup E]

/-- Oriented displacement from `x` to `y`. -/
def bondDisplacement (geometry : LatticeGeometry Site E) (x y : Site) : E :=
  geometry.position y - geometry.position x

/-- Reversing a bond reverses its displacement. -/
theorem bondDisplacement_swap (geometry : LatticeGeometry Site E) (x y : Site) :
    geometry.bondDisplacement y x = -geometry.bondDisplacement x y := by
  unfold bondDisplacement
  abel

variable [Module ℝ E]

/-- Scalar bond coordinate measured by a real linear functional. -/
def bondCoordinate (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x y : Site) : ℝ :=
  direction (geometry.bondDisplacement x y)

/-- Reversing a bond negates its scalar coordinate. -/
theorem bondCoordinate_swap (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x y : Site) :
    geometry.bondCoordinate direction y x =
      -geometry.bondCoordinate direction x y := by
  unfold bondCoordinate
  rw [bondDisplacement_swap, map_neg]

@[simp]
theorem bondCoordinate_self (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x : Site) :
    geometry.bondCoordinate direction x x = 0 := by
  unfold bondCoordinate bondDisplacement
  simp

end LatticeGeometry

end QuantumMechanics.SingleParticle
