import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option linter.style.header false

/-!
# Lattice site geometry

Positions, oriented bond displacements, and scalar coordinates are independent of exchange
statistics and Fock-space realizations. First- and second-quantized lattice models
may use the same geometry.
-/

/-- Positions of lattice sites in a real vector space. -/
structure LatticeGeometry (Site E : Type*) where
  /-- Position of each site. -/
  position : Site → E

namespace LatticeGeometry

variable {Site E : Type*} [AddCommGroup E]

/-- Oriented displacement from `x` to `y`. -/
def bondDisplacement (geometry : LatticeGeometry Site E) (x y : Site) : E :=
  geometry.position y - geometry.position x

variable [Module ℝ E]

/-- Scalar bond coordinate measured by a real linear functional. -/
def bondCoordinate (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x y : Site) : ℝ :=
  direction (geometry.bondDisplacement x y)

end LatticeGeometry
