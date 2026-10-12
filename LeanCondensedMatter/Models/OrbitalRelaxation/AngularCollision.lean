import LeanCondensedMatter.Models.OrbitalRelaxation.Finite
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite angular collision modes

A finite set of momentum directions carries a scattering kernel. Its zeroth,
first, and traceless second coordinate moments determine the action of the
collision operator on the first two nonconstant angular modes. These moment
identities are explicit hypotheses: deriving them from a rotationally invariant
continuous kernel or a microscopic disorder ensemble is a separate step.

The mode distinction follows the orbital kinetic calculation of Sohn, Lee,
and Lee, Phys. Rev. Lett. 132, 246301 (2024), supplemental Sec. I.A.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- Gain-minus-loss action of a finite angular scattering kernel. -/
def angularCollision (kernel : Ω → Ω → ℝ) (f : Ω → ℝ) (p : Ω) : ℝ :=
  ∑ q, kernel p q * (f q - f p)

theorem angularCollision_eq (kernel : Ω → Ω → ℝ) (f : Ω → ℝ) (p : Ω) :
    angularCollision kernel f p =
      (∑ q, kernel p q * f q) - (∑ q, kernel p q) * f p := by
  simp [angularCollision, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

/-- Coordinate direction mode, the finite analogue of a degree-one spherical harmonic. -/
def coordinateMode (direction : Ω → Fin 3 → ℝ) (i : Fin 3) (p : Ω) : ℝ :=
  direction p i

/-- Traceless coordinate-quadratic mode, the finite analogue of degree two. -/
noncomputable def quadrupoleMode
    (direction : Ω → Fin 3 → ℝ) (i j : Fin 3) (p : Ω) : ℝ :=
  direction p i * direction p j - (if i = j then (1 / 3 : ℝ) else 0)

/-- Moment data for a finite angular kernel. Rotationally invariant scattering
is expected to produce these identities; they are assumed, not inferred from
the kernel alone. `firstCoefficient` and `secondCoefficient` are gain moments. -/
structure AngularKernelMoments (Ω : Type*) [Fintype Ω] where
  direction : Ω → Fin 3 → ℝ
  unit_direction : ∀ p, ∑ i, direction p i ^ 2 = 1
  kernel : Ω → Ω → ℝ
  totalRate : ℝ
  firstCoefficient : ℝ
  secondCoefficient : ℝ
  total_moment : ∀ p, ∑ q, kernel p q = totalRate
  first_moment : ∀ p i,
    ∑ q, kernel p q * direction q i = firstCoefficient * direction p i
  second_moment : ∀ p i j,
    ∑ q, kernel p q * (direction q i * direction q j) =
      (totalRate - secondCoefficient) / 3 * (if i = j then (1 : ℝ) else 0) +
        secondCoefficient * (direction p i * direction p j)

namespace AngularKernelMoments

variable (data : AngularKernelMoments Ω)

/-- Loss rate of the coordinate mode. -/
def momentumRate : ℝ := data.totalRate - data.firstCoefficient

/-- Loss rate of the traceless quadratic mode. -/
def degreeTwoRate : ℝ := data.totalRate - data.secondCoefficient

/-- The coordinate mode is an eigenfunction of the collision action. -/
theorem collision_coordinate (p : Ω) (i : Fin 3) :
    angularCollision data.kernel (coordinateMode data.direction i) p =
      -data.momentumRate * coordinateMode data.direction i p := by
  rw [angularCollision_eq]
  simp only [coordinateMode, data.first_moment, data.total_moment, momentumRate]
  ring

private theorem quadrupole_gain (p : Ω) (i j : Fin 3) :
    (∑ q, data.kernel p q * quadrupoleMode data.direction i j q) =
      data.secondCoefficient * quadrupoleMode data.direction i j p := by
  simp only [quadrupoleMode]
  calc
    (∑ q, data.kernel p q *
        (data.direction q i * data.direction q j -
          if i = j then (1 / 3 : ℝ) else 0)) =
        (∑ q, data.kernel p q * (data.direction q i * data.direction q j)) -
          (∑ q, data.kernel p q) * (if i = j then (1 / 3 : ℝ) else 0) := by
          simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = data.secondCoefficient *
        (data.direction p i * data.direction p j -
          if i = j then (1 / 3 : ℝ) else 0) := by
          rw [data.second_moment p i j, data.total_moment p]
          split_ifs <;> ring

/-- The traceless quadratic mode is an eigenfunction of the collision action. -/
theorem collision_quadrupole (p : Ω) (i j : Fin 3) :
    angularCollision data.kernel (quadrupoleMode data.direction i j) p =
      -data.degreeTwoRate * quadrupoleMode data.direction i j p := by
  rw [angularCollision_eq, data.quadrupole_gain p i j, data.total_moment p]
  unfold degreeTwoRate
  ring

end AngularKernelMoments

end QuantumTheory.Models.OrbitalRelaxation
