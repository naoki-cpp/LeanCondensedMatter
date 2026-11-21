import LeanCondensedMatter.Models.OrbitalRelaxation.Finite
import LeanCondensedMatter.Analysis.Geometry.SphericalMoments
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Orbital fourth-moment cubature and physical spherical averages

Generic continuous spherical-coordinate integrals and fourth moments are proved in
`Analysis.Geometry.SphericalMoments`. Here the orbital model's finite cubature
is compared with that continuous integral on a restricted quartic class,
then specialized to the physical double-commutator and orbital relaxation rate.
The cubature is not identified with the sphere average for arbitrary functions.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

open SphericalMoments

/-- Exactness of the finite cubature on *all* coordinate-even homogeneous
quartics, justified by the continuous spherical-coordinate integral. -/
private theorem sphericalAverage_evenQuartic_eq_cubature (r a b c d e f : ℝ) :
    sphericalAverage r (evenQuarticPolynomial a b c d e f) =
      evenQuarticCubature r (evenQuarticPolynomial a b c d e f) := by
  rw [sphericalAverage_evenQuarticPolynomial]
  simp [evenQuarticCubature, evenQuarticPolynomial]
  ring

/-- The orbital double-commutator quartic has the same continuous spherical
average as the finite cubature, for all three Cartesian polarizations. -/
theorem sphericalAverage_orbitalPolynomial_eq_cubature (axis : Fin 3)
    (c₁ c₂ r : ℝ) :
    sphericalAverage r (orbitalPolynomial axis c₁ c₂) =
      evenQuarticCubature r (orbitalPolynomial axis c₁ c₂) := by
  fin_cases axis
  · convert sphericalAverage_evenQuartic_eq_cubature r
      0 (c₁ ^ 2) (c₁ ^ 2) (c₂ ^ 2) (c₂ ^ 2)
      (4 * c₂ ^ 2 - 2 * c₁ ^ 2) using 1 <;>
      (congr 1; funext k; simp [orbitalPolynomial, evenQuarticPolynomial]; ring)
  · convert sphericalAverage_evenQuartic_eq_cubature r
      (c₁ ^ 2) 0 (c₁ ^ 2) (c₂ ^ 2)
      (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2) using 1 <;>
      (congr 1; funext k; simp [orbitalPolynomial, evenQuarticPolynomial]; ring)
  · convert sphericalAverage_evenQuartic_eq_cubature r
      (c₁ ^ 2) (c₁ ^ 2) 0
      (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2) (c₂ ^ 2) using 1 <;>
      (congr 1; funext k; simp [orbitalPolynomial, evenQuarticPolynomial]; ring)

/-- The exact matrix double commutator has the physical spherical-coordinate
fourth moment, without replacing the continuous angular integral by a cubature
assumption. -/
theorem sphericalAverage_orbitalDoubleCommutator (axis : Fin 3)
    (c₁ c₂ r : ℝ) :
    sphericalAverage r (orbitalDoubleCommutator axis c₁ c₂) =
      (2 * r ^ 4 / 15) * (2 * c₁ ^ 2 + 3 * c₂ ^ 2) := by
  have h : orbitalDoubleCommutator axis c₁ c₂ =
      orbitalPolynomial axis c₁ c₂ := by
    funext k
    exact orbitalDoubleCommutator_eq_polynomial axis c₁ c₂ k
  rw [h, sphericalAverage_orbitalPolynomial_eq_cubature,
    evenQuarticCubature_orbitalPolynomial]


/-- The previously defined finite-model rate equals the continuous
spherical-coordinate average of its exact matrix double commutator.
This replaces the cubature numerically on this quartic integrand only;
the second-order kinetic closure remains a separate physical assumption. -/
theorem orbitalRate_eq_sphericalAverage (axis : Fin 3)
    (ℏ τ₂ c₁ c₂ r : ℝ) :
    orbitalRate axis ℏ τ₂ c₁ c₂ r =
      τ₂ / ℏ ^ 2 * sphericalAverage r
        (orbitalDoubleCommutator axis c₁ c₂) := by
  rw [orbitalRate, evenQuarticCubature_orbitalDoubleCommutator,
    sphericalAverage_orbitalDoubleCommutator]

end QuantumTheory.Models.OrbitalRelaxation
