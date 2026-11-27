import LeanCondensedMatter.Models.OrbitalRelaxation.Finite
import LeanCondensedMatter.Analysis.Geometry.SphericalMoments
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Orbital fourth-moment cubature and physical spherical averages

Generic continuous spherical-coordinate integrals and fourth moments are proved in
`Analysis.Geometry.SphericalMoments`. Here the physical double-commutator average is evaluated directly with the
general even-quartic formula, without a finite-cubature comparison lemma.
The orbital relaxation rate is then identified with that continuous average
using the separately established finite cubature evaluation.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

open SphericalMoments

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
  rw [h]
  fin_cases axis
  · convert sphericalAverage_evenQuarticPolynomial r
        0 (c₁ ^ 2) (c₁ ^ 2) (c₂ ^ 2) (c₂ ^ 2)
        (4 * c₂ ^ 2 - 2 * c₁ ^ 2) using 1
    · congr 1; funext k; simp [orbitalPolynomial, evenQuarticPolynomial]; ring
    · ring
  · convert sphericalAverage_evenQuarticPolynomial r
        (c₁ ^ 2) 0 (c₁ ^ 2) (c₂ ^ 2)
        (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2) using 1
    · congr 1; funext k; simp [orbitalPolynomial, evenQuarticPolynomial]; ring
    · ring
  · convert sphericalAverage_evenQuarticPolynomial r
        (c₁ ^ 2) (c₁ ^ 2) 0
        (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2) (c₂ ^ 2) using 1
    · congr 1; funext k; simp [orbitalPolynomial, evenQuarticPolynomial]; ring
    · ring


/-- The finite-model rate equals the continuous spherical-coordinate average of its
exact matrix double commutator. The finite cubature is exact for this quartic integrand;
the second-order kinetic closure remains a separate physical assumption. -/
theorem orbitalRate_eq_sphericalAverage (axis : Fin 3)
    (ℏ τ₂ c₁ c₂ r : ℝ) :
    orbitalRate axis ℏ τ₂ c₁ c₂ r =
      τ₂ / ℏ ^ 2 * sphericalAverage r
        (orbitalDoubleCommutator axis c₁ c₂) := by
  rw [orbitalRate, evenQuarticCubature_orbitalDoubleCommutator,
    sphericalAverage_orbitalDoubleCommutator]

end QuantumTheory.Models.OrbitalRelaxation
