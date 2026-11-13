import LeanCondensedMatter.Models.OrbitalRelaxation.KineticClosure
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# A concrete dot-product scattering kernel on six Cartesian directions

This finite angular-scattering benchmark uses the six unit directions
`±e₁, ±e₂, ±e₃`, with transition weights `W(p · q)`.
Their dot products are in `{-1, 0, 1}`. Exact finite sums establish the
zeroth-, first-, and second-moment equations of `AngularKernelMoments`
*without assuming* those equations.

The quadrupole relaxation rate can then be computed both as an eigenvalue
of the collision operator and as a finite Legendre-weighted angular sum.
This is a discrete cubic grid, not the continuous SO(3)-invariant
sphere integral. In particular the off-diagonal quadrupoles vanish
identically on this grid, while the diagonal quadrupoles are nonzero.
The stationary kinetic closure remains a separate physical hypothesis.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

open scoped BigOperators

/-- The six signed Cartesian unit vectors in three dimensions. -/
def octahedralDirection (p : Fin 6) : Fin 3 → ℝ :=
  ![
    ![1, 0, 0], ![-1, 0, 0],
    ![0, 1, 0], ![0, -1, 0],
    ![0, 0, 1], ![0, 0, -1]
  ] p

/-- The cosine of the scattering angle between two of the six directions. -/
def octahedralCosine (p q : Fin 6) : ℝ :=
  ∑ i : Fin 3, octahedralDirection p i * octahedralDirection q i

/-- An isotropic (dot-product) kernel restricted to the six-direction grid.
No smoothness of the sampled function `W` is required. -/
def octahedralKernel (W : ℝ → ℝ) (p q : Fin 6) : ℝ :=
  W (octahedralCosine p q)

/-- Degree-two Legendre polynomial on the cosine of the scattering angle. -/
def legendreP2 (μ : ℝ) : ℝ := (3 * μ ^ 2 - 1) / 2

/-- The octahedral dot-product kernel automatically satisfies the moments
needed for first and diagonal second angular modes. Only the three sampled
values of `W` need to be nonnegative. -/
noncomputable def octahedralMoments (W : ℝ → ℝ)
    (hplus : 0 ≤ W 1) (hminus : 0 ≤ W (-1)) (horth : 0 ≤ W 0) :
    AngularKernelMoments (Fin 6) where
  direction := octahedralDirection
  unit_direction := by
    intro p
    fin_cases p <;> norm_num [octahedralDirection, Fin.sum_univ_three]
  kernel := octahedralKernel W
  kernel_nonneg := by
    intro p q
    fin_cases p <;> fin_cases q <;>
      simp [octahedralKernel, octahedralCosine, octahedralDirection,
        Fin.sum_univ_three, hplus, hminus, horth]
  totalRate := W 1 + W (-1) + 4 * W 0
  firstCoefficient := W 1 - W (-1)
  secondCoefficient := W 1 + W (-1) - 2 * W 0
  total_moment := by
    intro p
    fin_cases p <;>
      simp [octahedralKernel, octahedralCosine, octahedralDirection,
        Fin.sum_univ_six, Fin.sum_univ_three] <;> ring
  first_moment := by
    intro p i
    fin_cases p <;> fin_cases i <;>
      simp [octahedralKernel, octahedralCosine, octahedralDirection,
        Fin.sum_univ_six, Fin.sum_univ_three] <;> ring
  second_moment := by
    intro p i j
    fin_cases p <;> fin_cases i <;> fin_cases j <;>
      simp [octahedralKernel, octahedralCosine, octahedralDirection,
        Fin.sum_univ_six, Fin.sum_univ_three] <;> ring

/-- The degree-one (momentum) collision eigenvalue, explicitly derived
from the scattering kernel at backward and orthogonal scattering angles. -/
theorem octahedral_momentumRate (W : ℝ → ℝ)
    (hplus : 0 ≤ W 1) (hminus : 0 ≤ W (-1)) (horth : 0 ≤ W 0) :
    (octahedralMoments W hplus hminus horth).momentumRate =
      2 * W (-1) + 4 * W 0 := by
  simp [AngularKernelMoments.momentumRate, octahedralMoments]
  ring

/-- The degree-two collision eigenvalue depends only on the orthogonal
scattering channel in this six-direction model. -/
theorem octahedral_degreeTwoRate (W : ℝ → ℝ)
    (hplus : 0 ≤ W 1) (hminus : 0 ≤ W (-1)) (horth : 0 ≤ W 0) :
    (octahedralMoments W hplus hminus horth).degreeTwoRate =
      6 * W 0 := by
  simp [AngularKernelMoments.degreeTwoRate, octahedralMoments]
  ring

/-- The finite collision eigenvalue is exactly the Legendre-weighted
angular loss sum. This does not identify the finite sum with a continuous
angular integral over the sphere. -/
theorem octahedral_degreeTwoRate_eq_legendre (W : ℝ → ℝ)
    (hplus : 0 ≤ W 1) (hminus : 0 ≤ W (-1)) (horth : 0 ≤ W 0)
    (p : Fin 6) :
    (octahedralMoments W hplus hminus horth).degreeTwoRate =
      ∑ q : Fin 6, octahedralKernel W p q *
        (1 - legendreP2 (octahedralCosine p q)) := by
  rw [octahedral_degreeTwoRate]
  fin_cases p <;>
    simp [octahedralKernel, octahedralCosine, octahedralDirection, legendreP2,
      Fin.sum_univ_six, Fin.sum_univ_three] <;> ring

/-- The analogous finite transport-weighted sum equals the linear
angular-mode relaxation eigenvalue. -/
theorem octahedral_momentumRate_eq_transport (W : ℝ → ℝ)
    (hplus : 0 ≤ W 1) (hminus : 0 ≤ W (-1)) (horth : 0 ≤ W 0)
    (p : Fin 6) :
    (octahedralMoments W hplus hminus horth).momentumRate =
      ∑ q : Fin 6, octahedralKernel W p q * (1 - octahedralCosine p q) := by
  rw [octahedral_momentumRate]
  fin_cases p <;>
    simp [octahedralKernel, octahedralCosine, octahedralDirection,
      Fin.sum_univ_six, Fin.sum_univ_three] <;> ring

/-- A diagonal degree-two mode is nonzero on the octahedral grid. -/
theorem octahedral_quadrupole_nonzero :
    ∃ p : Fin 6, quadrupoleMode octahedralDirection 0 0 p ≠ 0 := by
  refine ⟨0, ?_⟩
  norm_num [quadrupoleMode, octahedralDirection]

/-- Strictly positive orthogonal scattering gives a positive quadrupole
relaxation rate, hence a finite positive `τ₂ = (6 W(0))⁻¹`. -/
theorem octahedral_degreeTwoRate_pos (W : ℝ → ℝ)
    (hplus : 0 ≤ W 1) (hminus : 0 ≤ W (-1)) (horth : 0 < W 0) :
    0 < (octahedralMoments W hplus hminus (le_of_lt horth)).degreeTwoRate := by
  rw [octahedral_degreeTwoRate]
  positivity

/-- With the collision moments constructed from `W`, the conditional
quasistationary kinetics has the expected `I₂ = 6 W(0)` timescale.
The closure hypothesis itself is not derived from this scattering kernel. -/
theorem octahedral_polarization_eq_exp (W : ℝ → ℝ)
    (hplus : 0 ≤ W 1) (hminus : 0 ≤ W (-1)) (horth : 0 ≤ W 0)
    {axis : Fin 3} {ℏ c₁ c₂ r : ℝ}
    (closure : QuasistationaryOrbitalKineticClosure
      (octahedralMoments W hplus hminus horth) axis 0 0 ℏ c₁ c₂ r)
    (t : ℝ) :
    closure.polarization t =
      closure.polarization 0 *
        Real.exp (-(orbitalRate axis ℏ ((6 * W 0)⁻¹) c₁ c₂ r * t)) := by
  rw [closure.polarization_eq_exp, octahedral_degreeTwoRate]
  rfl

end QuantumTheory.Models.OrbitalRelaxation
