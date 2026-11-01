import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Heisenberg dynamics of a one-parameter unitary group

The Schrödinger propagators are a monoid homomorphism from multiplicatively tagged real time
to unitary bounded operators. Heisenberg evolution is `U(t)† A U(t)`. Its algebraic laws need
neither a bounded generator nor a continuity hypothesis. Norm differentiation and integration
require separate analytic hypotheses and are not inferred from these laws.
-/

namespace QuantumTheory.LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))

/-- Heisenberg evolution induced by the supplied one-parameter Schrödinger unitary group. -/
def heisenbergEvolution (t : ℝ) : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
  Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (star (U (Multiplicative.ofAdd t)))

/-- The observable is conjugated by the adjoint of the Schrödinger propagator. -/
theorem heisenbergEvolution_apply (t : ℝ) (A : H →L[ℂ] H) :
    heisenbergEvolution U t A =
      star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) * A *
        (U (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  exact Unitary.conjStarAlgAut_star_apply (U (Multiplicative.ofAdd t)) A

@[simp]
theorem heisenbergEvolution_zero (A : H →L[ℂ] H) :
    heisenbergEvolution U 0 A = A := by
  simp [heisenbergEvolution]

/-- Successive Heisenberg evolutions add their time parameters. -/
@[simp]
theorem heisenbergEvolution_heisenbergEvolution (A : H →L[ℂ] H) (t s : ℝ) :
    heisenbergEvolution U s (heisenbergEvolution U t A) =
      heisenbergEvolution U (t + s) A := by
  have htime := U.map_mul (Multiplicative.ofAdd t) (Multiplicative.ofAdd s)
  change U (Multiplicative.ofAdd (t + s)) =
    U (Multiplicative.ofAdd t) * U (Multiplicative.ofAdd s) at htime
  simp only [heisenbergEvolution_apply, htime, Submonoid.coe_mul, star_mul]
  simp only [mul_assoc]

/-- A two-time commutator is the evolution of a relative-time commutator. -/
theorem lie_heisenbergEvolution_eq_relativeTime (A B : H →L[ℂ] H) (t s : ℝ) :
    ⁅heisenbergEvolution U t A, heisenbergEvolution U s B⁆ =
      heisenbergEvolution U s ⁅heisenbergEvolution U (t - s) A, B⁆ := by
  have htime : heisenbergEvolution U s (heisenbergEvolution U (t - s) A) =
      heisenbergEvolution U t A := by
    rw [heisenbergEvolution_heisenbergEvolution, sub_add_cancel]
  rw [← htime]
  simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul]

/-- Unitary conjugation preserves the norm of every bounded observable. -/
@[simp]
theorem norm_heisenbergEvolution (A : H →L[ℂ] H) (t : ℝ) :
    ‖heisenbergEvolution U t A‖ = ‖A‖ := by
  have hU := (U (Multiplicative.ofAdd t)).property
  rw [heisenbergEvolution_apply]
  calc
    ‖star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) * A *
        (U (Multiplicative.ofAdd t) : H →L[ℂ] H)‖ =
        ‖star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) * A‖ :=
      CStarRing.norm_mul_mem_unitary _ hU
    _ = ‖A‖ := CStarRing.norm_mem_unitary_mul A (Unitary.star_mem hU)

end
end QuantumTheory.LinearResponse
