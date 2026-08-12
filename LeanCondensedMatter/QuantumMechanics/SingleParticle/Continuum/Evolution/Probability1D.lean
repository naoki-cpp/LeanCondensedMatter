import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Evolution.Interface1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.L2.Probability1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Born probability under continuum Schrödinger evolution

This file contains only the dynamical consequence of the abstract unitary evolution: exact
conservation of total Born probability.  The dynamics-independent bridges

`totalProbability1D = ‖ψ‖²`

for `L²` wavefunctions and their Schwartz specialization are owned below dynamics in the
`L²` probability bridge layer.

No pointwise time derivative is inferred from strong `L²` differentiability. The finer connection
to the local continuity equation remains a separate representative-regularity layer.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace SchwartzMap

variable {κ : ℝ} {potential : ℝ → ℝ}
variable {hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)}
variable (evolution : ContinuumSchrodingerEvolution1D κ potential hpotential)

/-- The `L²` Born probability is preserved by the abstract continuum Schrödinger propagator. -/
theorem ContinuumSchrodingerEvolution1D.totalProbability1D_l2_propagator
    (t : ℝ) (ψ : ContinuumL2Wavefunction1D) :
    totalProbability1D (fun x => evolution.propagator t ψ x) =
      totalProbability1D (fun x => ψ x) := by
  rw [totalProbability1D_l2_coe_eq_norm_sq, totalProbability1D_l2_coe_eq_norm_sq]
  rw [evolution.norm_propagator_apply]

/-- A Schwartz-valued family representing the abstract unitary evolution has exactly conserved
whole-space probability. -/
theorem ContinuumSchrodingerEvolution1D.totalProbability1D_schwartz_eq_initial
    (ψ : ℝ → SchwartzMap ℝ ℂ)
    (hrep : ∀ t,
      (ψ t).toLp 2 (volume : Measure ℝ) =
        evolution.propagator t ((ψ 0).toLp 2 (volume : Measure ℝ)))
    (t : ℝ) :
    totalProbability1D (fun x => ψ t x) =
      totalProbability1D (fun x => ψ 0 x) := by
  rw [totalProbability1D_schwartz_eq_toLp_norm_sq,
    totalProbability1D_schwartz_eq_toLp_norm_sq]
  rw [hrep t, evolution.norm_propagator_apply]

end
end Continuum
end SingleParticle
end QuantumMechanics
