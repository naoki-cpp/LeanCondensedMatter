import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerEvolution1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.ProbabilityIntegral1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# L² Born probability and continuum Schrödinger evolution

This file connects the operator-theoretic evolution layer to the whole-space probability quantity
used by the pointwise/weak continuity development.

The key bridge is independent of dynamics: for an `L²(ℝ, ℂ)` wavefunction, the integral of the
pointwise probability density of its chosen representative is exactly the squared Hilbert norm.
Consequently, any Schwartz representative compatible with the unitary propagator from
`ContinuumSchrodingerEvolution1D` has exactly conserved `totalProbability1D`.

No pointwise time derivative is inferred from strong `L²` differentiability. The finer connection to
the local continuity equation therefore remains a separate regularity layer.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace SchwartzMap

private theorem inner_self_complex_eq_probabilityDensityValue (z : ℂ) :
    inner ℂ z z = (probabilityDensityValue z : ℂ) := by
  rw [probabilityDensityValue]
  rw [inner_self_eq_norm_sq_to_K, pow_two]
  change Complex.ofReal ‖z‖ * Complex.ofReal ‖z‖ =
    Complex.ofReal (Complex.normSq z)
  calc
    Complex.ofReal ‖z‖ * Complex.ofReal ‖z‖ =
        Complex.ofReal (‖z‖ * ‖z‖) := (Complex.ofReal_mul _ _).symm
    _ = Complex.ofReal (Complex.normSq z) :=
      congrArg Complex.ofReal (Complex.norm_mul_self_eq_normSq z)

/-- The whole-space probability integral of the canonical representative of an `L²` wavefunction
is its squared Hilbert norm. -/
theorem totalProbability1D_l2_coe_eq_norm_sq (ψ : ContinuumL2Wavefunction1D) :
    totalProbability1D (fun x => ψ x) = ‖ψ‖ ^ 2 := by
  have hinner :
      inner ℂ ψ ψ = (totalProbability1D (fun x => ψ x) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    unfold totalProbability1D
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x =>
      inner_self_complex_eq_probabilityDensityValue (ψ x)
  have hnorm : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ)
  apply Complex.ofReal_injective
  exact hinner.symm.trans hnorm

/-- For a Schwartz wavefunction, the pointwise probability integral used in the continuity-equation
API is exactly the squared norm of its canonical `L²` image. -/
theorem totalProbability1D_schwartz_eq_toLp_norm_sq (ψ : SchwartzMap ℝ ℂ) :
    totalProbability1D (fun x => ψ x) =
      ‖ψ.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  calc
    totalProbability1D (fun x => ψ x) =
        totalProbability1D (fun x => ψ.toLp 2 (volume : Measure ℝ) x) := by
      unfold totalProbability1D
      apply integral_congr_ae
      filter_upwards [SchwartzMap.coeFn_toLp ψ 2 (volume : Measure ℝ)] with x hx
      rw [hx]
    _ = ‖ψ.toLp 2 (volume : Measure ℝ)‖ ^ 2 :=
      totalProbability1D_l2_coe_eq_norm_sq (ψ.toLp 2 (volume : Measure ℝ))

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
whole-space probability. This is the operator-theoretic bridge back to the `totalProbability1D`
quantity from the continuity-equation development. -/
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
