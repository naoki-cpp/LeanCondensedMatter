import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerEvolution1D
import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionGeneratorEquation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Stone construction of the one-dimensional Schrödinger evolution

This file closes the abstract evolution boundary in `SchrodingerEvolution1D.lean` for the bounded
real-potential Hamiltonian.  For the physical Hamiltonian

`H = -κ Δ + V`,

self-adjointness gives the generic Stone evolution `U_H(s)`.  Physical time is introduced only by
the rescaling

`propagator(t) = U_H(t / ℏ)`.

Thus no second Stone construction for the scaled unbounded operator is needed.  The generic group,
adjoint, domain, and generator theorems immediately provide the corresponding Schrödinger evolution
properties; the derivative acquires the physical factor `1 / ℏ` by the chain rule.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- The Stone evolution of the self-adjoint bounded-real-potential Schrödinger Hamiltonian,
rescaled from Stone time to physical time by `t ↦ t / ℏ`. -/
noncomputable def continuumSchrodingerEvolution1D
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ))
    (hκ : κ ≠ 0) (hbar : ℝ) (hbar_pos : 0 < hbar) :
    ContinuumSchrodingerEvolution1D κ potential hpotential := by
  let H := continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential
  have hH : IsSelfAdjoint H := by
    simpa [H] using
      continuumRealPotentialSchrodingerHamiltonian1D_isSelfAdjoint κ potential hpotential hκ
  refine
    { hbar := hbar
      hbar_pos := hbar_pos
      propagator := fun t =>
        LinearPMap.resolventEvolutionStrongLimitOperator H hH (t / hbar)
      propagator_zero := ?_
      propagator_add := ?_
      propagator_star := ?_
      preserves_domain := ?_
      hasDerivAt_propagator_apply := ?_ }
  · simpa using LinearPMap.resolventEvolutionStrongLimitOperator_zero H hH
  · intro t s
    rw [add_div]
    exact LinearPMap.resolventEvolutionStrongLimitOperator_add H hH (t / hbar) (s / hbar)
  · intro t
    simpa only [neg_div] using
      LinearPMap.resolventEvolutionStrongLimitOperator_star H hH (t / hbar)
  · intro t ψ
    have hmem :=
      LinearPMap.resolventEvolutionStrongLimitOperator_mem_domain H hH (t / hbar)
        (show H.domain from ψ)
    simpa [H] using hmem
  · intro t ψ
    have hU :=
      LinearPMap.resolventEvolutionStrongLimitOperator_apply_hasDerivAt H hH
        (show H.domain from ψ) (t / hbar)
    have hscale : HasDerivAt (fun τ : ℝ => τ / hbar) (1 / hbar) t := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const hbar⁻¹
    have hcomp := hU.scomp t hscale
    have hcast : ((hbar⁻¹ : ℝ) : ℂ) = (hbar : ℂ)⁻¹ := by
      exact RCLike.ofReal_inv hbar
    have hcoeff : (hbar⁻¹ : ℝ) • (-Complex.I : ℂ) = -(Complex.I / (hbar : ℂ)) := by
      change ((hbar⁻¹ : ℝ) : ℂ) * (-Complex.I) = _
      rw [hcast]
      ring
    have hrescale (v : ContinuumL2Wavefunction1D) :
        (hbar⁻¹ : ℝ) • ((-Complex.I : ℂ) • v) =
          (-(Complex.I / (hbar : ℂ))) • v := by
      rw [← smul_assoc, hcoeff]
    have hcomp' := hcomp
    simp only [one_div] at hcomp'
    rw [hrescale] at hcomp'
    simpa [Function.comp_def, H] using hcomp'

end
end Continuum
end SingleParticle
end QuantumMechanics
