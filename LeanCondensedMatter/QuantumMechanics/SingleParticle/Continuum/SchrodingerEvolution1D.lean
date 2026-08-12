import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonian1D
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Abstract Schrödinger evolution for the one-dimensional continuum Hamiltonian

This module is the stable physical interface between the concrete continuum Hamiltonian and any
construction of its time evolution.  It records exactly the data used downstream:

* a one-parameter group of bounded propagators on physical `L²(ℝ, ℂ)`;
* adjoint equals negative-time evolution, hence norm preservation;
* invariance of the explicit `H²(ℝ)` Hamiltonian domain;
* differentiability on that domain with generator `-(i/ℏ) H`.

The interface deliberately depends only on the domain-carrying Hamiltonian definition, not on a
particular self-adjointness proof or Stone construction.  `SchrodingerStoneEvolution1D` supplies the
current implementation from the self-adjoint Hamiltonian.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- Evolution data for the one-dimensional Schrödinger Hamiltonian
`H = -κ Δ + V` on `H²(ℝ)`.

The structure is an interface: existence is established separately by the Stone construction. -/
structure ContinuumSchrodingerEvolution1D
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)) where
  /-- Reduced Planck constant. -/
  hbar : ℝ
  hbar_pos : 0 < hbar
  /-- Bounded time-evolution operator on physical `L²`. -/
  propagator : ℝ → ContinuumL2Wavefunction1D →L[ℂ] ContinuumL2Wavefunction1D
  propagator_zero : propagator 0 = 1
  propagator_add : ∀ t s, propagator (t + s) = propagator t * propagator s
  propagator_star : ∀ t, star (propagator t) = propagator (-t)
  /-- The generated evolution leaves the unbounded Hamiltonian domain invariant. -/
  preserves_domain : ∀ t (ψ : continuumH2Domain1D),
    propagator t (ψ : ContinuumL2Wavefunction1D) ∈ continuumH2Domain1D
  /-- On `H²`, the strong derivative is the Schrödinger generator `-(i/ℏ) H`. -/
  hasDerivAt_propagator_apply : ∀ t (ψ : continuumH2Domain1D),
    HasDerivAt
      (fun τ : ℝ => propagator τ (ψ : ContinuumL2Wavefunction1D))
      (-(Complex.I / (hbar : ℂ)) •
        continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential
          ⟨propagator t (ψ : ContinuumL2Wavefunction1D), preserves_domain t ψ⟩)
      t

variable {κ : ℝ} {potential : ℝ → ℝ}
variable {hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)}
variable (evolution : ContinuumSchrodingerEvolution1D κ potential hpotential)

/-- Positivity of `ℏ` implies the nonzero hypothesis used by Schrödinger scaling. -/
theorem ContinuumSchrodingerEvolution1D.hbar_ne_zero : evolution.hbar ≠ 0 :=
  ne_of_gt evolution.hbar_pos

/-- The abstract Schrödinger propagator preserves the physical `L²` norm. -/
@[simp]
theorem ContinuumSchrodingerEvolution1D.norm_propagator_apply
    (t : ℝ) (ψ : ContinuumL2Wavefunction1D) :
    ‖evolution.propagator t ψ‖ = ‖ψ‖ := by
  have hstarMul : star (evolution.propagator t) * evolution.propagator t = 1 := by
    rw [evolution.propagator_star]
    calc
      evolution.propagator (-t) * evolution.propagator t =
          evolution.propagator (-t + t) := (evolution.propagator_add (-t) t).symm
      _ = 1 := by simp [evolution.propagator_zero]
  have hcomp :
      ContinuousLinearMap.adjoint (evolution.propagator t) ∘SL evolution.propagator t = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg
      (fun U : ContinuumL2Wavefunction1D →L[ℂ] ContinuumL2Wavefunction1D => U x)
      hstarMul
    change ContinuousLinearMap.adjoint (evolution.propagator t)
        (evolution.propagator t x) = x at h
    exact h
  exact
    ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (evolution.propagator t)).2 hcomp) ψ

end
end Continuum
end SingleParticle
end QuantumMechanics
