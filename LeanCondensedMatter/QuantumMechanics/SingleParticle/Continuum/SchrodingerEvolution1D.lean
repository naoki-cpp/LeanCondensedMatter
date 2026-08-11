import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonianSelfAdjoint1D
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Abstract Schrödinger evolution for the one-dimensional continuum Hamiltonian

The pinned Mathlib unbounded-operator API provides adjoints, closedness, and self-adjointness for
`LinearPMap`, but it does not yet provide Stone's theorem or an unbounded functional calculus that
constructs `exp (-i t H / ℏ)` from a self-adjoint partial operator.

Accordingly, this file does not pretend to construct a propagator from self-adjointness alone.
Instead it isolates the exact evolution data that a future Stone-theorem layer must provide for the
bounded-real-potential continuum Hamiltonian:

* a one-parameter group of bounded propagators on physical `L²(ℝ, ℂ)`;
* adjoint equals negative-time evolution, hence unitarity;
* invariance of the explicit `H²(ℝ)` Hamiltonian domain;
* differentiability on that domain with generator `-(i/ℏ) H`.

This makes the analytic boundary explicit while allowing later continuum results to depend only on
the properties they actually use.
-/

namespace QuantumTheory
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- Evolution data for the self-adjoint one-dimensional Schrödinger Hamiltonian
`H = -κ Δ + V` on `H²(ℝ)`.

The existence of this structure is the Stone-theorem obligation that is not currently supplied by
the pinned Mathlib `LinearPMap` API. -/
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

@[simp]
theorem ContinuumSchrodingerEvolution1D.propagator_zero_apply
    (ψ : ContinuumL2Wavefunction1D) :
    evolution.propagator 0 ψ = ψ := by
  rw [evolution.propagator_zero]
  rfl

/-- Negative time is a left inverse for the propagator. -/
theorem ContinuumSchrodingerEvolution1D.propagator_neg_mul (t : ℝ) :
    evolution.propagator (-t) * evolution.propagator t = 1 := by
  calc
    evolution.propagator (-t) * evolution.propagator t =
        evolution.propagator (-t + t) := (evolution.propagator_add (-t) t).symm
    _ = 1 := by simp [evolution.propagator_zero]

/-- Negative time is a right inverse for the propagator. -/
theorem ContinuumSchrodingerEvolution1D.propagator_mul_neg (t : ℝ) :
    evolution.propagator t * evolution.propagator (-t) = 1 := by
  calc
    evolution.propagator t * evolution.propagator (-t) =
        evolution.propagator (t + -t) := (evolution.propagator_add t (-t)).symm
    _ = 1 := by simp [evolution.propagator_zero]

/-- The adjoint propagator is its left inverse. -/
@[simp]
theorem ContinuumSchrodingerEvolution1D.star_mul_propagator (t : ℝ) :
    star (evolution.propagator t) * evolution.propagator t = 1 := by
  rw [evolution.propagator_star]
  exact evolution.propagator_neg_mul t

/-- The adjoint propagator is its right inverse. -/
@[simp]
theorem ContinuumSchrodingerEvolution1D.propagator_mul_star (t : ℝ) :
    evolution.propagator t * star (evolution.propagator t) = 1 := by
  rw [evolution.propagator_star]
  exact evolution.propagator_mul_neg t

/-- The abstract unbounded Schrödinger propagator preserves the physical `L²` norm. -/
@[simp]
theorem ContinuumSchrodingerEvolution1D.norm_propagator_apply
    (t : ℝ) (ψ : ContinuumL2Wavefunction1D) :
    ‖evolution.propagator t ψ‖ = ‖ψ‖ := by
  have hcomp :
      ContinuousLinearMap.adjoint (evolution.propagator t) ∘SL evolution.propagator t = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg
      (fun U : ContinuumL2Wavefunction1D →L[ℂ] ContinuumL2Wavefunction1D => U x)
      (evolution.star_mul_propagator t)
    change ContinuousLinearMap.adjoint (evolution.propagator t)
        (evolution.propagator t x) = x at h
    exact h
  exact
    ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (evolution.propagator t)).2 hcomp) ψ

/-- Evolution restricted to the invariant `H²` Hamiltonian domain. -/
noncomputable def ContinuumSchrodingerEvolution1D.evolveH2
    (t : ℝ) (ψ : continuumH2Domain1D) : continuumH2Domain1D :=
  ⟨evolution.propagator t (ψ : ContinuumL2Wavefunction1D),
    evolution.preserves_domain t ψ⟩

@[simp]
theorem ContinuumSchrodingerEvolution1D.evolveH2_coe
    (t : ℝ) (ψ : continuumH2Domain1D) :
    (evolution.evolveH2 t ψ : ContinuumL2Wavefunction1D) =
      evolution.propagator t (ψ : ContinuumL2Wavefunction1D) :=
  rfl

@[simp]
theorem ContinuumSchrodingerEvolution1D.evolveH2_zero
    (ψ : continuumH2Domain1D) :
    evolution.evolveH2 0 ψ = ψ := by
  apply Subtype.ext
  simp

/-- The restricted `H²` evolution inherits the additive time action. -/
theorem ContinuumSchrodingerEvolution1D.evolveH2_add
    (t s : ℝ) (ψ : continuumH2Domain1D) :
    evolution.evolveH2 t (evolution.evolveH2 s ψ) = evolution.evolveH2 (t + s) ψ := by
  apply Subtype.ext
  change evolution.propagator t
      (evolution.propagator s (ψ : ContinuumL2Wavefunction1D)) =
    evolution.propagator (t + s) (ψ : ContinuumL2Wavefunction1D)
  simpa [mul_apply_eq_comp] using
    congrArg
      (fun U : ContinuumL2Wavefunction1D →L[ℂ] ContinuumL2Wavefunction1D =>
        U (ψ : ContinuumL2Wavefunction1D))
      (evolution.propagator_add t s).symm

/-- The domain-valued trajectory satisfies the strong Schrödinger equation when viewed in `L²`. -/
theorem ContinuumSchrodingerEvolution1D.hasDerivAt_evolveH2_coe
    (t : ℝ) (ψ : continuumH2Domain1D) :
    HasDerivAt
      (fun τ : ℝ => (evolution.evolveH2 τ ψ : ContinuumL2Wavefunction1D))
      (-(Complex.I / (evolution.hbar : ℂ)) •
        continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential
          (evolution.evolveH2 t ψ))
      t := by
  simpa [ContinuumSchrodingerEvolution1D.evolveH2] using
    evolution.hasDerivAt_propagator_apply t ψ

end
end Continuum
end QuantumTheory
