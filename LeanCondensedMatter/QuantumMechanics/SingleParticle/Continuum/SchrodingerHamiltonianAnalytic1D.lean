import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonian1D
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

set_option linter.style.header false

/-!
# Analytic foundations for the one-dimensional continuum Schrödinger Hamiltonian

This file begins the analytic layer for the domain-carrying Schrödinger operator from
`SchrodingerHamiltonian1D.lean`.

The first step is density of the `H²(ℝ)` domain in physical `L²(ℝ, ℂ)`. Schwartz functions give a
canonical dense core: Mathlib proves that their `L²` images are dense, while every Schwartz
function belongs to every Bessel-potential Sobolev space. Combining these facts shows that the
`LinearPMap` Schrödinger Hamiltonians defined on `H²` are genuinely densely defined.

Closedness, formal symmetry, adjoints, and self-adjointness remain later layers.
-/

namespace QuantumTheory
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory SchwartzMap

/-- Every Schwartz wavefunction, viewed in `L²(ℝ, ℂ)`, belongs to the continuum `H²` domain. -/
theorem schwartz_toLp_mem_continuumH2Domain1D (f : 𝓢(ℝ, ℂ)) :
    f.toLp 2 (volume : Measure ℝ) ∈ continuumH2Domain1D := by
  rw [mem_continuumH2Domain1D_iff]
  simpa [l2ToTemperedDistribution1D] using
    (f.memSobolev (s := (2 : ℝ)) (p := 2))

/-- The explicit continuum `H²(ℝ)` domain is dense in physical `L²(ℝ, ℂ)`. -/
theorem continuumH2Domain1D_dense :
    Dense ((continuumH2Domain1D : Submodule ℂ ContinuumL2Wavefunction1D) :
      Set ContinuumL2Wavefunction1D) := by
  apply Dense.mono ?_
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      (μ := (volume : Measure ℝ)) (by simp))
  rintro _ ⟨f, rfl⟩
  exact schwartz_toLp_mem_continuumH2Domain1D f

/-- The domain-carrying Schrödinger Hamiltonian with bounded complex potential is densely defined. -/
theorem continuumSchrodingerHamiltonian1D_denseDomain
    (κ : ℝ) (potential : ContinuumLInfMultiplier1D) :
    Dense (((continuumSchrodingerHamiltonian1D κ potential).domain :
      Submodule ℂ ContinuumL2Wavefunction1D) : Set ContinuumL2Wavefunction1D) := by
  simpa only [continuumSchrodingerHamiltonian1D_domain] using continuumH2Domain1D_dense

/-- The real bounded-potential specialization is densely defined on the same `H²` domain. -/
theorem continuumRealPotentialSchrodingerHamiltonian1D_denseDomain
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)) :
    Dense (((continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential).domain :
      Submodule ℂ ContinuumL2Wavefunction1D) : Set ContinuumL2Wavefunction1D) := by
  simpa only [continuumRealPotentialSchrodingerHamiltonian1D_domain] using
    continuumH2Domain1D_dense

end
end Continuum
end QuantumTheory
