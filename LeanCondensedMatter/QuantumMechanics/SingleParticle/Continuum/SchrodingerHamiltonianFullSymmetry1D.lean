import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.L2.Multiplication1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonianLaplacianSymmetry1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Symmetry of the one-dimensional Schrödinger Hamiltonian

This file combines the symmetry of the `H²` distributional Laplacian with symmetry of bounded
real multiplication operators. Consequently the real-potential Schrödinger Hamiltonian

`H = -κ Δ + V`

is symmetric on its explicit `H²(ℝ)` domain for every real kinetic coefficient `κ` and every
essentially bounded real potential `V`.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- The one-dimensional Schrödinger Hamiltonian with real kinetic coefficient and bounded real
potential is symmetric on its explicit `H²` domain. -/
theorem continuumRealPotentialSchrodingerHamiltonian1D_symmetric
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ))
    (ψ φ : continuumH2Domain1D) :
    inner ℂ
        (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential ψ)
        (φ : ContinuumL2Wavefunction1D) =
      inner ℂ
        (ψ : ContinuumL2Wavefunction1D)
        (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential φ) := by
  change
    inner ℂ
        (-(κ : ℂ) • continuumH2Laplacian1D ψ +
          l2MultiplicationOperator1D (realLInfMultiplier1D potential hpotential)
            (ψ : ContinuumL2Wavefunction1D))
        (φ : ContinuumL2Wavefunction1D) =
      inner ℂ
        (ψ : ContinuumL2Wavefunction1D)
        (-(κ : ℂ) • continuumH2Laplacian1D φ +
          l2MultiplicationOperator1D (realLInfMultiplier1D potential hpotential)
            (φ : ContinuumL2Wavefunction1D))
  calc
    inner ℂ
        (-(κ : ℂ) • continuumH2Laplacian1D ψ +
          l2MultiplicationOperator1D (realLInfMultiplier1D potential hpotential)
            (ψ : ContinuumL2Wavefunction1D))
        (φ : ContinuumL2Wavefunction1D) =
      inner ℂ (-(κ : ℂ) • continuumH2Laplacian1D ψ)
          (φ : ContinuumL2Wavefunction1D) +
        inner ℂ
          (l2MultiplicationOperator1D (realLInfMultiplier1D potential hpotential)
            (ψ : ContinuumL2Wavefunction1D))
          (φ : ContinuumL2Wavefunction1D) := by
        rw [inner_add_left]
    _ = inner ℂ (ψ : ContinuumL2Wavefunction1D)
          (-(κ : ℂ) • continuumH2Laplacian1D φ) +
        inner ℂ (ψ : ContinuumL2Wavefunction1D)
          (l2MultiplicationOperator1D (realLInfMultiplier1D potential hpotential)
            (φ : ContinuumL2Wavefunction1D)) := by
      congr 1
      · rw [inner_smul_left, inner_smul_right, continuumH2Laplacian1D_symmetric]
        simp
      · exact l2RealMultiplicationOperator1D_symmetric potential hpotential
          (ψ : ContinuumL2Wavefunction1D) (φ : ContinuumL2Wavefunction1D)
    _ = inner ℂ
        (ψ : ContinuumL2Wavefunction1D)
        (-(κ : ℂ) • continuumH2Laplacian1D φ +
          l2MultiplicationOperator1D (realLInfMultiplier1D potential hpotential)
            (φ : ContinuumL2Wavefunction1D)) := by
      rw [inner_add_right]

/-- The real-potential Schrödinger Hamiltonian is a formal adjoint of itself on `H²(ℝ)`. -/
theorem continuumRealPotentialSchrodingerHamiltonian1D_isFormalAdjoint
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)) :
    (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential).IsFormalAdjoint
      (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential) := by
  intro ψ φ
  simpa using continuumRealPotentialSchrodingerHamiltonian1D_symmetric
    κ potential hpotential ψ φ

end
end Continuum
end SingleParticle
end QuantumMechanics
