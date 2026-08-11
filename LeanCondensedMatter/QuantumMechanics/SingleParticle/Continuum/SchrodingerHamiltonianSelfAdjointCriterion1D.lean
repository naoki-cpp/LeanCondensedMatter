import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonianFullSymmetry1D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Self-adjointness criteria for the one-dimensional Schrödinger Hamiltonian

For a densely defined symmetric partial operator, Mathlib's maximality theorem for the adjoint
already gives `A ≤ A†`. Therefore self-adjointness reduces to the reverse domain inclusion
`A†.domain ≤ A.domain`.

This file packages that reduction for the continuum `H²` Laplacian and the bounded real-potential
Schrödinger Hamiltonian. The remaining analytic task is now isolated cleanly as adjoint-domain
regularity: prove that every vector in the adjoint domain actually belongs to `H²(ℝ)`.
-/

namespace QuantumTheory
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

private theorem isSelfAdjoint_of_isFormalAdjoint_of_adjoint_domain_le
    {A : ContinuumL2Wavefunction1D →ₗ.[ℂ] ContinuumL2Wavefunction1D}
    (hdense : Dense ((A.domain : Submodule ℂ ContinuumL2Wavefunction1D) :
      Set ContinuumL2Wavefunction1D))
    (hsymm : A.IsFormalAdjoint A)
    (hdom : A.adjoint.domain ≤ A.domain) :
    IsSelfAdjoint A := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hle : A ≤ A.adjoint := hsymm.le_adjoint hdense
  have hdomain : A.domain = A.adjoint.domain := le_antisymm hle.1 hdom
  exact (LinearPMap.eq_of_le_of_domain_eq hle hdomain).symm

/-- The free `H²` Laplacian is self-adjoint exactly when its adjoint domain has no vectors outside
`H²`. Symmetry gives the opposite inclusion automatically. -/
theorem continuumH2LaplacianPMap1D_isSelfAdjoint_iff_adjoint_domain_le :
    IsSelfAdjoint continuumH2LaplacianPMap1D ↔
      continuumH2LaplacianPMap1D.adjoint.domain ≤ continuumH2Domain1D := by
  constructor
  · intro hself
    have hadj : continuumH2LaplacianPMap1D.adjoint = continuumH2LaplacianPMap1D :=
      LinearPMap.isSelfAdjoint_def.mp hself
    rw [hadj, continuumH2LaplacianPMap1D_domain]
  · intro hdom
    apply isSelfAdjoint_of_isFormalAdjoint_of_adjoint_domain_le
      continuumH2Domain1D_dense continuumH2LaplacianPMap1D_isFormalAdjoint
    simpa only [continuumH2LaplacianPMap1D_domain] using hdom

/-- For a bounded real potential, self-adjointness of `H = -κ Δ + V` on `H²` is equivalent to
adjoint-domain regularity. This is the precise remaining analytic obligation after symmetry. -/
theorem continuumRealPotentialSchrodingerHamiltonian1D_isSelfAdjoint_iff_adjoint_domain_le
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)) :
    IsSelfAdjoint (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential) ↔
      (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential).adjoint.domain ≤
        continuumH2Domain1D := by
  constructor
  · intro hself
    have hadj :
        (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential).adjoint =
          continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential :=
      LinearPMap.isSelfAdjoint_def.mp hself
    rw [hadj, continuumRealPotentialSchrodingerHamiltonian1D_domain]
  · intro hdom
    apply isSelfAdjoint_of_isFormalAdjoint_of_adjoint_domain_le
      (continuumRealPotentialSchrodingerHamiltonian1D_denseDomain κ potential hpotential)
      (continuumRealPotentialSchrodingerHamiltonian1D_isFormalAdjoint κ potential hpotential)
    simpa only [continuumRealPotentialSchrodingerHamiltonian1D_domain] using hdom

end
end Continuum
end QuantumTheory
