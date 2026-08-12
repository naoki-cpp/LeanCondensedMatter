import LeanCondensedMatter.Analysis.Operator.Unbounded.SelfAdjointCriterion
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Hamiltonian.DenseDomain1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Hamiltonian.Closed1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Hamiltonian.Symmetry1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Self-adjointness criteria for the one-dimensional Schrödinger Hamiltonian

For a densely defined symmetric partial operator, self-adjointness reduces to the reverse domain
inclusion `A†.domain ≤ A.domain`. The generic Hilbert-space criterion is owned by
`Analysis.Operator.Unbounded.SelfAdjointCriterion`; this file only specializes it to the continuum
`H²` Laplacian and the bounded real-potential Schrödinger Hamiltonian.

The remaining analytic task is adjoint-domain regularity: prove that every vector in the adjoint
domain actually belongs to `H²(ℝ)`.

The imports intentionally name the three independent concrete prerequisites directly: dense-domain
facts, the explicit `H²` partial operator, and symmetry. The specialization should not rely on a
historical transitive import chain.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- The free `H²` Laplacian is self-adjoint exactly when its adjoint domain has no vectors outside
`H²`. Symmetry gives the opposite inclusion automatically. -/
theorem continuumH2LaplacianPMap1D_isSelfAdjoint_iff_adjoint_domain_le :
    IsSelfAdjoint continuumH2LaplacianPMap1D ↔
      continuumH2LaplacianPMap1D.adjoint.domain ≤ continuumH2Domain1D := by
  simpa only [continuumH2LaplacianPMap1D_domain] using
    (LinearPMap.isSelfAdjoint_iff_adjoint_domain_le_of_isFormalAdjoint
      (A := continuumH2LaplacianPMap1D)
      continuumH2Domain1D_dense continuumH2LaplacianPMap1D_isFormalAdjoint)

/-- For a bounded real potential, self-adjointness of `H = -κ Δ + V` on `H²` is equivalent to
adjoint-domain regularity. This is the precise remaining analytic obligation after symmetry. -/
theorem continuumRealPotentialSchrodingerHamiltonian1D_isSelfAdjoint_iff_adjoint_domain_le
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)) :
    IsSelfAdjoint (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential) ↔
      (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential).adjoint.domain ≤
        continuumH2Domain1D := by
  simpa only [continuumRealPotentialSchrodingerHamiltonian1D_domain] using
    (LinearPMap.isSelfAdjoint_iff_adjoint_domain_le_of_isFormalAdjoint
      (A := continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential)
      (continuumRealPotentialSchrodingerHamiltonian1D_denseDomain κ potential hpotential)
      (continuumRealPotentialSchrodingerHamiltonian1D_isFormalAdjoint κ potential hpotential))

end
end Continuum
end SingleParticle
end QuantumMechanics
