import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonianLaplacianSelfAdjoint1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Self-adjointness of the one-dimensional bounded-potential Schrödinger Hamiltonian

This file transfers self-adjointness from the free `H²` Laplacian to

`H = -κ Δ + V`

for nonzero real `κ` and an essentially bounded real multiplication potential `V`.

The proof does not repeat the distributional regularity argument for the free Laplacian. Given a
vector `u` in the adjoint domain of `H`, the adjoint relation supplies an `L²` representative
`H†u`. Subtracting the bounded symmetric potential contribution and dividing by `-κ` produces a
witness that `u` lies in the adjoint domain of the free Laplacian. The free self-adjointness result
then forces `u ∈ H²`, which is exactly the reverse domain inclusion required by the previously
proved self-adjointness criterion.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- For nonzero kinetic coefficient and bounded real potential, every vector in the adjoint domain
of `H = -κ Δ + V` already belongs to the explicit `H²(ℝ)` domain. -/
theorem continuumRealPotentialSchrodingerHamiltonian1D_adjoint_domain_le
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ))
    (hκ : κ ≠ 0) :
    (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential).adjoint.domain ≤
      continuumH2Domain1D := by
  intro u hu
  apply continuumH2LaplacianPMap1D_adjoint_domain_le
  let H := continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential
  let M := l2MultiplicationOperator1D (realTestMultiplier1D potential hpotential)
  let uAdj : H.adjoint.domain := ⟨u, hu⟩
  let wH : ContinuumL2Wavefunction1D := H.adjoint uAdj
  apply LinearPMap.mem_adjoint_domain_of_exists
  refine ⟨-((κ : ℂ)⁻¹) • (wH - M u), ?_⟩
  intro ψ
  have hadj :=
    LinearPMap.adjoint_isFormalAdjoint
      (continuumRealPotentialSchrodingerHamiltonian1D_denseDomain κ potential hpotential)
      uAdj ψ
  have hadj' :
      inner ℂ wH (ψ : ContinuumL2Wavefunction1D) =
        inner ℂ u
          (-(κ : ℂ) • continuumH2Laplacian1D ψ +
            M (ψ : ContinuumL2Wavefunction1D)) := by
    change
      inner ℂ wH (ψ : ContinuumL2Wavefunction1D) =
        inner ℂ u
          (-(κ : ℂ) • continuumH2Laplacian1D ψ +
            M (ψ : ContinuumL2Wavefunction1D)) at hadj
    exact hadj
  have hM :
      inner ℂ (M u) (ψ : ContinuumL2Wavefunction1D) =
        inner ℂ u (M (ψ : ContinuumL2Wavefunction1D)) := by
    simpa [M] using
      l2RealMultiplicationOperator1D_symmetric potential hpotential u
        (ψ : ContinuumL2Wavefunction1D)
  change
    inner ℂ (-((κ : ℂ)⁻¹) • (wH - M u)) (ψ : ContinuumL2Wavefunction1D) =
      inner ℂ u (continuumH2Laplacian1D ψ)
  calc
    inner ℂ (-((κ : ℂ)⁻¹) • (wH - M u)) (ψ : ContinuumL2Wavefunction1D) =
        -((κ : ℂ)⁻¹) *
          (inner ℂ wH (ψ : ContinuumL2Wavefunction1D) -
            inner ℂ (M u) (ψ : ContinuumL2Wavefunction1D)) := by
      rw [inner_smul_left, inner_sub_left]
      simp
    _ = -((κ : ℂ)⁻¹) *
          (inner ℂ u
              (-(κ : ℂ) • continuumH2Laplacian1D ψ +
                M (ψ : ContinuumL2Wavefunction1D)) -
            inner ℂ u (M (ψ : ContinuumL2Wavefunction1D))) := by
      rw [hadj', hM]
    _ = inner ℂ u (continuumH2Laplacian1D ψ) := by
      rw [inner_add_right, inner_smul_right]
      have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
      field_simp [hκc]
      ring

/-- The one-dimensional Schrödinger Hamiltonian with nonzero real kinetic coefficient and bounded
real scalar potential is self-adjoint on the explicit `H²(ℝ)` domain. -/
theorem continuumRealPotentialSchrodingerHamiltonian1D_isSelfAdjoint
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ))
    (hκ : κ ≠ 0) :
    IsSelfAdjoint (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential) :=
  continuumRealPotentialSchrodingerHamiltonian1D_isSelfAdjoint_iff_adjoint_domain_le
    κ potential hpotential |>.mpr
      (continuumRealPotentialSchrodingerHamiltonian1D_adjoint_domain_le
        κ potential hpotential hκ)

end
end Continuum
end SingleParticle
end QuantumMechanics
