import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.PeierlsContact
import LeanCondensedMatter.QuantumTheory.LinearResponse.ObservableVariation

set_option linter.style.header false

/-!
# Peierls bond-current response adapter

The source-dependent bond current and contact operator are lattice-owned. This module only
specializes the generic observable-variation response theorem to those operators.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- Peierls current response with the contact term retained.

The Hamiltonian source coupling is `-λ f(s) J₀`, while the measured current at time `t` has affine
coefficient `f(t) J₁`. Therefore the total derivative is the retarded `J₀`–`J₀` response plus the
explicit expectation of the evolved contact operator. -/
theorem hasDerivAt_boundedPeierlsAffineCurrentExpectation_zero_of_bound_retarded
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (f : ℝ → ℝ) (K : LocallyFiniteHopping Site) (ℏ q : ℂ)
    (x y : Site)
    (hJ : IsSelfAdjoint (boundedBondCurrent ℏ q K x y))
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) β,
      ‖QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
          (boundedBondCurrent ℏ q K x y)) s‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
          (boundedBondCurrent ℏ q K x y))) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ =>
        QuantumTheory.LinearResponse.affinePerturbedExpectation system expectation
          (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
            (boundedBondCurrent ℏ q K x y))
          (boundedBondCurrent ℏ q K x y)
          ((f t : ℂ) • boundedBondContact K ℏ q x y) lam t)
      ((∫ s in (0 : ℝ)..t,
          (f s : ℂ) *
            QuantumTheory.LinearResponse.retardedSusceptibility system expectation
              (boundedBondCurrent ℏ q K x y)
              (boundedBondCurrent ℏ q K x y) t s) +
        expectation
          (QuantumTheory.LinearResponse.heisenbergEvolution system
            ((f t : ℂ) • boundedBondContact K ℏ q x y) t))
      0 := by
  exact
    QuantumTheory.LinearResponse.hasDerivAt_affineSourceCoupledExpectation_zero_of_bound_retarded
      system expectation f hJ
      (boundedBondCurrent ℏ q K x y)
      ((f t : ℂ) • boundedBondContact K ℏ q x y)
      hM hV ht hInt


end
end Field
end Fermionic
end SecondQuantization
