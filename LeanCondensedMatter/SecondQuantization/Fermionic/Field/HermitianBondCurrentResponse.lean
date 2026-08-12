import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.HermitianBondCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.PeierlsContactResponse

set_option linter.style.header false

/-!
# Hermitian bond-current response adapter

Self-adjointness is derived in `Fermionic.Lattice.HermitianBondCurrent`; this downstream module
uses it to specialize the generic Peierls current response theorem.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- Peierls current response for Hermitian hopping and real charge, with current self-adjointness
derived from the model rather than supplied separately.

The Planck constant used in the current is the same positive real `system.hbar` carried by the
bounded free system. -/
theorem hasDerivAt_boundedPeierlsAffineCurrentExpectation_zero_of_bound_retarded_of_hermitian
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (f : ℝ → ℝ) (K : LocallyFiniteHopping Site)
    (hK : K.HasHermitianAmplitudes) (q : ℝ)
    (x y : Site)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) β,
      ‖QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
          (boundedBondCurrent (system.hbar : ℂ) (q : ℂ) K x y)) s‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
          (boundedBondCurrent (system.hbar : ℂ) (q : ℂ) K x y)))
      MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ =>
        QuantumTheory.LinearResponse.affinePerturbedExpectation system expectation
          (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
            (boundedBondCurrent (system.hbar : ℂ) (q : ℂ) K x y))
          (boundedBondCurrent (system.hbar : ℂ) (q : ℂ) K x y)
          ((f t : ℂ) •
            boundedBondContact K (system.hbar : ℂ) (q : ℂ) x y) lam t)
      ((∫ s in (0 : ℝ)..t,
          (f s : ℂ) *
            QuantumTheory.LinearResponse.retardedSusceptibility system expectation
              (boundedBondCurrent (system.hbar : ℂ) (q : ℂ) K x y)
              (boundedBondCurrent (system.hbar : ℂ) (q : ℂ) K x y) t s) +
        expectation
          (QuantumTheory.LinearResponse.heisenbergEvolution system
            ((f t : ℂ) •
              boundedBondContact K (system.hbar : ℂ) (q : ℂ) x y) t))
      0 := by
  exact
    hasDerivAt_boundedPeierlsAffineCurrentExpectation_zero_of_bound_retarded
      system expectation f K (system.hbar : ℂ) (q : ℂ) x y
      (isSelfAdjoint_boundedBondCurrent_ofReal K hK system.hbar q x y)
      hM hV ht hInt

end
end Field
end Fermionic
end SecondQuantization
