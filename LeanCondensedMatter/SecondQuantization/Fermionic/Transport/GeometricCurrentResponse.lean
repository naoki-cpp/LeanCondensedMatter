import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent
import LeanCondensedMatter.QuantumTheory.LinearResponse.ResponseChannel

set_option linter.style.header false

/-!
# Geometric-current response adapter

Geometric current/contact construction is owned by `Fermionic.Lattice`; this file contains only
the generic retarded-response specialization and the response-channel packaging used by transport.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse

noncomputable section

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Response channel for the current component measured along `measuredDirection` under a uniform
Peierls vector-potential source along `sourceDirection`.

The observable variation is the mixed geometric contact operator. After factoring out the scalar
source amplitude, this is the canonical finite-lattice channel underlying the conductivity
component `σ_ij = ∂J_i / ∂E_j`. -/
noncomputable def peierlsCurrentComponentResponseChannel
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    ResponseChannel (FiniteLatticeHilbertFock Site) where
  measured := boundedDirectionalCurrent geometry measuredDirection ℏ q K
  source := boundedDirectionalCurrent geometry sourceDirection ℏ q K
  observableVariation :=
    boundedMixedDirectionalContact geometry measuredDirection sourceDirection ℏ q K

/-- For Hermitian hopping and real physical parameters, the source vertex of every Peierls current
component channel is self-adjoint. -/
theorem peierlsCurrentComponentResponseChannel_source_isSelfAdjoint
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (hK : K.HasHermitianAmplitudes)
    (ℏ q : ℝ) :
    IsSelfAdjoint
      (peierlsCurrentComponentResponseChannel geometry measuredDirection sourceDirection
        (ℏ : ℂ) (q : ℂ) K).source := by
  simpa [peierlsCurrentComponentResponseChannel] using
    isSelfAdjoint_boundedDirectionalCurrent geometry sourceDirection K hK ℏ q

/-- Retarded response of a geometric current component with the source-dependent geometric contact
term retained. Current self-adjointness is derived from Hermitian hopping and the real physical
charge rather than supplied externally. -/
theorem hasDerivAt_boundedDirectionalCurrentExpectation_zero_of_bound_retarded
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (f : ℝ → ℝ)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (hK : K.HasHermitianAmplitudes) (q : ℝ)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) β,
      ‖QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)) s‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)))
      MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ =>
        QuantumTheory.LinearResponse.affinePerturbedExpectation system expectation
          (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K))
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          ((f t : ℂ) •
            boundedDirectionalContact geometry direction
              (system.hbar : ℂ) (q : ℂ) K) lam t)
      ((∫ s in (0 : ℝ)..t,
          (f s : ℂ) *
            QuantumTheory.LinearResponse.retardedSusceptibility system expectation
              (boundedDirectionalCurrent geometry direction
                (system.hbar : ℂ) (q : ℂ) K)
              (boundedDirectionalCurrent geometry direction
                (system.hbar : ℂ) (q : ℂ) K) t s) +
        expectation
          (QuantumTheory.LinearResponse.heisenbergEvolution system
            ((f t : ℂ) •
              boundedDirectionalContact geometry direction
                (system.hbar : ℂ) (q : ℂ) K) t))
      0 := by
  exact
    QuantumTheory.LinearResponse.hasDerivAt_affineSourceCoupledExpectation_zero_of_bound_retarded
      system expectation f
      (isSelfAdjoint_boundedDirectionalCurrent geometry direction K hK system.hbar q)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      ((f t : ℂ) •
        boundedDirectionalContact geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
      hM hV ht hInt

end
end Transport
end Fermionic
end SecondQuantization
