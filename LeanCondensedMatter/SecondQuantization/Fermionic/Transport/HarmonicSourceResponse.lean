import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.FrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.GeometricCurrentResponse
import LeanCondensedMatter.QuantumTheory.LinearResponse.HarmonicSource

set_option linter.style.header false

/-!
# Real harmonic sources for the finite-frequency current response

The representation-independent cosine/sine source quadratures now live in
`QuantumTheory.LinearResponse.HarmonicSource`, where they are defined directly from the canonical
adiabatic phase.

This module retains the fermionic finite-lattice realization. The bounded source-coupling theorem
accepts a real source profile, so the two physical quadratures give directional-current response
theorems without introducing a complex-valued Hamiltonian perturbation. At the observation time,
the cosine source equals one and therefore carries the explicit Peierls contact response, while the
sine source vanishes and has no contact contribution.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice
open QuantumTheory.LinearResponse

noncomputable section

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Finite-time response coefficient measured with the real cosine quadrature. The contact term is
present because the normalized cosine source equals one at the observation time. -/
noncomputable def finiteTimeAdiabaticDirectionalCosineResponse
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η T : ℝ) : ℂ :=
  let J := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  (∫ s in (0 : ℝ)..T,
      (adiabaticCosineSource ω η T s : ℂ) *
        QuantumTheory.LinearResponse.retardedSusceptibility
          system expectation J J T s) +
    boundedDirectionalContactExpectation
      system expectation geometry direction K q T

/-- Finite-time response coefficient measured with the real sine quadrature. There is no contact
term because the normalized sine source vanishes at the observation time. -/
noncomputable def finiteTimeAdiabaticDirectionalSineResponse
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η T : ℝ) : ℂ :=
  let J := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  ∫ s in (0 : ℝ)..T,
    (adiabaticSineSource ω η T s : ℂ) *
      QuantumTheory.LinearResponse.retardedSusceptibility
        system expectation J J T s

/-- The cosine quadrature is a genuine real-source response theorem. Its derivative contains the
retarded current-current contribution and the geometric Peierls contact expectation. -/
theorem hasDerivAt_boundedDirectionalCosineExpectation_zero_of_bound_retarded
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (hK : K.HasHermitianAmplitudes)
    (q ω η T : ℝ)
    {β M : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) β,
      ‖QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation
          (adiabaticCosineSource ω η T)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)) s‖ ≤ M)
    (hT : T ∈ Set.Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation
          (adiabaticCosineSource ω η T)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)))
      MeasureTheory.volume 0 T) :
    HasDerivAt
      (fun lam : ℝ =>
        QuantumTheory.LinearResponse.affinePerturbedExpectation system expectation
          (QuantumTheory.LinearResponse.sourceCoupledPerturbation
            (adiabaticCosineSource ω η T)
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K))
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K) lam T)
      (finiteTimeAdiabaticDirectionalCosineResponse
        system expectation geometry direction K q ω η T)
      0 := by
  have h :=
    hasDerivAt_boundedDirectionalCurrentExpectation_zero_of_bound_retarded
      system expectation (adiabaticCosineSource ω η T)
      geometry direction K hK q hM hV hT hInt
  simpa [finiteTimeAdiabaticDirectionalCosineResponse,
    boundedDirectionalContactExpectation] using h

/-- The sine quadrature is a genuine real-source response theorem. Its explicit observable
variation vanishes because the source is zero at the observation time. -/
theorem hasDerivAt_boundedDirectionalSineExpectation_zero_of_bound_retarded
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (hK : K.HasHermitianAmplitudes)
    (q ω η T : ℝ)
    {β M : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) β,
      ‖QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation
          (adiabaticSineSource ω η T)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)) s‖ ≤ M)
    (hT : T ∈ Set.Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation
          (adiabaticSineSource ω η T)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)))
      MeasureTheory.volume 0 T) :
    HasDerivAt
      (fun lam : ℝ =>
        QuantumTheory.LinearResponse.affinePerturbedExpectation system expectation
          (QuantumTheory.LinearResponse.sourceCoupledPerturbation
            (adiabaticSineSource ω η T)
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K))
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          0 lam T)
      (finiteTimeAdiabaticDirectionalSineResponse
        system expectation geometry direction K q ω η T)
      0 := by
  have h :=
    hasDerivAt_boundedDirectionalCurrentExpectation_zero_of_bound_retarded
      system expectation (adiabaticSineSource ω η T)
      geometry direction K hK q hM hV hT hInt
  simpa [finiteTimeAdiabaticDirectionalSineResponse,
    QuantumTheory.LinearResponse.heisenbergEvolution] using h

end
end Transport
end Fermionic
end SecondQuantization
