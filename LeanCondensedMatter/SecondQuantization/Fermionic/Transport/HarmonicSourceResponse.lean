import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.FrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.GeometricCurrentResponse

set_option linter.style.header false

/-!
# Real harmonic sources for the finite-frequency current response

The bounded source-coupling theorem accepts a real source profile. The complex adiabatic factor
used by `FrequencyResponse` is therefore interpreted as the complexification of two physical real
experiments:

```text
f_cos(s) = Re exp ((-η + iω) (T - s)),
f_sin(s) = Im exp ((-η + iω) (T - s)).
```

At the observation time, `f_cos(T) = 1` and `f_sin(T) = 0`. Consequently the cosine experiment
contains the explicit Peierls contact response, while the sine experiment has no contact
contribution. The two derivative theorems below are direct specializations of the proved bounded
retarded-response theorem; no complex-valued Hamiltonian perturbation is introduced.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice

noncomputable section

/-- Real cosine quadrature of the normalized adiabatic harmonic source. -/
def adiabaticCosineSource (ω η T s : ℝ) : ℝ :=
  (adiabaticFrequencyFactor ω η (T - s)).re

/-- Real sine quadrature of the normalized adiabatic harmonic source. -/
def adiabaticSineSource (ω η T s : ℝ) : ℝ :=
  (adiabaticFrequencyFactor ω η (T - s)).im

/-- The complex adiabatic source is the complexification of its two real quadratures. -/
theorem adiabaticFrequencyFactor_eq_cosine_add_I_sine
    (ω η T s : ℝ) :
    adiabaticFrequencyFactor ω η (T - s) =
      (adiabaticCosineSource ω η T s : ℂ) +
        Complex.I * (adiabaticSineSource ω η T s : ℂ) := by
  apply Complex.ext <;>
    simp [adiabaticCosineSource, adiabaticSineSource]

@[simp]
theorem adiabaticCosineSource_at_observation (ω η T : ℝ) :
    adiabaticCosineSource ω η T T = 1 := by
  simp [adiabaticCosineSource]

@[simp]
theorem adiabaticSineSource_at_observation (ω η T : ℝ) :
    adiabaticSineSource ω η T T = 0 := by
  simp [adiabaticSineSource]

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
