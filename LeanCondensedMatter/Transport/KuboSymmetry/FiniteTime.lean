import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.FiniteTime
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.Transport.Core.ConductivityTensor

set_option linter.style.header false

/-!
# Finite-time Kubo conductivity under unitary spatial symmetry

The representation-independent finite-time response covariance is proved in
`QuantumTheory.LinearResponse.Frequency.FiniteTime`. This module only applies
the existing positive-volume normalization for a total-current response to
a vector-potential source, retaining the contact contribution.

The normalized tensor is a physical conductivity when the supplied operators
realize the physical current, vector-potential coupling and contact variation,
the observation time is nonnegative, and the driving frequency and switching
rate are not both zero. The algebraic definition remains total; no zero-rate,
DC, thermodynamic limit or microscopic point-group realization is asserted.
-/

namespace QuantumTheory.Transport

open QuantumTheory.LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
variable (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))

/-- A finite-observation-time conductivity tensor using the shared
positive-volume vector-potential-to-electric-field normalization.
The operator families must be supplied by a physical current and
vector-potential coupling model for the components to be conductivities.
For physical electric-field conversion require `0 ≤ T` and
`ω ≠ 0 ∨ η ≠ 0`; the latter guarantees a nonzero denominator by
`finiteVolumeConductivityDenominator_ne_zero`. At `ω = η = 0` the totalized
inverse returns zero, not a physical DC conductivity.
There is no new tensor representation or normalization convention. -/
noncomputable def finiteTimeVectorPotentialConductivityTensor
    {I : Type*}
    (measured source : I → (H →L[ℂ] H))
    (variation : I → I → (H →L[ℂ] H))
    (volume : PositiveVolume)
    (hbar ω η T : ℝ) (expectation : NormalizedExpectation H) :
    ConductivityTensor I where
  component i j := finiteVolumeConductivityFromVectorPotential volume ω η
    (({ measured := measured i, source := source j,
        observableVariation := variation i j } : ResponseChannel H).finiteTimeAdiabaticResponse
      U hbar expectation ω η T)

/-- Microscopic unitary covariance and interval integrability imply
the two-sided matrix constraint on the *normalized* finite-volume tensor.
Only the already-defined scalar normalization is used. The equality is algebraic
also at zero rates; its physical interpretation requires the nonzero-rate
condition documented on the tensor definition. -/
theorem finiteTimeVectorPotentialConductivityTensor_linearMixing
    {I : Type*} [Fintype I]
    (measured source : I → (H →L[ℂ] H))
    (variation : I → I → (H →L[ℂ] H))
    (R S : I → I → ℂ)
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (volume : PositiveVolume)
    (hbar ω η T : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ A : H →L[ℂ] H, expectation (Φ A) = expectation A)
    (hMeasured : ∀ i, Φ (measured i) = ∑ k, R i k • measured k)
    (hSource : ∀ j, Φ (source j) = ∑ l, S j l • source l)
    (hVariation : ∀ i j,
      Φ (variation i j) = ∑ k, ∑ l, (R i k * S j l) • variation k l)
    (hIntegrable : ∀ k l,
      IntervalIntegrable
        (fun s : ℝ => adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility U hbar expectation (measured k) (source l) T s)
        MeasureTheory.volume 0 T)
    (i j : I) :
    (∑ k, ∑ l, (R i k * S j l) *
      (finiteTimeVectorPotentialConductivityTensor U measured source variation
        volume hbar ω η T expectation).component k l) =
      (finiteTimeVectorPotentialConductivityTensor U measured source variation
        volume hbar ω η T expectation).component i j := by
  classical
  let X : I → I → ℂ := fun k l =>
    (({ measured := measured k, source := source l,
        observableVariation := variation k l } : ResponseChannel H).finiteTimeAdiabaticResponse
      U hbar expectation ω η T)
  let n := finiteVolumeConductivityNormalization volume ω η
  have hX :
      (∑ k : I, ∑ l : I, (R i k * S j l) * X k l) = X i j :=
    ResponseChannel.finiteTimeAdiabaticResponse_linearMixing U Φ measured source variation R S
      hU hbar expectation hω hMeasured hSource hVariation ω η T hIntegrable i j
  change (∑ k : I, ∑ l : I, (R i k * S j l) * (X k l * n)) = X i j * n
  calc
    _ = (∑ k : I, ∑ l : I, (R i k * S j l) * X k l) * n := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := by rw [hX]

end
end QuantumTheory.Transport
