import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Symmetry
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.FiniteTime
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Finite-time Kubo conductivity under unitary spatial symmetry

The existing microscopic unitary covariance theorem supplies a double finite
sum for the retarded kernel and the source-dependent contact operator. This
module performs the otherwise missing analytic step: exchanging those finite
sums with the finite-observation-time integral, under explicit per-component
interval-integrability hypotheses. The contact expectation remains present.

A consumer then applies the existing positive-volume normalization for a
total-current response to a vector-potential source. The normalized tensor
is physically an electrical conductivity only when its supplied operators
are the appropriate current, vector-potential coupling, and contact variation.
No such microscopic realization, DC limit, or point-group action is invented
by the adapter.
-/

namespace QuantumTheory.Transport

open QuantumTheory.LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
variable (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))

/-- After explicitly assuming integrability of every weighted retarded
component, the full *finite-time* response (including the contact term)
has the same separate measured/source matrix transformation law as the
two-time Kubo kernel. Neither continuity nor integrability is inferred
from an arbitrary algebraic unitary time-evolution group. -/
theorem finiteTimeAdiabaticResponse_linearMixing
    {I J : Type*} [Fintype I] [Fintype J]
    (measured : I → (H →L[ℂ] H))
    (source : J → (H →L[ℂ] H))
    (variation : I → J → (H →L[ℂ] H))
    (R : I → I → ℂ) (S : J → J → ℂ)
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (hbar : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ A : H →L[ℂ] H, expectation (Φ A) = expectation A)
    (hMeasured : ∀ i, Φ (measured i) = ∑ k, R i k • measured k)
    (hSource : ∀ j, Φ (source j) = ∑ l, S j l • source l)
    (hVariation : ∀ i j,
      Φ (variation i j) = ∑ k, ∑ l, (R i k * S j l) • variation k l)
    (ω η T : ℝ)
    (hIntegrable : ∀ k l,
      IntervalIntegrable
        (fun s : ℝ => adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility U hbar expectation (measured k) (source l) T s)
        MeasureTheory.volume 0 T)
    (i : I) (j : J) :
    (∑ k, ∑ l, (R i k * S j l) *
      (({ measured := measured k, source := source l,
          observableVariation := variation k l } : ResponseChannel H).finiteTimeAdiabaticResponse
        U hbar expectation ω η T)) =
      (({ measured := measured i, source := source j,
          observableVariation := variation i j } : ResponseChannel H).finiteTimeAdiabaticResponse
        U hbar expectation ω η T) := by
  classical
  let K : I → J → ℝ → ℂ := fun k l s =>
    adiabaticFrequencyPhase ω η (T - s) *
      retardedSusceptibility U hbar expectation (measured k) (source l) T s
  let C : I → J → ℂ := fun k l =>
    expectation (heisenbergEvolution U T (variation k l))
  have hWeighted (k : I) (l : J) :
      IntervalIntegrable (fun s : ℝ => (R i k * S j l) * K k l s)
        MeasureTheory.volume 0 T := by
    exact (hIntegrable k l).const_mul _
  have hInner (k : I) :
      IntervalIntegrable (fun s : ℝ =>
        ∑ l : J, (R i k * S j l) * K k l s) MeasureTheory.volume 0 T := by
    exact IntervalIntegrable.sum (Finset.univ : Finset J)
      (by intro l hl; exact hWeighted k l)
  have hIntegral :
      (∫ s in (0 : ℝ)..T, ∑ k : I, ∑ l : J,
        (R i k * S j l) * K k l s) =
        ∑ k : I, ∑ l : J,
          (R i k * S j l) * (∫ s in (0 : ℝ)..T, K k l s) := by
    rw [intervalIntegral.integral_finsetSum
      (by intro k hk; exact hInner k)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_finsetSum
      (by intro l hl; exact hWeighted k l)]
    apply Finset.sum_congr rfl
    intro l hl
    rw [intervalIntegral.integral_const_mul]
  have hPointwise (s : ℝ) :
      (∑ k : I, ∑ l : J, (R i k * S j l) * K k l s) = K i j s := by
    dsimp [K]
    calc
      (∑ k : I, ∑ l : J, (R i k * S j l) *
          (adiabaticFrequencyPhase ω η (T - s) *
            retardedSusceptibility U hbar expectation (measured k) (source l) T s)) =
        (∑ k : I, ∑ l : J, (R i k * S j l) *
          retardedSusceptibility U hbar expectation (measured k) (source l) T s) *
          adiabaticFrequencyPhase ω η (T - s) := by
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro l hl
            ring
      _ = retardedSusceptibility U hbar expectation (measured i) (source j) T s *
          adiabaticFrequencyPhase ω η (T - s) := by
            rw [retardedSusceptibility_linearMixing U Φ measured source R S
              hU hbar expectation hω hMeasured hSource i j T s]
      _ = _ := mul_comm _ _
  have hIntegralEq :
      (∑ k : I, ∑ l : J,
        (R i k * S j l) * (∫ s in (0 : ℝ)..T, K k l s)) =
        ∫ s in (0 : ℝ)..T, K i j s := by
    rw [← hIntegral]
    apply intervalIntegral.integral_congr
    intro s hs
    exact hPointwise s
  have hContact :
      (∑ k : I, ∑ l : J, (R i k * S j l) * C k l) = C i j := by
    exact expectation_heisenbergEvolution_linearMixing U Φ
      variation R S hU expectation hω hVariation i j T
  change
    (∑ k : I, ∑ l : J, (R i k * S j l) *
      ((∫ s in (0 : ℝ)..T, K k l s) + C k l)) =
      (∫ s in (0 : ℝ)..T, K i j s) + C i j
  calc
    _ = (∑ k : I, ∑ l : J,
          (R i k * S j l) * (∫ s in (0 : ℝ)..T, K k l s)) +
        (∑ k : I, ∑ l : J, (R i k * S j l) * C k l) := by
          simp_rw [mul_add]
          simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hIntegralEq, hContact]

/-- A finite-observation-time conductivity tensor using the shared
positive-volume vector-potential-to-electric-field normalization.
The operator families must be supplied by a physical current and
vector-potential coupling model for the components to be conductivities.
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
Only the already-defined physical scalar normalization is used. -/
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
    finiteTimeAdiabaticResponse_linearMixing U Φ measured source variation R S
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
