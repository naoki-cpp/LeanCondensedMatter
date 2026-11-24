import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.AdiabaticSwitching
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.LimitOrder
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Symmetry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Finite-time scalar adiabatic response

This module owns the representation-independent finite-observation-time transform used by the
frequency-domain response stack. For a scalar causal kernel `K` and the canonical adiabatic phase

```text
exp ((i ω - η) τ),
```

the finite-time transform is

```text
∫₀ᵀ dτ exp ((i ω - η) τ) K(τ).
```

The module also applies the same finite-time phase directly to a neutral `ResponseChannel`, keeping
its retarded measured/source kernel and explicit observable-variation contact expectation together.
It names convergence in the observation-time variable `T → +∞` and remains independent of particle
statistics, Fock-space realizations, current operators, lattice geometry, and conductivity
normalization. Microscopic symmetry extends to the integrated response by finite-sum interchange
under explicit interval-integrability hypotheses, including the contact term. Zero-switching and static-limit orderings are owned by `Frequency.LimitOrder`.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

/-- Finite-observation-time adiabatic transform of a scalar causal kernel. No limit is taken. -/
noncomputable def finiteTimeAdiabaticTransform
    (kernel : ℝ → ℂ) (ω η T : ℝ) : ℂ :=
  ∫ τ in (0 : ℝ)..T, adiabaticFrequencyPhase ω η τ * kernel τ

@[simp]
theorem finiteTimeAdiabaticTransform_zero_time
    (kernel : ℝ → ℂ) (ω η : ℝ) :
    finiteTimeAdiabaticTransform kernel ω η 0 = 0 := by
  simp [finiteTimeAdiabaticTransform]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ResponseChannel

/-- Finite-observation-time adiabatic response of a neutral response channel.

The source value at the observation time has been factored out, so the retarded kernel carries the
lag phase `exp ((i ω - η) (T - s))` while the explicit observable variation contributes its
contact expectation at `T`. No stationarity or infinite-time limit is assumed. -/
noncomputable def finiteTimeAdiabaticResponse
    (channel : ResponseChannel H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ) (expectation : NormalizedExpectation H)
    (ω η T : ℝ) : ℂ :=
  (∫ s in (0 : ℝ)..T,
      adiabaticFrequencyPhase ω η (T - s) *
        channel.retardedKernel U hbar expectation T s) +
    channel.contactExpectation U expectation T

/-- A fixed-observable channel has no contact contribution, so its finite-time adiabatic response is
exactly the retarded measured/source transform. -/
theorem finiteTimeAdiabaticResponse_fixed
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ) (expectation : NormalizedExpectation H)
    (measured source : H →L[ℂ] H) (ω η T : ℝ) :
    (fixed measured source).finiteTimeAdiabaticResponse U hbar expectation ω η T =
      ∫ s in (0 : ℝ)..T,
        adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility U hbar
            expectation measured source T s := by
  rw [finiteTimeAdiabaticResponse, fixed_contactExpectation]
  simp [retardedKernel, fixed]

/-- In a stationary state, a nonnegative observation interval is a lag transform plus the
stationary observable-variation expectation. The source value at observation time is factored out. -/
theorem finiteTimeAdiabaticResponse_eq_stationaryLag
    (channel : ResponseChannel H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ) (expectation : NormalizedExpectation H)
    (hstationary : IsStationary U expectation)
    (ω η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    channel.finiteTimeAdiabaticResponse U hbar expectation ω η T =
      finiteTimeAdiabaticTransform
          (fun τ => commutatorSusceptibility U hbar expectation
            channel.measured channel.source τ 0) ω η T +
        expectation channel.observableVariation := by
  rw [finiteTimeAdiabaticResponse, contactExpectation,
    hstationary T channel.observableVariation]
  congr 1
  let g : ℝ → ℂ := fun τ => adiabaticFrequencyPhase ω η τ *
    commutatorSusceptibility U hbar
      expectation channel.measured channel.source τ 0
  change (∫ s in (0 : ℝ)..T, adiabaticFrequencyPhase ω η (T - s) *
      retardedSusceptibility U hbar
        expectation channel.measured channel.source T s) =
    ∫ τ in (0 : ℝ)..T, g τ
  calc
    _ = ∫ s in (0 : ℝ)..T, g (T - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsIcc : s ∈ Set.Icc (0 : ℝ) T := by
        simpa [Set.uIcc_of_le hT] using hs
      change adiabaticFrequencyPhase ω η (T - s) *
        retardedSusceptibility U hbar
          expectation channel.measured channel.source T s =
          g (T - s)
      rw [retardedSusceptibility_eq_timeDifference_of_stationary
        U hbar
        expectation hstationary channel.measured channel.source T s]
      simp [g, sub_nonneg.mpr hsIcc.2]
    _ = ∫ τ in (0 : ℝ)..T, g τ := by
      simpa using intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ)) (b := T) g T

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
  have hIntegral :
      (∫ s in (0 : ℝ)..T, ∑ k : I, ∑ l : J,
        (R i k * S j l) * K k l s) =
        ∑ k : I, ∑ l : J,
          (R i k * S j l) * (∫ s in (0 : ℝ)..T, K k l s) := by
    have hProd :
        (∫ s in (0 : ℝ)..T, ∑ p : I × J,
          (R i p.1 * S j p.2) * K p.1 p.2 s) =
          ∑ p : I × J,
            (R i p.1 * S j p.2) * (∫ s in (0 : ℝ)..T, K p.1 p.2 s) := by
      rw [intervalIntegral.integral_finsetSum
        (by intro p hp; exact (hIntegrable p.1 p.2).const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
    simpa only [Fintype.sum_prod_type] using hProd
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

end ResponseChannel

end
end LinearResponse
end QuantumTheory
