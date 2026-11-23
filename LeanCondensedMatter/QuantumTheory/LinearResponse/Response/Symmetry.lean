import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Channel
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Unitary spatial symmetries of the Kubo response

A complex-linear star-algebra symmetry of bounded observables that fixes the
free propagators commutes with Heisenberg evolution. If the equilibrium
expectation is invariant under the same symmetry, the causal commutator
kernel and the full response channel are invariant after transforming both
measured and source operators.

The channel proof also transforms the first-order observable variation:
it does **not** discard the contact contribution. These statements are
independent of specific current operators and physical conductivity
normalization. Antiunitary time reversal, which reverses time, is a
different symmetry and belongs to the reciprocity theory.
-/

namespace QuantumTheory.LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
variable (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))

/-- A star-algebra symmetry fixing every free propagator commutes with
Heisenberg evolution. This is derived from multiplicativity and
preservation of the star operation, not assumed on the evolved operators. -/
theorem heisenbergEvolution_symmetry
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (t : ℝ) (A : H →L[ℂ] H) :
    heisenbergEvolution U t (Φ A) = Φ (heisenbergEvolution U t A) := by
  simp only [heisenbergEvolution_apply, map_mul, map_star, hU t]

/-- A symmetry-invariant equilibrium expectation has invariant commutator
susceptibility when *both* measured and source operators are transformed. -/
theorem commutatorSusceptibility_symmetry
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (hbar : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ A : H →L[ℂ] H, expectation (Φ A) = expectation A)
    (A B : H →L[ℂ] H) (t s : ℝ) :
    commutatorSusceptibility U hbar expectation (Φ A) (Φ B) t s =
      commutatorSusceptibility U hbar expectation A B t s := by
  have hcomm (X Y : H →L[ℂ] H) :
      ⁅Φ X, Φ Y⁆ = Φ ⁅X, Y⁆ := by
    simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul]
  unfold commutatorSusceptibility
  rw [heisenbergEvolution_symmetry U Φ hU t A,
    heisenbergEvolution_symmetry U Φ hU s B, hcomm, hω]

/-- The same microscopic invariance descends to the retarded causal kernel.
The causal support condition is untouched by a unitary spatial symmetry. -/
theorem retardedSusceptibility_symmetry
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (hbar : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ A : H →L[ℂ] H, expectation (Φ A) = expectation A)
    (A B : H →L[ℂ] H) (t s : ℝ) :
    retardedSusceptibility U hbar expectation (Φ A) (Φ B) t s =
      retardedSusceptibility U hbar expectation A B t s := by
  by_cases hs : s ≤ t
  · simpa [retardedSusceptibility, hs] using
      commutatorSusceptibility_symmetry U Φ hU hbar expectation hω A B t s
  · simp [retardedSusceptibility, hs]

/-- The explicit contact expectation transforms covariantly under the same
microscopic symmetry as the retarded kernel. -/
theorem expectation_heisenbergEvolution_symmetry
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (expectation : NormalizedExpectation H)
    (hω : ∀ A : H →L[ℂ] H, expectation (Φ A) = expectation A)
    (C : H →L[ℂ] H) (t : ℝ) :
    expectation (heisenbergEvolution U t (Φ C)) =
      expectation (heisenbergEvolution U t C) := by
  rw [heisenbergEvolution_symmetry U Φ hU t C, hω]

/-- The *full* scalar Kubo response is invariant under a unitary symmetry,
including the observable-variation/contact contribution. A source profile
is held fixed, and no assumption about zero contact or conductivity units
is made. -/
theorem ResponseChannel.causalResponse_symmetry
    (channel : ResponseChannel H)
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (hbar : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ A : H →L[ℂ] H, expectation (Φ A) = expectation A)
    (f : ℝ → ℝ) (t : ℝ) :
    ({ measured := Φ channel.measured,
       source := Φ channel.source,
       observableVariation := Φ channel.observableVariation } : ResponseChannel H).causalResponse
         U hbar expectation f t =
      channel.causalResponse U hbar expectation f t := by
  change
    (∫ s in (0 : ℝ)..t, (f s : ℂ) *
      retardedSusceptibility U hbar expectation (Φ channel.measured) (Φ channel.source) t s) +
      expectation (heisenbergEvolution U t (Φ channel.observableVariation)) =
    (∫ s in (0 : ℝ)..t, (f s : ℂ) *
      retardedSusceptibility U hbar expectation channel.measured channel.source t s) +
      expectation (heisenbergEvolution U t channel.observableVariation)
  rw [expectation_heisenbergEvolution_symmetry U Φ hU expectation hω
    channel.observableVariation t]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  change (f s : ℂ) *
      retardedSusceptibility U hbar expectation (Φ channel.measured) (Φ channel.source) t s =
    (f s : ℂ) *
      retardedSusceptibility U hbar expectation channel.measured channel.source t s
  rw [retardedSusceptibility_symmetry U Φ hU hbar expectation hω
    channel.measured channel.source t s]

end
end QuantumTheory.LinearResponse
