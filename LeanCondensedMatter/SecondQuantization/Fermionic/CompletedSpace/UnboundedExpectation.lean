import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbs

set_option linter.style.header false

/-!
# Integrable diagonal Gibbs expectations

The canonical `DensityOperator.expectation` API accepts bounded continuous linear observables.
Diagonal observables such as the free Hamiltonian or total particle number can be unbounded on the
completed fermionic Fock space, so their thermal expectations are represented separately as
absolutely summable occupation-basis series.

This file turns the integrability predicate from `FreeGibbs.lean` into an explicit expectation and
specializes it to the completed free Hamiltonian and total-number observables.  No coercion of an
unbounded `LinearPMap` to a bounded operator is introduced.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*}

/-- The occupation-series expectation of a real diagonal observable.  This definition is intended
to be used together with `CompletedFreeGibbsIntegrableDiagonal`, which ensures that the `tsum` is
not the nonsummable junk value. -/
noncomputable def completedFreeGibbsDiagonalExpectation
    (ε : Mode → ℝ) (β : ℝ) (a : Occupation Mode → ℝ) : ℝ :=
  ∑' n : Occupation Mode, completedFreeGibbsProbability ε β n * a n

/-- The Gibbs integrability predicate gives ordinary summability of the real expectation series. -/
theorem completedFreeGibbsIntegrableDiagonal_summable
    (ε : Mode → ℝ) (β : ℝ) (a : Occupation Mode → ℝ)
    (hint : CompletedFreeGibbsIntegrableDiagonal ε β a) :
    Summable fun n : Occupation Mode => completedFreeGibbsProbability ε β n * a n :=
  Summable.of_norm hint

/-- An integrable real diagonal observable has the expected occupation-basis `HasSum`. -/
theorem hasSum_completedFreeGibbsDiagonalExpectation
    (ε : Mode → ℝ) (β : ℝ) (a : Occupation Mode → ℝ)
    (hint : CompletedFreeGibbsIntegrableDiagonal ε β a) :
    HasSum
      (fun n : Occupation Mode => completedFreeGibbsProbability ε β n * a n)
      (completedFreeGibbsDiagonalExpectation ε β a) := by
  exact (completedFreeGibbsIntegrableDiagonal_summable ε β a hint).hasSum

/-- The constant-one diagonal observable is Gibbs integrable whenever the Gibbs state exists. -/
theorem completedFreeGibbsIntegrableDiagonal_one
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β) :
    CompletedFreeGibbsIntegrableDiagonal ε β (fun _ => 1) := by
  unfold CompletedFreeGibbsIntegrableDiagonal
  simpa using (hasSum_completedFreeGibbsProbability ε β hsum).summable.norm

/-- The unbounded-diagonal expectation has the same normalization as the density-state API. -/
@[simp]
theorem completedFreeGibbsDiagonalExpectation_one
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β) :
    completedFreeGibbsDiagonalExpectation ε β (fun _ => 1) = 1 := by
  unfold completedFreeGibbsDiagonalExpectation
  simpa using (hasSum_completedFreeGibbsProbability ε β hsum).tsum_eq

/-- An integrable nonnegative diagonal observable has nonnegative Gibbs expectation. -/
theorem completedFreeGibbsDiagonalExpectation_nonneg
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
    (a : Occupation Mode → ℝ) (_hint : CompletedFreeGibbsIntegrableDiagonal ε β a)
    (ha : ∀ n, 0 ≤ a n) :
    0 ≤ completedFreeGibbsDiagonalExpectation ε β a := by
  unfold completedFreeGibbsDiagonalExpectation
  exact tsum_nonneg fun n =>
    mul_nonneg (completedFreeGibbsProbability_nonneg ε β hsum n) (ha n)

/-- Integrability is stable under pointwise addition of real diagonal observables. -/
theorem completedFreeGibbsIntegrableDiagonal_add
    (ε : Mode → ℝ) (β : ℝ) (a b : Occupation Mode → ℝ)
    (ha : CompletedFreeGibbsIntegrableDiagonal ε β a)
    (hb : CompletedFreeGibbsIntegrableDiagonal ε β b) :
    CompletedFreeGibbsIntegrableDiagonal ε β (fun n => a n + b n) := by
  have hsa := completedFreeGibbsIntegrableDiagonal_summable ε β a ha
  have hsb := completedFreeGibbsIntegrableDiagonal_summable ε β b hb
  apply Summable.norm
  simpa [mul_add] using hsa.add hsb

/-- Gibbs expectation is additive on integrable real diagonal observables. -/
theorem completedFreeGibbsDiagonalExpectation_add
    (ε : Mode → ℝ) (β : ℝ) (a b : Occupation Mode → ℝ)
    (ha : CompletedFreeGibbsIntegrableDiagonal ε β a)
    (hb : CompletedFreeGibbsIntegrableDiagonal ε β b) :
    completedFreeGibbsDiagonalExpectation ε β (fun n => a n + b n) =
      completedFreeGibbsDiagonalExpectation ε β a +
        completedFreeGibbsDiagonalExpectation ε β b := by
  unfold completedFreeGibbsDiagonalExpectation
  have hsa := completedFreeGibbsIntegrableDiagonal_summable ε β a ha
  have hsb := completedFreeGibbsIntegrableDiagonal_summable ε β b hb
  rw [← hsa.tsum_add hsb]
  apply tsum_congr
  intro n
  ring

/-- Integrability condition for the unbounded completed free Hamiltonian expectation. -/
def CompletedFreeEnergyIntegrable (ε : Mode → ℝ) (β : ℝ) : Prop :=
  CompletedFreeGibbsIntegrableDiagonal ε β (fermionEnergy ε)

/-- Thermal expectation of the completed free Hamiltonian, represented by its diagonal occupation
energy series. -/
noncomputable def completedFreeEnergyExpectation (ε : Mode → ℝ) (β : ℝ) : ℝ :=
  completedFreeGibbsDiagonalExpectation ε β (fermionEnergy ε)

/-- Under the explicit energy-integrability hypothesis, the free-energy expectation is represented
by an absolutely convergent occupation-basis series. -/
theorem hasSum_completedFreeEnergyExpectation
    (ε : Mode → ℝ) (β : ℝ) (hint : CompletedFreeEnergyIntegrable ε β) :
    HasSum
      (fun n : Occupation Mode => completedFreeGibbsProbability ε β n * fermionEnergy ε n)
      (completedFreeEnergyExpectation ε β) := by
  exact hasSum_completedFreeGibbsDiagonalExpectation ε β (fermionEnergy ε) hint

/-- Integrability condition for the unbounded total particle-number expectation. -/
def CompletedFreeTotalNumberIntegrable (ε : Mode → ℝ) (β : ℝ) : Prop :=
  CompletedFreeGibbsIntegrableDiagonal ε β (fun n : Occupation Mode => (particleNumber n : ℝ))

/-- Thermal expectation of the completed total particle-number operator, represented by its
occupation-number series. -/
noncomputable def completedFreeTotalNumberExpectation (ε : Mode → ℝ) (β : ℝ) : ℝ :=
  completedFreeGibbsDiagonalExpectation ε β
    (fun n : Occupation Mode => (particleNumber n : ℝ))

/-- Under the explicit number-integrability hypothesis, the total particle-number expectation is
represented by an absolutely convergent occupation-basis series. -/
theorem hasSum_completedFreeTotalNumberExpectation
    (ε : Mode → ℝ) (β : ℝ) (hint : CompletedFreeTotalNumberIntegrable ε β) :
    HasSum
      (fun n : Occupation Mode =>
        completedFreeGibbsProbability ε β n * (particleNumber n : ℝ))
      (completedFreeTotalNumberExpectation ε β) := by
  exact hasSum_completedFreeGibbsDiagonalExpectation ε β
    (fun n : Occupation Mode => (particleNumber n : ℝ)) hint

end
end Fermionic
end SecondQuantization
