import LeanCondensedMatter.QuantumTheory.LinearResponse.PurePointDynamics
import Mathlib.Topology.Algebra.InfiniteSum.Module

set_option linter.style.header false

/-!
# Time-domain pure-point Lehmann representation

This module identifies the causal commutator susceptibility of the diagonal pure-point expectation
with its countable transition series.  The infinite-dimensional theorem keeps every rearrangement
hypothesis explicit.  `PurePointTimeDomainSummable` requires absolute summability of the two ordered
products entering the commutator and of the already defined physical transition weights.

On the causal half-line the result is

`χᴿ_AB(τ) = ∑' (m,n), Wₘₙ exp (i (Eₘ - Eₙ) τ / ℏ)`,

where

`Wₘₙ = (i / ℏ) (pₘ - pₙ) Aₘₙ Bₙₘ`.

For a finite spectral index all summability assumptions are automatic.  The exchange of this
transition series with the fixed-rate Bochner time integral is left to the next module.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
variable (system : BoundedFreeSystem H)

/-- The ordered product with diagonal probability `pₘ` entering
`ω(A_I(τ) B)`. -/
noncomputable def purePointForwardWeight
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) : ℂ :=
  (data.probability mn.1 : ℂ) *
    inner ℂ (data.basis mn.1) (A (data.basis mn.2)) *
    inner ℂ (data.basis mn.2) (B (data.basis mn.1))

/-- The ordered product with diagonal probability `pₘ` entering
`ω(B A_I(τ))`. -/
noncomputable def purePointBackwardWeight
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) : ℂ :=
  (data.probability mn.1 : ℂ) *
    inner ℂ (data.basis mn.1) (B (data.basis mn.2)) *
    inner ℂ (data.basis mn.2) (A (data.basis mn.1))

/-- Explicit absolute-summability assumptions used to expand and rearrange the countable
commutator series. -/
def PurePointTimeDomainSummable
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) : Prop :=
  (Summable fun mn : ι × ι => ‖purePointForwardWeight system data A B mn‖) ∧
  (Summable fun mn : ι × ι => ‖purePointBackwardWeight system data A B mn‖) ∧
  PurePointLehmannSummable system data A B

/-- In finite dimension all time-domain rearrangement assumptions are automatic. -/
theorem purePointTimeDomainSummable_of_finite
    [Finite ι] (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) :
    PurePointTimeDomainSummable system data A B := by
  exact ⟨Summable.of_finite, Summable.of_finite,
    purePointLehmannSummable_of_finite system data A B⟩

/-- Schrödinger phases have unit norm. -/
@[simp]
theorem norm_purePointSchrodingerPhase
    (data : PurePointLehmannData system ι) (i : ι) (t : ℝ) :
    ‖purePointSchrodingerPhase system data i t‖ = 1 := by
  rw [purePointSchrodingerPhase, Complex.norm_exp]
  simp

/-- Relative transition phases have unit norm. -/
@[simp]
theorem norm_purePointTransitionPhase
    (data : PurePointLehmannData system ι)
    (m n : ι) (t : ℝ) :
    ‖purePointTransitionPhase system data m n t‖ = 1 := by
  simp [purePointTransitionPhase]

/-- One forward ordered transition at time `τ`. -/
noncomputable def purePointForwardTimeTerm
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) (mn : ι × ι) : ℂ :=
  purePointForwardWeight system data A B mn *
    purePointTransitionPhase system data mn.1 mn.2 τ

/-- One backward ordered transition at time `τ`. -/
noncomputable def purePointBackwardTimeTerm
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) (mn : ι × ι) : ℂ :=
  purePointBackwardWeight system data A B mn *
    purePointTransitionPhase system data mn.2 mn.1 τ

/-- One physical time-domain Lehmann transition. -/
noncomputable def purePointTimeDomainTerm
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) (mn : ι × ι) : ℂ :=
  purePointTransitionWeight system data A B mn *
    purePointTransitionPhase system data mn.1 mn.2 τ

/-- The physical transition term written with the explicit energy-difference exponential. -/
theorem purePointTimeDomainTerm_eq_exp_energyDifference
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) (mn : ι × ι) :
    purePointTimeDomainTerm system data A B τ mn =
      purePointTransitionWeight system data A B mn *
        Complex.exp
          (Complex.I * ((((data.energy mn.1 - data.energy mn.2) * τ) /
            system.hbar : ℝ) : ℂ)) := by
  rw [purePointTimeDomainTerm,
    purePointTransitionPhase_eq_exp_energyDifference]

/-- The countable time-domain pure-point Lehmann series. -/
noncomputable def purePointTimeDomainSeries
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) : ℂ :=
  ∑' mn : ι × ι, purePointTimeDomainTerm system data A B τ mn

/-- Absolute summability of the forward weights is preserved by the unit transition phase. -/
theorem summable_purePointForwardTimeTerm
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : PurePointTimeDomainSummable system data A B) :
    Summable (purePointForwardTimeTerm system data A B τ) := by
  apply hsum.1.of_norm_bounded
  intro mn
  simp [purePointForwardTimeTerm, norm_mul]

/-- Absolute summability of the backward weights is preserved by the unit transition phase. -/
theorem summable_purePointBackwardTimeTerm
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : PurePointTimeDomainSummable system data A B) :
    Summable (purePointBackwardTimeTerm system data A B τ) := by
  apply hsum.2.1.of_norm_bounded
  intro mn
  simp [purePointBackwardTimeTerm, norm_mul]

/-- Absolute summability of the physical weights is preserved by the unit transition phase. -/
theorem summable_purePointTimeDomainTerm
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : PurePointTimeDomainSummable system data A B) :
    Summable (purePointTimeDomainTerm system data A B τ) := by
  apply hsum.2.2.of_norm_bounded
  intro mn
  simp [purePointTimeDomainTerm, norm_mul]

/-- Expansion of `ω(A_I(τ) B)` into the forward ordered transition series. -/
theorem purePointExpectation_heisenberg_mul_eq_tsum
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : PurePointTimeDomainSummable system data A B) :
    purePointNormalizedExpectation system data
        (heisenbergEvolution system A τ * B) =
      ∑' mn : ι × ι,
        purePointForwardTimeTerm system data A B τ mn := by
  rw [purePointNormalizedExpectation_apply]
  have htime := summable_purePointForwardTimeTerm system data A B τ hsum
  rw [htime.tsum_prod]
  apply tsum_congr
  intro m
  simp only [mul_apply_eq_comp]
  have hinner := data.basis.hasSum_inner_mul_inner
    (((heisenbergEvolution system A τ)†) (data.basis m))
    (B (data.basis m))
  have hscaled := hinner.mul_left (data.probability m : ℂ)
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [← hscaled.tsum_eq]
  apply tsum_congr
  intro n
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [inner_purePointBasis_heisenbergEvolution system data A m n τ]
  simp [purePointForwardTimeTerm, purePointForwardWeight]
  ring

/-- Expansion of `ω(B A_I(τ))` into the backward ordered transition series. -/
theorem purePointExpectation_mul_heisenberg_eq_tsum
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : PurePointTimeDomainSummable system data A B) :
    purePointNormalizedExpectation system data
        (B * heisenbergEvolution system A τ) =
      ∑' mn : ι × ι,
        purePointBackwardTimeTerm system data A B τ mn := by
  rw [purePointNormalizedExpectation_apply]
  have htime := summable_purePointBackwardTimeTerm system data A B τ hsum
  rw [htime.tsum_prod]
  apply tsum_congr
  intro m
  simp only [mul_apply_eq_comp]
  have hinner := data.basis.hasSum_inner_mul_inner
    ((B†) (data.basis m))
    (heisenbergEvolution system A τ (data.basis m))
  have hscaled := hinner.mul_left (data.probability m : ℂ)
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [← hscaled.tsum_eq]
  apply tsum_congr
  intro n
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [inner_purePointBasis_heisenbergEvolution system data A n m τ]
  simp [purePointBackwardTimeTerm, purePointBackwardWeight]
  ring

/-- The two ordered transition sums combine into the physical `(pₘ - pₙ)` transition series. -/
theorem purePoint_forward_sub_backward_eq_timeDomainSeries
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : PurePointTimeDomainSummable system data A B) :
    (Complex.I / (system.hbar : ℂ)) *
        ((∑' mn : ι × ι,
            purePointForwardTimeTerm system data A B τ mn) -
          ∑' mn : ι × ι,
            purePointBackwardTimeTerm system data A B τ mn) =
      purePointTimeDomainSeries system data A B τ := by
  have hforward := summable_purePointForwardTimeTerm system data A B τ hsum
  have hbackward := summable_purePointBackwardTimeTerm system data A B τ hsum
  have hbackwardSwap : Summable fun mn : ι × ι =>
      purePointBackwardTimeTerm system data A B τ mn.swap := by
    change Summable
      (purePointBackwardTimeTerm system data A B τ ∘ Prod.swap)
    exact hbackward.comp_injective (Equiv.prodComm ι ι).injective
  have hswap :
      (∑' mn : ι × ι,
          purePointBackwardTimeTerm system data A B τ mn) =
        ∑' mn : ι × ι,
          purePointBackwardTimeTerm system data A B τ mn.swap := by
    symm
    simpa using (Equiv.prodComm ι ι).tsum_eq
      (purePointBackwardTimeTerm system data A B τ)
  rw [hswap]
  rw [← hforward.tsum_sub hbackwardSwap]
  rw [← tsum_mul_left]
  rw [purePointTimeDomainSeries]
  apply tsum_congr
  intro mn
  simp [purePointTimeDomainTerm, purePointTransitionWeight,
    purePointForwardTimeTerm, purePointForwardWeight,
    purePointBackwardTimeTerm, purePointBackwardWeight]
  ring

/-- The physical commutator susceptibility equals the countable time-domain Lehmann series. -/
theorem commutatorSusceptibility_purePoint_eq_timeDomainSeries
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : PurePointTimeDomainSummable system data A B) :
    commutatorSusceptibility system
        (purePointNormalizedExpectation system data) A B τ 0 =
      purePointTimeDomainSeries system data A B τ := by
  rw [commutatorSusceptibility]
  simp only [heisenbergEvolution_zero]
  rw [map_sub]
  rw [purePointExpectation_heisenberg_mul_eq_tsum system data A B τ hsum]
  rw [purePointExpectation_mul_heisenberg_eq_tsum system data A B τ hsum]
  exact purePoint_forward_sub_backward_eq_timeDomainSeries
    system data A B τ hsum

/-- On the causal half-line, the retarded kernel equals the countable pure-point transition
series. -/
theorem retardedTimeDifferenceKernel_purePoint_eq_timeDomainSeries_of_nonneg
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsum : PurePointTimeDomainSummable system data A B) :
    retardedTimeDifferenceKernel system
        (purePointNormalizedExpectation system data) A B τ =
      purePointTimeDomainSeries system data A B τ := by
  rw [retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
    system (purePointNormalizedExpectation system data) A B hτ]
  exact commutatorSusceptibility_purePoint_eq_timeDomainSeries
    system data A B τ hsum

/-- For a finite spectral index, the physical retarded kernel is the usual finite double
transition sum. -/
theorem retardedTimeDifferenceKernel_purePoint_eq_finite_sum_of_nonneg
    [Fintype ι] (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) {τ : ℝ} (hτ : 0 ≤ τ) :
    retardedTimeDifferenceKernel system
        (purePointNormalizedExpectation system data) A B τ =
      ∑ mn : ι × ι,
        purePointTimeDomainTerm system data A B τ mn := by
  rw [retardedTimeDifferenceKernel_purePoint_eq_timeDomainSeries_of_nonneg
    system data A B hτ
      (purePointTimeDomainSummable_of_finite system data A B)]
  simp [purePointTimeDomainSeries]

end
end LinearResponse
end QuantumTheory
