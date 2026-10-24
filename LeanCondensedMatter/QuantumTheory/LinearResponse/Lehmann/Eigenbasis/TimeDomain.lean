import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.Dynamics
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.Susceptibility
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Time-domain eigenbasis Lehmann representation

This module identifies the causal commutator susceptibility of the diagonal eigenbasis expectation
with its countable transition series.  Each physical term projects its weight from the canonical
`LehmannTransitionData` adapter defined in `Lehmann.lean`; the corresponding energy gap is the same
record field used by the frequency-domain path.  The infinite-dimensional theorem keeps every
rearrangement hypothesis explicit.  `EigenbasisTimeDomainSummable` requires absolute summability only of
the two ordered products entering the commutator; physical transition-weight summability is derived.

On the causal half-line the result is

`χᴿ_AB(τ) = ∑' (m,n), Wₘₙ exp (i (Eₘ - Eₙ) τ / ℏ)`,

where

`Wₘₙ = (i / ℏ) (pₘ - pₙ) Aₘₙ Bₙₘ`.

For a finite spectral index all summability assumptions are automatic.  The exchange of this
transition series with the fixed-rate Bochner time integral is left to the next module.
-/

namespace QuantumTheory
namespace LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
variable (system : BoundedFreeSystem H)

/-- The ordered product with diagonal probability `pₘ` entering
`ω(A_I(τ) B)`. -/
noncomputable def eigenbasisForwardWeight
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) : ℂ :=
  (data.probability mn.1 : ℂ) *
    inner ℂ (data.basis mn.1) (A (data.basis mn.2)) *
    inner ℂ (data.basis mn.2) (B (data.basis mn.1))

/-- The ordered product with diagonal probability `pₘ` entering
`ω(B A_I(τ))`. -/
noncomputable def eigenbasisBackwardWeight
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) : ℂ :=
  (data.probability mn.1 : ℂ) *
    inner ℂ (data.basis mn.1) (B (data.basis mn.2)) *
    inner ℂ (data.basis mn.2) (A (data.basis mn.1))

/-- Explicit absolute-summability assumptions used to expand and rearrange the countable
commutator series. -/
def EigenbasisTimeDomainSummable
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) : Prop :=
  (Summable fun mn : ι × ι => ‖eigenbasisForwardWeight system data A B mn‖) ∧
  Summable fun mn : ι × ι => ‖eigenbasisBackwardWeight system data A B mn‖

/-- Absolute summability of both ordered commutator products implies absolute summability
of the canonical Lehmann transition weights. The separate ordered-product hypotheses
remain the assumptions used for time-domain trace rearrangements. -/
theorem EigenbasisTimeDomainSummable.lehmannSummable
    (data : EnergyEigenbasisLehmannData system ι) (A B : H →L[ℂ] H)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    EigenbasisLehmannSummable system data A B := by
  change Summable fun mn : ι × ι => ‖(eigenbasisTransitionData system data A B mn).weight‖
  have hphysical := ((Summable.of_norm hsum.1).sub
    ((Summable.of_norm hsum.2).comp_injective (Equiv.prodComm ι ι).injective)).mul_left
      (Complex.I / (system.hbar : ℂ))
  convert hphysical.norm using 1
  funext mn
  congr 1
  simp [eigenbasisTransitionData, orderedLehmannTransitionWeight,
    eigenbasisForwardWeight, eigenbasisBackwardWeight]
  ring

/-- In finite dimension all time-domain rearrangement assumptions are automatic. -/
theorem eigenbasisTimeDomainSummable_of_finite
    [Finite ι] (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) :
    EigenbasisTimeDomainSummable system data A B := by
  exact ⟨Summable.of_finite, Summable.of_finite⟩

/-- Schrödinger phases have unit norm. -/
@[simp]
theorem norm_eigenbasisSchrodingerPhase
    (data : EnergyEigenbasisLehmannData system ι) (i : ι) (t : ℝ) :
    ‖eigenbasisSchrodingerPhase system data i t‖ = 1 := by
  rw [eigenbasisSchrodingerPhase, Complex.norm_exp]
  simp

/-- Relative transition phases have unit norm. -/
@[simp]
theorem norm_eigenbasisTransitionPhase
    (data : EnergyEigenbasisLehmannData system ι)
    (m n : ι) (t : ℝ) :
    ‖eigenbasisTransitionPhase system data m n t‖ = 1 := by
  simp [eigenbasisTransitionPhase]

/-- One forward ordered transition at time `τ`. -/
noncomputable def eigenbasisForwardTimeTerm
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) (mn : ι × ι) : ℂ :=
  eigenbasisForwardWeight system data A B mn *
    eigenbasisTransitionPhase system data mn.1 mn.2 τ

/-- One backward ordered transition at time `τ`. -/
noncomputable def eigenbasisBackwardTimeTerm
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) (mn : ι × ι) : ℂ :=
  eigenbasisBackwardWeight system data A B mn *
    eigenbasisTransitionPhase system data mn.2 mn.1 τ

/-- One physical time-domain Lehmann transition, evaluated from the canonical transition
record. -/
noncomputable def eigenbasisTimeDomainTerm
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) (mn : ι × ι) : ℂ :=
  (eigenbasisTransitionData system data A B mn).timeTerm τ

/-- The canonical transition time term agrees with the operator-derived Heisenberg phase. -/
theorem eigenbasisTimeDomainTerm_eq_weight_mul_transitionPhase
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) (mn : ι × ι) :
    eigenbasisTimeDomainTerm system data A B τ mn =
      (eigenbasisTransitionData system data A B mn).weight *
        eigenbasisTransitionPhase system data mn.1 mn.2 τ := by
  simp [eigenbasisTimeDomainTerm, LehmannTransitionData.timeTerm,
    eigenbasisTransitionPhase_eq_exp_energyDifference]

/-- The countable time-domain eigenbasis Lehmann series. -/
noncomputable def eigenbasisTimeDomainSeries
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ) : ℂ :=
  ∑' mn : ι × ι, eigenbasisTimeDomainTerm system data A B τ mn

/-- Absolute summability of the forward weights is preserved by the unit transition phase. -/
theorem summable_eigenbasisForwardTimeTerm
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    Summable (eigenbasisForwardTimeTerm system data A B τ) := by
  apply hsum.1.of_norm_bounded
  intro mn
  simp [eigenbasisForwardTimeTerm]

/-- Absolute summability of the backward weights is preserved by the unit transition phase. -/
theorem summable_eigenbasisBackwardTimeTerm
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    Summable (eigenbasisBackwardTimeTerm system data A B τ) := by
  apply hsum.2.of_norm_bounded
  intro mn
  simp [eigenbasisBackwardTimeTerm]

/-- Expansion of `ω(A_I(τ) B)` into the forward ordered transition series. -/
theorem eigenbasisExpectation_heisenberg_mul_eq_tsum
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    eigenbasisNormalizedExpectation system data
        (heisenbergEvolution (freePropagatorGroup system) τ A * B) =
      ∑' mn : ι × ι,
        eigenbasisForwardTimeTerm system data A B τ mn := by
  rw [eigenbasisNormalizedExpectation_apply]
  have htime := summable_eigenbasisForwardTimeTerm system data A B τ hsum
  rw [htime.tsum_prod]
  apply tsum_congr
  intro m
  simp only [mul_apply_eq_comp]
  have hinner := data.basis.hasSum_inner_mul_inner
    (((heisenbergEvolution (freePropagatorGroup system) τ A)†) (data.basis m))
    (B (data.basis m))
  have hscaled := hinner.mul_left (data.probability m : ℂ)
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [← hscaled.tsum_eq]
  apply tsum_congr
  intro n
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [inner_energyEigenbasis_heisenbergEvolution system data A m n τ]
  simp [eigenbasisForwardTimeTerm, eigenbasisForwardWeight]
  ring

/-- Expansion of `ω(B A_I(τ))` into the backward ordered transition series. -/
theorem eigenbasisExpectation_mul_heisenberg_eq_tsum
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    eigenbasisNormalizedExpectation system data
        (B * heisenbergEvolution (freePropagatorGroup system) τ A) =
      ∑' mn : ι × ι,
        eigenbasisBackwardTimeTerm system data A B τ mn := by
  rw [eigenbasisNormalizedExpectation_apply]
  have htime := summable_eigenbasisBackwardTimeTerm system data A B τ hsum
  rw [htime.tsum_prod]
  apply tsum_congr
  intro m
  simp only [mul_apply_eq_comp]
  have hinner := data.basis.hasSum_inner_mul_inner
    ((B†) (data.basis m))
    (heisenbergEvolution (freePropagatorGroup system) τ A (data.basis m))
  have hscaled := hinner.mul_left (data.probability m : ℂ)
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [← hscaled.tsum_eq]
  apply tsum_congr
  intro n
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [inner_energyEigenbasis_heisenbergEvolution system data A n m τ]
  simp [eigenbasisBackwardTimeTerm, eigenbasisBackwardWeight]
  ring

/-- The two ordered transition sums combine into the physical `(pₘ - pₙ)` transition series. -/
theorem eigenbasis_forward_sub_backward_eq_timeDomainSeries
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    (Complex.I / (system.hbar : ℂ)) *
        ((∑' mn : ι × ι,
            eigenbasisForwardTimeTerm system data A B τ mn) -
          ∑' mn : ι × ι,
            eigenbasisBackwardTimeTerm system data A B τ mn) =
      eigenbasisTimeDomainSeries system data A B τ := by
  have hforward := summable_eigenbasisForwardTimeTerm system data A B τ hsum
  have hbackward := summable_eigenbasisBackwardTimeTerm system data A B τ hsum
  have hbackwardSwap : Summable fun mn : ι × ι =>
      eigenbasisBackwardTimeTerm system data A B τ mn.swap := by
    change Summable
      (eigenbasisBackwardTimeTerm system data A B τ ∘ Prod.swap)
    exact hbackward.comp_injective (Equiv.prodComm ι ι).injective
  have hswap :
      (∑' mn : ι × ι,
          eigenbasisBackwardTimeTerm system data A B τ mn) =
        ∑' mn : ι × ι,
          eigenbasisBackwardTimeTerm system data A B τ mn.swap := by
    symm
    simpa using (Equiv.prodComm ι ι).tsum_eq
      (eigenbasisBackwardTimeTerm system data A B τ)
  rw [hswap]
  rw [← hforward.tsum_sub hbackwardSwap]
  rw [← tsum_mul_left]
  rw [eigenbasisTimeDomainSeries]
  apply tsum_congr
  intro mn
  rw [eigenbasisTimeDomainTerm_eq_weight_mul_transitionPhase]
  simp [eigenbasisTransitionData,
    orderedLehmannTransitionWeight, eigenbasisForwardTimeTerm, eigenbasisForwardWeight,
    eigenbasisBackwardTimeTerm, eigenbasisBackwardWeight]
  ring

/-- The physical commutator susceptibility equals the countable time-domain Lehmann series. -/
theorem commutatorSusceptibility_eigenbasis_eq_timeDomainSeries
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (τ : ℝ)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    commutatorSusceptibility system
        (eigenbasisNormalizedExpectation system data) A B τ 0 =
      eigenbasisTimeDomainSeries system data A B τ := by
  rw [commutatorSusceptibility]
  simp only [heisenbergEvolution_zero, LieRing.of_associative_ring_bracket]
  rw [map_sub]
  rw [eigenbasisExpectation_heisenberg_mul_eq_tsum system data A B τ hsum]
  rw [eigenbasisExpectation_mul_heisenberg_eq_tsum system data A B τ hsum]
  exact eigenbasis_forward_sub_backward_eq_timeDomainSeries
    system data A B τ hsum

/-- On the causal half-line, the retarded kernel equals the countable eigenbasis transition
series. -/
theorem retardedTimeDifferenceKernel_eigenbasis_eq_timeDomainSeries_of_nonneg
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    retardedTimeDifferenceKernel system
        (eigenbasisNormalizedExpectation system data) A B τ =
      eigenbasisTimeDomainSeries system data A B τ := by
  rw [retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
    system (eigenbasisNormalizedExpectation system data) A B hτ]
  exact commutatorSusceptibility_eigenbasis_eq_timeDomainSeries
    system data A B τ hsum

/-- For a finite spectral index, the physical retarded kernel is the usual finite double
transition sum. -/
theorem retardedTimeDifferenceKernel_eigenbasis_eq_finite_sum_of_nonneg
    [Fintype ι] (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) {τ : ℝ} (hτ : 0 ≤ τ) :
    retardedTimeDifferenceKernel system
        (eigenbasisNormalizedExpectation system data) A B τ =
      ∑ mn : ι × ι,
        eigenbasisTimeDomainTerm system data A B τ mn := by
  rw [retardedTimeDifferenceKernel_eigenbasis_eq_timeDomainSeries_of_nonneg
    system data A B hτ
      (eigenbasisTimeDomainSummable_of_finite system data A B)]
  simp [eigenbasisTimeDomainSeries]

end
end LinearResponse
end QuantumTheory
