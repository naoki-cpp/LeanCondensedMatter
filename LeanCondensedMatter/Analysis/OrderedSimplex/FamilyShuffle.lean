import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleIntegrand
import LeanCondensedMatter.Combinatorics.FamilySlotShuffleDecomposition

set_option linter.style.header false

/-!
# Finite-family ordered-simplex shuffle identity

The binary ordered-simplex shuffle identity iterates over a finite family of ordered slot blocks.
Using the head-versus-tail decomposition of `FamilySlotShuffle`, the finite sum over all family
shuffles equals the product of the local ordered-simplex integrals.
-/

namespace Combinatorics

open intervalIntegral
open BinaryShuffle

/-- The ordered-simplex term associated with a recursively constructed family shuffle is the binary
ambient-slot term whose right integrand is the shuffled tail-family integrand. -/
theorem FamilySlotShuffle.orderedSimplexIntegral_cons {k : ℕ}
    (size : Fin (k + 1) → ℕ)
    (outer : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size))
    (tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size))
    (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ) :
    orderedSimplexIntegral (∑ i, size i) β
        ((FamilySlotShuffle.cons size outer tail).integrand localIntegrand) =
      orderedSimplexIntegral (size 0 + FamilySlotShuffle.tailTotal size) β
        (outer.integrand (localIntegrand 0)
          (tail.integrand (fun i => localIntegrand i.succ))) := by
  rw [intervalIntegral.orderedSimplexIntegral_cast
    (FamilySlotShuffle.sum_eq_head_add_tail size)]
  apply orderedSimplexIntegral_congr
  intro τ
  unfold FamilySlotShuffle.integrand BinaryShuffle.SlotShuffle.integrand
  rw [Fin.prod_univ_succ]
  apply congrArg₂ (· * ·)
  · apply congrArg (localIntegrand 0)
    funext j
    simp [FamilySlotShuffleTo.timeAssignment]
  · apply congrArg (fun h : Fin k → ℂ => ∏ i, h i)
    funext i
    apply congrArg (localIntegrand i.succ)
    funext j
    simp [FamilySlotShuffleTo.timeAssignment]

/-- Finite-family ordered-simplex shuffle product identity under measurable local boundedness. -/
theorem FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_of_measurableLocallyBounded :
    ∀ (k : ℕ) (size : Fin k → ℕ) (β : ℝ)
      (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ),
      (∀ i, MeasurableLocallyBounded (localIntegrand i)) →
      (∑ shuffle : FamilySlotShuffle size,
        orderedSimplexIntegral (∑ i, size i) β
          (shuffle.integrand localIntegrand)) =
        ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i)
  | 0, size, β, localIntegrand, _ => by
      let h : (∑ i : Fin 0, size i) = 0 := by simp
      calc
        (∑ shuffle : FamilySlotShuffle size,
            orderedSimplexIntegral (∑ i, size i) β
              (shuffle.integrand localIntegrand)) =
          orderedSimplexIntegral (∑ i, size i) β
            ((default : FamilySlotShuffle size).integrand localIntegrand) := by simp
        _ = orderedSimplexIntegral 0 β (fun τ =>
              (default : FamilySlotShuffle size).integrand localIntegrand
                (fun i => τ (Fin.cast h i))) :=
          intervalIntegral.orderedSimplexIntegral_cast h β
            ((default : FamilySlotShuffle size).integrand localIntegrand)
        _ = 1 := by simp [FamilySlotShuffle.integrand]
        _ = ∏ i : Fin 0, orderedSimplexIntegral (size i) β (localIntegrand i) := by simp
  | k + 1, size, β, localIntegrand, hlocal => by
      classical
      let tailIntegrand : ∀ i : Fin k, (Fin (FamilySlotShuffle.tailSize size i) → ℝ) → ℂ :=
        fun i => localIntegrand i.succ
      have htail : ∀ i, MeasurableLocallyBounded (tailIntegrand i) := fun i => hlocal i.succ
      have houter (tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size)) :
          (∑ outer : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size),
            orderedSimplexIntegral (size 0 + FamilySlotShuffle.tailTotal size) β
              (outer.integrand (localIntegrand 0) (tail.integrand tailIntegrand))) =
            orderedSimplexIntegral (size 0) β (localIntegrand 0) *
              orderedSimplexIntegral (FamilySlotShuffle.tailTotal size) β
                (tail.integrand tailIntegrand) :=
        BinaryShuffle.sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul_of_measurableLocallyBounded
          (size 0) (FamilySlotShuffle.tailTotal size) β
          (localIntegrand 0) (tail.integrand tailIntegrand)
          (hlocal 0) (tail.measurableLocallyBounded_integrand tailIntegrand htail)
      calc
        (∑ shuffle : FamilySlotShuffle size,
            orderedSimplexIntegral (∑ i, size i) β
              (shuffle.integrand localIntegrand)) =
          ∑ p : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size) ×
              FamilySlotShuffle (FamilySlotShuffle.tailSize size),
            orderedSimplexIntegral (∑ i, size i) β
              ((FamilySlotShuffle.cons size p.1 p.2).integrand localIntegrand) := by
                rw [← Equiv.sum_comp (FamilySlotShuffle.consEquiv size)]
                apply Finset.sum_congr rfl
                intro p _
                rfl
        _ = ∑ outer : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size),
              ∑ tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size),
                orderedSimplexIntegral (size 0 + FamilySlotShuffle.tailTotal size) β
                  (outer.integrand (localIntegrand 0) (tail.integrand tailIntegrand)) := by
                rw [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro outer _
                apply Finset.sum_congr rfl
                intro tail _
                exact FamilySlotShuffle.orderedSimplexIntegral_cons
                  size outer tail β localIntegrand
        _ = ∑ tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size),
              ∑ outer : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size),
                orderedSimplexIntegral (size 0 + FamilySlotShuffle.tailTotal size) β
                  (outer.integrand (localIntegrand 0) (tail.integrand tailIntegrand)) := by
                rw [Finset.sum_comm]
        _ = ∑ tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size),
              orderedSimplexIntegral (size 0) β (localIntegrand 0) *
                orderedSimplexIntegral (FamilySlotShuffle.tailTotal size) β
                  (tail.integrand tailIntegrand) := by
                apply Finset.sum_congr rfl
                intro tail _
                exact houter tail
        _ = orderedSimplexIntegral (size 0) β (localIntegrand 0) *
              ∑ tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size),
                orderedSimplexIntegral (FamilySlotShuffle.tailTotal size) β
                  (tail.integrand tailIntegrand) := by
                rw [Finset.mul_sum]
        _ = orderedSimplexIntegral (size 0) β (localIntegrand 0) *
              ∏ i : Fin k,
                orderedSimplexIntegral (FamilySlotShuffle.tailSize size i) β
                  (tailIntegrand i) := by
                rw [FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_of_measurableLocallyBounded
                  k (FamilySlotShuffle.tailSize size) β tailIntegrand htail]
        _ = ∏ i : Fin (k + 1),
              orderedSimplexIntegral (size i) β (localIntegrand i) := by
                rw [Fin.prod_univ_succ]

/-- Finite-family ordered-simplex shuffle product identity for continuous local integrands. -/
theorem FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod
    (k : ℕ) (size : Fin k → ℕ) (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, Continuous (localIntegrand i)) :
    (∑ shuffle : FamilySlotShuffle size,
      orderedSimplexIntegral (∑ i, size i) β
        (shuffle.integrand localIntegrand)) =
      ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) :=
  FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_of_measurableLocallyBounded
    k size β localIntegrand (fun i => (hlocal i).measurableLocallyBounded)

end Combinatorics
