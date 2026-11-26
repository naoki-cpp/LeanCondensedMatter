import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity
import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffle
import Mathlib.Analysis.Complex.Basic
import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffleDecomposition
import LeanCondensedMatter.Combinatorics.Shuffle.FamilyOrderShuffle
import LeanCondensedMatter.Combinatorics.Shuffle.FinpartitionOrderShuffle

set_option linter.style.header false

/-!
# Finite-family and partition-order simplex shuffle identities

The binary ordered-simplex shuffle identity iterates over a finite family of ordered slot blocks.
The integrand layer below owns coordinate restriction, products of local integrands, continuity,
and measurable local boundedness for `FamilySlotShuffleTo`. The head-versus-tail decomposition of
`FamilySlotShuffle` then shows that the finite sum over all family shuffles equals the product
of the local ordered-simplex integrals.
-/

/-!
# Integrands associated with finite-family slot shuffles

Coordinate restriction, shuffled products, continuity, and measurable local boundedness belong to the
ordered-simplex analysis layer. The canonical integrand API is defined on `FamilySlotShuffleTo`,
with `FamilySlotShuffle` using it directly as the canonical-total abbreviation.
-/

namespace Combinatorics

variable {ι : Type*}

/-- Restrict an ambient assignment to one local block for a shuffle into an arbitrary ambient total. -/
def FamilySlotShuffleTo.timeAssignment {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) (τ : Fin total → ℝ) (i : ι) :
    Fin (size i) → ℝ :=
  fun j => τ (shuffle.slotEquiv ⟨i, j⟩)

@[simp]
theorem FamilySlotShuffleTo.timeAssignment_apply {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) (τ : Fin total → ℝ)
    (i : ι) (j : Fin (size i)) :
    shuffle.timeAssignment τ i j = τ (shuffle.slotEquiv ⟨i, j⟩) :=
  rfl

/-- Coordinate restriction to one local block is continuous. -/
private theorem FamilySlotShuffleTo.continuous_timeAssignment {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) (i : ι) :
    Continuous (fun τ : Fin total → ℝ => shuffle.timeAssignment τ i) := by
  exact continuous_pi fun j => continuous_apply (shuffle.slotEquiv ⟨i, j⟩)

variable [Fintype ι]

/-- Product of local integrands after embedding their coordinates into an arbitrary ambient total.
This is the `FamilySlotShuffleTo` form used when the ambient cardinality is only propositionally
equal to the sum of local block sizes. -/
noncomputable def FamilySlotShuffleTo.ambientIntegrand {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (τ : Fin total → ℝ) : ℂ :=
  ∏ i, localIntegrand i (shuffle.timeAssignment τ i)

/-- A finite product of continuous local integrands remains continuous after embedding their
coordinates by an arbitrary-total family shuffle. -/
theorem FamilySlotShuffleTo.continuous_ambientIntegrand {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, Continuous (localIntegrand i)) :
    Continuous (shuffle.ambientIntegrand localIntegrand) := by
  unfold FamilySlotShuffleTo.ambientIntegrand
  exact continuous_finsetProd _ fun i _ =>
    (hlocal i).comp (shuffle.continuous_timeAssignment i)

/-- A finite product of measurable locally bounded local integrands remains measurable locally
bounded after embedding their coordinates by an arbitrary-total family shuffle. -/
theorem FamilySlotShuffleTo.measurableLocallyBounded_ambientIntegrand
    {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, intervalIntegral.MeasurableLocallyBounded (localIntegrand i)) :
    intervalIntegral.MeasurableLocallyBounded (shuffle.ambientIntegrand localIntegrand) := by
  classical
  change intervalIntegral.MeasurableLocallyBounded
    (fun τ : Fin total → ℝ =>
      ∏ i, localIntegrand i (fun j => τ (shuffle.slotEquiv ⟨i, j⟩)))
  simpa using
    intervalIntegral.MeasurableLocallyBounded.finsetProd Finset.univ
      (fun i τ => localIntegrand i (fun j => τ (shuffle.slotEquiv ⟨i, j⟩)))
      (fun i _ => (hlocal i).comp_finCoordinateSelection
        (fun j => shuffle.slotEquiv ⟨i, j⟩))

end Combinatorics

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
        ((FamilySlotShuffle.cons size outer tail).ambientIntegrand localIntegrand) =
      orderedSimplexIntegral (size 0 + FamilySlotShuffle.tailTotal size) β
        (outer.integrand (localIntegrand 0)
          (tail.ambientIntegrand (fun i => localIntegrand i.succ))) := by
  rw [intervalIntegral.orderedSimplexIntegral_cast
    (Fin.sum_univ_succ size)]
  apply orderedSimplexIntegral_congr
  intro τ
  unfold FamilySlotShuffleTo.ambientIntegrand SlotShuffle.integrand
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
private theorem FamilySlotShuffle.sum_integral_eq_prod_fin :
    ∀ (k : ℕ) (size : Fin k → ℕ) (β : ℝ)
      (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ),
      (∀ i, MeasurableLocallyBounded (localIntegrand i)) →
      (∑ shuffle : FamilySlotShuffle size,
        orderedSimplexIntegral (∑ i, size i) β
          (shuffle.ambientIntegrand localIntegrand)) =
        ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i)
  | 0, size, β, localIntegrand, _ => by
      let h : (∑ i : Fin 0, size i) = 0 := by simp
      calc
        (∑ shuffle : FamilySlotShuffle size,
            orderedSimplexIntegral (∑ i, size i) β
              (shuffle.ambientIntegrand localIntegrand)) =
          orderedSimplexIntegral (∑ i, size i) β
            ((default : FamilySlotShuffle size).ambientIntegrand localIntegrand) := by simp
        _ = orderedSimplexIntegral 0 β (fun τ =>
              (default : FamilySlotShuffle size).ambientIntegrand localIntegrand
                (fun i => τ (Fin.cast h i))) :=
          intervalIntegral.orderedSimplexIntegral_cast h β
            ((default : FamilySlotShuffle size).ambientIntegrand localIntegrand)
        _ = 1 := by simp [FamilySlotShuffleTo.ambientIntegrand]
        _ = ∏ i : Fin 0, orderedSimplexIntegral (size i) β (localIntegrand i) := by simp
  | k + 1, size, β, localIntegrand, hlocal => by
      classical
      let tailIntegrand : ∀ i : Fin k, (Fin (FamilySlotShuffle.tailSize size i) → ℝ) → ℂ :=
        fun i => localIntegrand i.succ
      have htail : ∀ i, MeasurableLocallyBounded (tailIntegrand i) := fun i => hlocal i.succ
      have houter (tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size)) :
          (∑ outer : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size),
            orderedSimplexIntegral (size 0 + FamilySlotShuffle.tailTotal size) β
              (outer.integrand (localIntegrand 0) (tail.ambientIntegrand tailIntegrand))) =
            orderedSimplexIntegral (size 0) β (localIntegrand 0) *
              orderedSimplexIntegral (FamilySlotShuffle.tailTotal size) β
                (tail.ambientIntegrand tailIntegrand) :=
        BinaryShuffle.sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul_of_measurableLocallyBounded
          (size 0) (FamilySlotShuffle.tailTotal size) β
          (localIntegrand 0) (tail.ambientIntegrand tailIntegrand)
          (hlocal 0) (tail.measurableLocallyBounded_ambientIntegrand tailIntegrand htail)
      calc
        (∑ shuffle : FamilySlotShuffle size,
            orderedSimplexIntegral (∑ i, size i) β
              (shuffle.ambientIntegrand localIntegrand)) =
          ∑ p : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size) ×
              FamilySlotShuffle (FamilySlotShuffle.tailSize size),
            orderedSimplexIntegral (∑ i, size i) β
              ((FamilySlotShuffle.cons size p.1 p.2).ambientIntegrand localIntegrand) := by
                rw [← Equiv.sum_comp (FamilySlotShuffle.consEquiv size)]
                apply Finset.sum_congr rfl
                intro p _
                rfl
        _ = ∑ outer : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size),
              ∑ tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size),
                orderedSimplexIntegral (size 0 + FamilySlotShuffle.tailTotal size) β
                  (outer.integrand (localIntegrand 0) (tail.ambientIntegrand tailIntegrand)) := by
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
                  (outer.integrand (localIntegrand 0) (tail.ambientIntegrand tailIntegrand)) := by
                rw [Finset.sum_comm]
        _ = ∑ tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size),
              orderedSimplexIntegral (size 0) β (localIntegrand 0) *
                orderedSimplexIntegral (FamilySlotShuffle.tailTotal size) β
                  (tail.ambientIntegrand tailIntegrand) := by
                apply Finset.sum_congr rfl
                intro tail _
                exact houter tail
        _ = orderedSimplexIntegral (size 0) β (localIntegrand 0) *
              ∑ tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size),
                orderedSimplexIntegral (FamilySlotShuffle.tailTotal size) β
                  (tail.ambientIntegrand tailIntegrand) := by
                rw [Finset.mul_sum]
        _ = orderedSimplexIntegral (size 0) β (localIntegrand 0) *
              ∏ i : Fin k,
                orderedSimplexIntegral (FamilySlotShuffle.tailSize size i) β
                  (tailIntegrand i) := by
                rw [FamilySlotShuffle.sum_integral_eq_prod_fin
                  k (FamilySlotShuffle.tailSize size) β tailIntegrand htail]
        _ = ∏ i : Fin (k + 1),
              orderedSimplexIntegral (size i) β (localIntegrand i) := by
                rw [Fin.prod_univ_succ]


end Combinatorics

/-!
## Arbitrary finite index types

The recursive proof above is indexed by `Fin k`. The following transport makes the same shuffle
identity available directly for any finite component type without exposing that implementation
choice to consumers.
-/

namespace Combinatorics

open intervalIntegral

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable section

/-- Finite-family ordered-simplex shuffle product identity for an arbitrary finite block-index type,
under measurable local boundedness. -/
private theorem FamilySlotShuffle.sum_integral_eq_prod
    (size : ι → ℕ) (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, MeasurableLocallyBounded (localIntegrand i)) :
    (∑ shuffle : FamilySlotShuffle size,
      orderedSimplexIntegral (∑ i, size i) β (shuffle.ambientIntegrand localIntegrand)) =
      ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let sizeFin : Fin (Fintype.card ι) → ℕ := fun j => size (e j)
  let localFin : ∀ j, (Fin (sizeFin j) → ℝ) → ℂ := fun j => localIntegrand (e j)
  calc
    (∑ shuffle : FamilySlotShuffle size,
        orderedSimplexIntegral (∑ i, size i) β (shuffle.ambientIntegrand localIntegrand)) =
      ∑ shuffle : FamilySlotShuffle size,
        orderedSimplexIntegral (∑ j, sizeFin j) β
          ((FamilySlotShuffle.reindexEquiv e size shuffle).ambientIntegrand localFin) := by
            apply Fintype.sum_congr
            intro shuffle
            symm
            dsimp [sizeFin, localFin]
            let hsum : (∑ i : Fin (Fintype.card ι), size (e i)) = ∑ j : ι, size j :=
              Equiv.sum_comp e size
            rw [intervalIntegral.orderedSimplexIntegral_cast hsum]
            apply orderedSimplexIntegral_congr
            intro τ
            unfold FamilySlotShuffleTo.ambientIntegrand FamilySlotShuffleTo.timeAssignment
            have hterm : ∀ i : Fin (Fintype.card ι),
                localIntegrand (e i) (fun a =>
                  (fun z => τ (Fin.cast hsum z))
                    ((FamilySlotShuffle.reindexEquiv e size shuffle).slotEquiv ⟨i, a⟩)) =
                  localIntegrand (e i) (fun a => τ (shuffle.slotEquiv ⟨e i, a⟩)) := by
              intro i
              apply congrArg (localIntegrand (e i))
              funext a
              simp [FamilySlotShuffle.reindexEquiv]
            simp_rw [hterm]
            exact Equiv.prod_comp e
              (fun j => localIntegrand j (fun a => τ (shuffle.slotEquiv ⟨j, a⟩)))
    _ = ∑ shuffle : FamilySlotShuffle sizeFin,
        orderedSimplexIntegral (∑ j, sizeFin j) β (shuffle.ambientIntegrand localFin) :=
      Equiv.sum_comp (FamilySlotShuffle.reindexEquiv e size)
        (fun shuffle => orderedSimplexIntegral (∑ j, sizeFin j) β
          (shuffle.ambientIntegrand localFin))
    _ = ∏ j, orderedSimplexIntegral (sizeFin j) β (localFin j) :=
      FamilySlotShuffle.sum_integral_eq_prod_fin
        (Fintype.card ι) sizeFin β localFin (fun j => hlocal (e j))
    _ = ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) :=
      Equiv.prod_comp e (fun i => orderedSimplexIntegral (size i) β (localIntegrand i))

/-- Finite-family ordered-simplex shuffle product identity directly over an ambient total that is
propositionally equal to the sum of local block sizes. -/
theorem FamilySlotShuffleTo.sum_integral_eq_prod
    (size : ι → ℕ) (total : ℕ) (hTotal : (∑ i, size i) = total) (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, MeasurableLocallyBounded (localIntegrand i)) :
    (∑ shuffle : FamilySlotShuffleTo size total,
      orderedSimplexIntegral total β (shuffle.ambientIntegrand localIntegrand)) =
      ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) := by
  calc
    (∑ shuffle : FamilySlotShuffleTo size total,
        orderedSimplexIntegral total β (shuffle.ambientIntegrand localIntegrand)) =
      ∑ shuffle : FamilySlotShuffle size,
        orderedSimplexIntegral total β
          ((FamilySlotShuffleTo.castTotalEquiv hTotal shuffle).ambientIntegrand localIntegrand) :=
      (Equiv.sum_comp (FamilySlotShuffleTo.castTotalEquiv hTotal)
        (fun shuffle => orderedSimplexIntegral total β
          (shuffle.ambientIntegrand localIntegrand))).symm
    _ = ∑ shuffle : FamilySlotShuffle size,
        orderedSimplexIntegral (∑ i, size i) β (shuffle.ambientIntegrand localIntegrand) := by
      apply Fintype.sum_congr
      intro shuffle
      calc
        orderedSimplexIntegral total β
            ((FamilySlotShuffleTo.castTotalEquiv hTotal shuffle).ambientIntegrand localIntegrand) =
          orderedSimplexIntegral total β (fun τ =>
            shuffle.ambientIntegrand localIntegrand (fun j => τ (Fin.cast hTotal j))) := by
              apply orderedSimplexIntegral_congr
              intro τ
              unfold FamilySlotShuffleTo.ambientIntegrand
                FamilySlotShuffleTo.timeAssignment FamilySlotShuffleTo.castTotalEquiv
              rfl
        _ = orderedSimplexIntegral (∑ i, size i) β (shuffle.ambientIntegrand localIntegrand) := by
          symm
          exact intervalIntegral.orderedSimplexIntegral_cast hTotal β
            (shuffle.ambientIntegrand localIntegrand)
    _ = ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) :=
      FamilySlotShuffle.sum_integral_eq_prod
        size β localIntegrand hlocal

/-- The finite-family ordered-simplex integral product identity, indexed by
assignments of ambient interaction slots to blocks rather than by
order-preserving shuffles. The owner/shuffle equivalence ensures every
assignment with prescribed block sizes occurs once, including zero-size
blocks. This is an analytic bridge; identifying physical Wick-diagram
amplitudes with these local integrands is a separate step. -/
theorem FamilySlotShuffleTo.sum_fixedSizeOwner_integral_eq_prod
    (size : ι → ℕ) (total : ℕ)
    (hTotal : (∑ i, size i) = total) (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, MeasurableLocallyBounded (localIntegrand i)) :
    (∑ owner ∈ fixedSizeOwnerFiniteDomain
        (ι := ι) (size := size) (total := total),
      orderedSimplexIntegral total β
        ((familyShuffleOwnerEquiv.symm owner).ambientIntegrand localIntegrand)) =
      ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) := by
  classical
  calc
    (∑ owner ∈ fixedSizeOwnerFiniteDomain
        (ι := ι) (size := size) (total := total),
      orderedSimplexIntegral total β
        ((familyShuffleOwnerEquiv.symm owner).ambientIntegrand localIntegrand)) =
      ∑ shuffle : FamilySlotShuffleTo size total,
        orderedSimplexIntegral total β
          (shuffle.ambientIntegrand localIntegrand) := by
      exact (sum_familyShuffles_eq_sum_fixedSizeOwners
        (size := size) (total := total)
        (fun shuffle =>
          orderedSimplexIntegral total β
            (shuffle.ambientIntegrand localIntegrand))).symm
    _ = _ := FamilySlotShuffleTo.sum_integral_eq_prod
      size total hTotal β localIntegrand hlocal

end

end Combinatorics

/-!
## Ordered-simplex integral sums over finite-partition orders

A global order decomposes into part-local orders and an order-preserving shuffle.
When the global integrand agrees with the shuffled product of the local integrands,
summing its ordered-simplex integral over all global orders gives the product of
the corresponding local order sums. Regularity is required only of local integrands.
-/

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- Sum the ordered-simplex integrals over every order of a finite set by factoring
through a finite partition and its part-local order sums. -/
theorem sum_order_orderedSimplexIntegral_eq_prod_sum_partOrders
    (π : Finpartition s) (β : ℝ)
    (globalIntegrand : (Fin s.card ≃ ↥s) → (Fin s.card → ℝ) → ℂ)
    (localIntegrand : ∀ B : π.parts,
      (Fin (B : Finset α).card ≃ ↥(B : Finset α)) →
        (Fin (B : Finset α).card → ℝ) → ℂ)
    (hshuffle : ∀ (orders : π.PartOrders) (shuffle : π.PartShuffle),
      globalIntegrand (π.assembleOrder orders shuffle) =
        shuffle.ambientIntegrand (fun B => localIntegrand B (orders B)))
    (hlocal : ∀ B order, intervalIntegral.MeasurableLocallyBounded
      (localIntegrand B order)) :
    (∑ order : Fin s.card ≃ ↥s,
      intervalIntegral.orderedSimplexIntegral s.card β (globalIntegrand order)) =
      ∏ B : π.parts,
        ∑ order : Fin (B : Finset α).card ≃ ↥(B : Finset α),
          intervalIntegral.orderedSimplexIntegral (B : Finset α).card β
            (localIntegrand B order) := by
  classical
  have hcard : (∑ B : π.parts, (B : Finset α).card) = s.card := by
    rw [Finset.sum_coe_sort]
    exact π.sum_card_parts
  simpa only [one_mul] using
    (π.sum_order_eq_mul_prod_sum_partOrders
      (fun order => intervalIntegral.orderedSimplexIntegral s.card β (globalIntegrand order))
      (fun B order => intervalIntegral.orderedSimplexIntegral (B : Finset α).card β
        (localIntegrand B order))
      (1 : ℂ) (fun orders => by
        simp_rw [hshuffle orders]
        simpa only [one_mul] using
          Combinatorics.FamilySlotShuffleTo.sum_integral_eq_prod
            (fun B : π.parts => (B : Finset α).card) s.card hcard β
            (fun B => localIntegrand B (orders B))
            (fun B => hlocal B (orders B))))

end Finpartition
