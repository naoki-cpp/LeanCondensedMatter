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
theorem FamilySlotShuffle.sum_integral_eq_prod_fin :
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
                rw [FamilySlotShuffle.sum_integral_eq_prod_fin
                  k (FamilySlotShuffle.tailSize size) β tailIntegrand htail]
        _ = ∏ i : Fin (k + 1),
              orderedSimplexIntegral (size i) β (localIntegrand i) := by
                rw [Fin.prod_univ_succ]

/-- Finite-family ordered-simplex shuffle product identity for continuous local integrands. -/
theorem FamilySlotShuffle.sum_integral_eq_prod_fin_of_continuous
    (k : ℕ) (size : Fin k → ℕ) (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, Continuous (localIntegrand i)) :
    (∑ shuffle : FamilySlotShuffle size,
      orderedSimplexIntegral (∑ i, size i) β
        (shuffle.integrand localIntegrand)) =
      ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) :=
  FamilySlotShuffle.sum_integral_eq_prod_fin
    k size β localIntegrand (fun i => (hlocal i).measurableLocallyBounded)

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

private theorem sum_size_comp_equiv (e : ι ≃ κ) (size : κ → ℕ) :
    (∑ i : ι, size (e i)) = ∑ j : κ, size j :=
  Equiv.sum_comp e size

/-- Reindex family slot shuffles along an equivalence of their finite block-index types. -/
private noncomputable def reindexEquiv (e : ι ≃ κ) (size : κ → ℕ) :
    FamilySlotShuffle size ≃ FamilySlotShuffle (fun i => size (e i)) := by
  let hsum : (∑ i : ι, size (e i)) = ∑ j : κ, size j := sum_size_comp_equiv e size
  let localEquiv : (Σ i : ι, Fin (size (e i))) ≃ (Σ j : κ, Fin (size j)) :=
    e.sigmaCongrLeft (β := fun j : κ => Fin (size j))
  exact
    { toFun := fun shuffle =>
        { slotEquiv := localEquiv.trans (shuffle.slotEquiv.trans (finCongr hsum.symm))
          strictMono := by
            intro i a b hab
            change (finCongr hsum.symm)
                (shuffle.slotEquiv (localEquiv ⟨i, a⟩)) <
              (finCongr hsum.symm)
                (shuffle.slotEquiv (localEquiv ⟨i, b⟩))
            simpa [localEquiv] using
              (Fin.castOrderIso hsum.symm).strictMono
                (shuffle.strictMono (e i) hab) }
      invFun := fun shuffle =>
        { slotEquiv := localEquiv.symm.trans (shuffle.slotEquiv.trans (finCongr hsum))
          strictMono := by
            intro j
            obtain ⟨i, rfl⟩ := e.surjective j
            intro a b hab
            have ha : localEquiv.symm ⟨e i, a⟩ = ⟨i, a⟩ := by
              apply localEquiv.injective
              simp [localEquiv]
            have hb : localEquiv.symm ⟨e i, b⟩ = ⟨i, b⟩ := by
              apply localEquiv.injective
              simp [localEquiv]
            change (finCongr hsum)
                (shuffle.slotEquiv (localEquiv.symm ⟨e i, a⟩)) <
              (finCongr hsum)
                (shuffle.slotEquiv (localEquiv.symm ⟨e i, b⟩))
            rw [ha, hb]
            exact (Fin.castOrderIso hsum).strictMono
              (shuffle.strictMono i hab) }
      left_inv := by
        intro shuffle
        apply FamilySlotShuffle.ext
        apply Equiv.ext
        intro x
        change (finCongr hsum)
            ((finCongr hsum.symm)
              (shuffle.slotEquiv (localEquiv (localEquiv.symm x)))) =
          shuffle.slotEquiv x
        rw [localEquiv.apply_symm_apply]
        simp
      right_inv := by
        intro shuffle
        apply FamilySlotShuffle.ext
        apply Equiv.ext
        intro x
        change (finCongr hsum.symm)
            ((finCongr hsum)
              (shuffle.slotEquiv (localEquiv.symm (localEquiv x)))) =
          shuffle.slotEquiv x
        rw [localEquiv.symm_apply_apply]
        simp }

/-- Finite-family ordered-simplex shuffle product identity for an arbitrary finite block-index type,
under measurable local boundedness. -/
theorem FamilySlotShuffle.sum_integral_eq_prod
    (size : ι → ℕ) (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, MeasurableLocallyBounded (localIntegrand i)) :
    (∑ shuffle : FamilySlotShuffle size,
      orderedSimplexIntegral (∑ i, size i) β (shuffle.integrand localIntegrand)) =
      ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let sizeFin : Fin (Fintype.card ι) → ℕ := fun j => size (e j)
  let localFin : ∀ j, (Fin (sizeFin j) → ℝ) → ℂ := fun j => localIntegrand (e j)
  calc
    (∑ shuffle : FamilySlotShuffle size,
        orderedSimplexIntegral (∑ i, size i) β (shuffle.integrand localIntegrand)) =
      ∑ shuffle : FamilySlotShuffle size,
        orderedSimplexIntegral (∑ j, sizeFin j) β
          ((reindexEquiv e size shuffle).integrand localFin) := by
            apply Fintype.sum_congr
            intro shuffle
            symm
            dsimp [sizeFin, localFin]
            let hsum : (∑ i : Fin (Fintype.card ι), size (e i)) = ∑ j : ι, size j :=
              sum_size_comp_equiv e size
            rw [intervalIntegral.orderedSimplexIntegral_cast hsum]
            apply orderedSimplexIntegral_congr
            intro τ
            unfold FamilySlotShuffle.integrand FamilySlotShuffleTo.timeAssignment
            have hterm : ∀ i : Fin (Fintype.card ι),
                localIntegrand (e i) (fun a =>
                  (fun z => τ (Fin.cast hsum z))
                    ((reindexEquiv e size shuffle).slotEquiv ⟨i, a⟩)) =
                  localIntegrand (e i) (fun a => τ (shuffle.slotEquiv ⟨e i, a⟩)) := by
              intro i
              apply congrArg (localIntegrand (e i))
              funext a
              simp [reindexEquiv]
            simp_rw [hterm]
            exact Equiv.prod_comp e
              (fun j => localIntegrand j (fun a => τ (shuffle.slotEquiv ⟨j, a⟩)))
    _ = ∑ shuffle : FamilySlotShuffle sizeFin,
        orderedSimplexIntegral (∑ j, sizeFin j) β (shuffle.integrand localFin) :=
      Equiv.sum_comp (reindexEquiv e size)
        (fun shuffle => orderedSimplexIntegral (∑ j, sizeFin j) β
          (shuffle.integrand localFin))
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
        orderedSimplexIntegral (∑ i, size i) β (shuffle.integrand localIntegrand) := by
      apply Fintype.sum_congr
      intro shuffle
      calc
        orderedSimplexIntegral total β
            ((FamilySlotShuffleTo.castTotalEquiv hTotal shuffle).ambientIntegrand localIntegrand) =
          orderedSimplexIntegral total β (fun τ =>
            shuffle.integrand localIntegrand (fun j => τ (Fin.cast hTotal j))) := by
              apply orderedSimplexIntegral_congr
              intro τ
              unfold FamilySlotShuffleTo.ambientIntegrand FamilySlotShuffle.integrand
                FamilySlotShuffleTo.timeAssignment FamilySlotShuffleTo.castTotalEquiv
              rfl
        _ = orderedSimplexIntegral (∑ i, size i) β (shuffle.integrand localIntegrand) := by
          symm
          exact intervalIntegral.orderedSimplexIntegral_cast hTotal β
            (shuffle.integrand localIntegrand)
    _ = ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) :=
      FamilySlotShuffle.sum_integral_eq_prod
        size β localIntegrand hlocal

end

end Combinatorics
