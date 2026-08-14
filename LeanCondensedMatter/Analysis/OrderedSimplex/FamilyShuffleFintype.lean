import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle

set_option linter.style.header false

/-!
# Finite-index transport for family ordered-simplex shuffles

The recursive family-shuffle proof is naturally indexed by `Fin k`.  Public consumers, however,
should be able to use any finite component type directly.  This file transports the `Fin k` theorem
along `Fintype.equivFin`, keeping the recursive proof itself unchanged.
-/

namespace Combinatorics

open intervalIntegral

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable section

private theorem sum_size_comp_equiv (e : ι ≃ κ) (size : κ → ℕ) :
    (∑ i : ι, size (e i)) = ∑ j : κ, size j :=
  Equiv.sum_comp e size

/-- Reindex family slot shuffles along an equivalence of their finite block-index types. -/
noncomputable def FamilySlotShuffle.reindexEquiv (e : ι ≃ κ) (size : κ → ℕ) :
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

/-- One reindexed family-shuffle term has the same ordered-simplex integral as the original term. -/
theorem FamilySlotShuffle.orderedSimplexIntegral_reindexEquiv
    (e : ι ≃ κ) (size : κ → ℕ) (shuffle : FamilySlotShuffle size)
    (β : ℝ) (localIntegrand : ∀ j, (Fin (size j) → ℝ) → ℂ) :
    orderedSimplexIntegral (∑ i : ι, size (e i)) β
        ((FamilySlotShuffle.reindexEquiv e size shuffle).integrand
          (fun i => localIntegrand (e i))) =
      orderedSimplexIntegral (∑ j : κ, size j) β
        (shuffle.integrand localIntegrand) := by
  let hsum : (∑ i : ι, size (e i)) = ∑ j : κ, size j := sum_size_comp_equiv e size
  rw [intervalIntegral.orderedSimplexIntegral_cast hsum]
  apply orderedSimplexIntegral_congr
  intro τ
  unfold FamilySlotShuffle.integrand FamilySlotShuffle.timeAssignment
  have hterm : ∀ i : ι,
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

/-- Finite-family ordered-simplex shuffle product identity for an arbitrary finite block-index type,
under measurable local boundedness. -/
theorem FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_fintype_of_measurableLocallyBounded
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
          ((FamilySlotShuffle.reindexEquiv e size shuffle).integrand localFin) := by
            apply Fintype.sum_congr
            intro shuffle
            exact (FamilySlotShuffle.orderedSimplexIntegral_reindexEquiv
              e size shuffle β localIntegrand).symm
    _ = ∑ shuffle : FamilySlotShuffle sizeFin,
        orderedSimplexIntegral (∑ j, sizeFin j) β (shuffle.integrand localFin) :=
      Equiv.sum_comp (FamilySlotShuffle.reindexEquiv e size)
        (fun shuffle => orderedSimplexIntegral (∑ j, sizeFin j) β
          (shuffle.integrand localFin))
    _ = ∏ j, orderedSimplexIntegral (sizeFin j) β (localFin j) :=
      FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_of_measurableLocallyBounded
        (Fintype.card ι) sizeFin β localFin (fun j => hlocal (e j))
    _ = ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) :=
      Equiv.prod_comp e (fun i => orderedSimplexIntegral (size i) β (localIntegrand i))

/-- Transporting a canonical family shuffle to a propositionally equal ambient total preserves its
ordered-simplex term. -/
theorem FamilySlotShuffleTo.orderedSimplexIntegral_ambientIntegrand_castTotalEquiv
    (size : ι → ℕ) (total : ℕ) (hTotal : (∑ i, size i) = total)
    (shuffle : FamilySlotShuffle size) (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ) :
    orderedSimplexIntegral total β
        ((FamilySlotShuffleTo.castTotalEquiv hTotal shuffle).ambientIntegrand localIntegrand) =
      orderedSimplexIntegral (∑ i, size i) β (shuffle.integrand localIntegrand) := by
  calc
    orderedSimplexIntegral total β
        ((FamilySlotShuffleTo.castTotalEquiv hTotal shuffle).ambientIntegrand localIntegrand) =
      orderedSimplexIntegral total β (fun τ =>
        shuffle.integrand localIntegrand (fun j => τ (Fin.cast hTotal j))) := by
          apply orderedSimplexIntegral_congr
          intro τ
          unfold FamilySlotShuffleTo.ambientIntegrand FamilySlotShuffle.integrand
            FamilySlotShuffle.timeAssignment FamilySlotShuffleTo.castTotalEquiv
          rfl
    _ = orderedSimplexIntegral (∑ i, size i) β (shuffle.integrand localIntegrand) := by
      symm
      exact intervalIntegral.orderedSimplexIntegral_cast hTotal β
        (shuffle.integrand localIntegrand)

/-- Finite-family ordered-simplex shuffle product identity directly over an ambient total that is
propositionally equal to the sum of local block sizes. -/
theorem FamilySlotShuffleTo.sum_orderedSimplexIntegral_ambientIntegrand_eq_prod_fintype_of_measurableLocallyBounded
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
      exact FamilySlotShuffleTo.orderedSimplexIntegral_ambientIntegrand_castTotalEquiv
        size total hTotal shuffle β localIntegrand
    _ = ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) :=
      FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_fintype_of_measurableLocallyBounded
        size β localIntegrand hlocal

/-- Finite-family ordered-simplex shuffle product identity for continuous local integrands over an
arbitrary finite block-index type. -/
theorem FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_fintype
    (size : ι → ℕ) (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, Continuous (localIntegrand i)) :
    (∑ shuffle : FamilySlotShuffle size,
      orderedSimplexIntegral (∑ i, size i) β (shuffle.integrand localIntegrand)) =
      ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) :=
  FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_fintype_of_measurableLocallyBounded
    size β localIntegrand (fun i => (hlocal i).measurableLocallyBounded)

/-- Finite-family ordered-simplex shuffle product identity for continuous local integrands directly
over an ambient total propositionally equal to the sum of local block sizes. -/
theorem FamilySlotShuffleTo.sum_orderedSimplexIntegral_ambientIntegrand_eq_prod_fintype
    (size : ι → ℕ) (total : ℕ) (hTotal : (∑ i, size i) = total) (β : ℝ)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, Continuous (localIntegrand i)) :
    (∑ shuffle : FamilySlotShuffleTo size total,
      orderedSimplexIntegral total β (shuffle.ambientIntegrand localIntegrand)) =
      ∏ i, orderedSimplexIntegral (size i) β (localIntegrand i) :=
  FamilySlotShuffleTo.sum_orderedSimplexIntegral_ambientIntegrand_eq_prod_fintype_of_measurableLocallyBounded
    size total hTotal β localIntegrand (fun i => (hlocal i).measurableLocallyBounded)

end

end Combinatorics
