import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedOrderPairing

set_option linter.style.header false

/-!
# Even mixed-time crossings between distinct components

`MixedComponentCrossing.lean` factors the mixed-order pairing weight over full diagram components
under the hypothesis that off-diagonal geometric crossing counts are even. This module discharges
that hypothesis.

Two mixed pairs from distinct components have disjoint endpoints, so their crossing parity is the
parity of the four endpoint comparisons; reindexing all pair endpoints turns the off-diagonal
crossing parity into the number of mixed positions of one component lying before positions of the
other. A vacuum component consists of quartic interaction vertices only, each contributing four
consecutive atomic legs to the mixed-time flattened list, and a position of a distinct component
lies outside that event block. Every vacuum block therefore contributes zero or four inversions,
which makes the count even and removes the parity hypothesis.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*}

private theorem FixedExternalTwoPointWickDiagram.mixedComponentPair_endpoints_ne
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (p : d.MixedComponentPair τ τ' σ B)
    (q : d.MixedComponentPair τ τ' σ C) :
    p.1.1.1 ≠ q.1.1.1 ∧
      p.1.1.1 ≠ q.1.1.2 ∧
      p.1.1.2 ≠ q.1.1.1 ∧
      p.1.1.2 ≠ q.1.1.2 := by
  refine (d.pairingInMixedOrder τ τ' σ).normalizedPair_endpoints_ne_of_ne p.1 q.1 ?_
  intro hpq
  apply hBC
  calc
    B = d.mixedPairComponent τ τ' σ p.1 := p.2.symm
    _ = d.mixedPairComponent τ τ' σ q.1 := congrArg _ hpq
    _ = C := q.2

private theorem
    FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointInversionCount_mod_two_eq_indicator
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (p : d.MixedComponentPair τ τ' σ B)
    (q : d.MixedComponentPair τ τ' σ C) :
    pairEndpointInversionCount p.1.1 q.1.1 % 2 =
      if Crosses p.1.1 q.1.1 ∨ Crosses q.1.1 p.1.1 then 1 else 0 := by
  have hEnds := d.mixedComponentPair_endpoints_ne τ τ' σ B C hBC p q
  exact pairEndpointInversionCount_mod_two_eq_crossesIndicator
    p.1.1 q.1.1
    ((d.pairingInMixedOrder τ τ' σ).pairs_normalized p.1.2)
    ((d.pairingInMixedOrder τ τ' σ).pairs_normalized q.1.2)
    hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2

private noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) : ℕ :=
  ∑ p : d.MixedComponentPosition τ τ' σ B,
    ∑ q : d.MixedComponentPosition τ τ' σ C,
      if q.1 < p.1 then 1 else 0

private theorem FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointEquiv_val
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPair τ τ' σ B) (k : Fin 2) :
    (d.mixedComponentPairEndpointEquiv τ τ' σ B (p, k)).1 =
      pairEndpointAt p.1.1 k := by
  rfl

private theorem FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointInversionCount_eq_sum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts)
    (p : d.MixedComponentPair τ τ' σ B)
    (q : d.MixedComponentPair τ τ' σ C) :
    pairEndpointInversionCount p.1.1 q.1.1 =
      ∑ a : Fin 2, ∑ b : Fin 2,
        if (d.mixedComponentPairEndpointEquiv τ τ' σ C (q, b)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (p, a)).1
        then 1 else 0 := by
  rw [pairEndpointInversionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [d.mixedComponentPairEndpointEquiv_val, d.mixedComponentPairEndpointEquiv_val]

private theorem
    FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_positionInversionCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 =
      d.mixedComponentPositionInversionCount τ τ' σ B C % 2 := by
  classical
  let endpointPairEquiv :
      ((d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C) ×
          (Fin 2 × Fin 2)) ≃
        (d.MixedComponentPosition τ τ' σ B ×
          d.MixedComponentPosition τ τ' σ C) :=
    (Equiv.prodProdProdComm _ _ _ _).trans
      (Equiv.prodCongr
        (d.mixedComponentPairEndpointEquiv τ τ' σ B)
        (d.mixedComponentPairEndpointEquiv τ τ' σ C))
  have hpositions :
      (∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
        pairEndpointInversionCount x.1.1.1 x.2.1.1) =
        d.mixedComponentPositionInversionCount τ τ' σ B C := by
    calc
      (∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
          pairEndpointInversionCount x.1.1.1 x.2.1.1) =
        ∑ x : (d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C) ×
            (Fin 2 × Fin 2),
          if (d.mixedComponentPairEndpointEquiv τ τ' σ C (x.1.2, x.2.2)).1 <
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (x.1.1, x.2.1)).1
          then 1 else 0 := by
            simp only [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro q _
            exact d.mixedComponentPairEndpointInversionCount_eq_sum τ τ' σ B C p q
      _ = ∑ x : d.MixedComponentPosition τ τ' σ B ×
            d.MixedComponentPosition τ τ' σ C,
          if x.2.1 < x.1.1 then 1 else 0 := by
            refine Fintype.sum_equiv endpointPairEquiv
              (fun x =>
                if (d.mixedComponentPairEndpointEquiv τ τ' σ C (x.1.2, x.2.2)).1 <
                  (d.mixedComponentPairEndpointEquiv τ τ' σ B (x.1.1, x.2.1)).1
                then 1 else 0)
              (fun x => if x.2.1 < x.1.1 then 1 else 0) ?_
            intro x
            rfl
      _ = d.mixedComponentPositionInversionCount τ τ' σ B C := by
            rw [FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount,
              Fintype.sum_prod_type]
  calc
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 =
        (∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
          pairEndpointInversionCount x.1.1.1 x.2.1.1) % 2 := by
          symm
          exact fintype_sum_mod_two_congr _ _ fun x => by
            have h := d.mixedComponentPairEndpointInversionCount_mod_two_eq_indicator
              τ τ' σ B C hBC x.1 x.2
            split_ifs at h ⊢ <;> simpa using h
    _ = d.mixedComponentPositionInversionCount τ τ' σ B C % 2 := by rw [hpositions]

private noncomputable def FixedExternalTwoPointWickDiagram.mixedVacuumPositionDataEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C) :
    d.MixedComponentPosition τ τ' σ C ≃
      ↥(Common.TwoPointDiagram.interactionPart
        (C : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n))))) × Fin 4 :=
  (d.mixedVacuumPositionEquiv τ τ' σ C hVac).trans
    (Common.quarticLegEquiv
      (Common.TwoPointDiagram.interactionPart
        (C : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n))))))

private noncomputable def FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.MixedComponentPosition τ τ' σ C :=
  (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).symm (v, l)

private theorem
    FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount_eq_sum_vacuumBlocks
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C) :
    d.mixedComponentPositionInversionCount τ τ' σ B C =
      ∑ p : d.MixedComponentPosition τ τ' σ B,
        ∑ v : ↥(Common.TwoPointDiagram.interactionPart
          (C : Finset (Common.TwoPointVertex
            (Finset.univ : Finset (Fin n))))),
          ∑ l : Fin 4,
            if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1
            then 1 else 0 := by
  classical
  rw [FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount]
  apply Finset.sum_congr rfl
  intro p _
  calc
    (∑ q : d.MixedComponentPosition τ τ' σ C,
        if q.1 < p.1 then 1 else 0) =
      ∑ x : ↥(Common.TwoPointDiagram.interactionPart
          (C : Finset (Common.TwoPointVertex
            (Finset.univ : Finset (Fin n))))) × Fin 4,
        if ((d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).symm x).1 < p.1
        then 1 else 0 :=
      (Equiv.sum_comp (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).symm
        (fun q => if q.1 < p.1 then 1 else 0)).symm
    _ = ∑ v : ↥(Common.TwoPointDiagram.interactionPart
          (C : Finset (Common.TwoPointVertex
            (Finset.univ : Finset (Fin n))))),
        ∑ l : Fin 4,
          if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1
          then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      rfl

private theorem
    FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount_mod_two_eq_zero_of_vacuumBlockUniform
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (hUniform : ∀ p : d.MixedComponentPosition τ τ' σ B,
      ∀ v : ↥(Common.TwoPointDiagram.interactionPart
        (C : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n))))), ∀ l : Fin 4,
        ((d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1) =
          ((d.mixedVacuumInteractionPosition τ τ' σ C hVac v 0).1 < p.1)) :
    d.mixedComponentPositionInversionCount τ τ' σ B C % 2 = 0 := by
  classical
  rw [d.mixedComponentPositionInversionCount_eq_sum_vacuumBlocks τ τ' σ B C hVac]
  apply Nat.mod_eq_zero_of_dvd
  refine Finset.dvd_sum fun p _ => ?_
  refine Finset.dvd_sum fun v _ => ?_
  have hsum :
      (∑ l : Fin 4,
        if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1
        then 1 else 0) =
      ∑ _l : Fin 4,
        if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v 0).1 < p.1
        then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases h0 : (d.mixedVacuumInteractionPosition τ τ' σ C hVac v 0).1 < p.1
    · have hl : (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1 := by
        simpa [h0] using hUniform p v l
      simp [h0, hl]
    · have hl : ¬ (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1 := by
        simpa [h0] using hUniform p v l
      simp [h0, hl]
  rw [hsum, Fin.sum_univ_four]
  split_ifs <;> omega

private def mixedTimeOrderedInteractionLeg {n : ℕ} (v : Fin n) (l : Fin 4) :
    OrderedTwoPointLeg n :=
  Sum.inr (⟨v, Finset.mem_univ v⟩, l)

private theorem mixedTimeOrderedInteractionLeg_mem_eventBlock {n : ℕ}
    (v : Fin n) (l : Fin 4) :
    mixedTimeOrderedInteractionLeg v l ∈
      twoPointTimedEventAtomicLegs (Sum.inr v : TwoPointTimedEvent n) := by
  fin_cases l <;>
    simp [mixedTimeOrderedInteractionLeg, twoPointTimedEventAtomicLegs]

private theorem interactionEvent_mem_orderedTwoPointTimedEvents {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (v : Fin n) :
    (Sum.inr v : TwoPointTimedEvent n) ∈ orderedTwoPointTimedEvents τ τ' σ := by
  exact (orderedTwoPointTimedEvents_perm τ τ' σ).symm.subset (by
    simp [twoPointInteractionEventList])

private theorem FixedExternalTwoPointWickDiagram.mixedPositionComponent_interactionLegPosition
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.mixedPositionComponent τ τ' σ
        (mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedInteractionLeg v.1 l)) = C := by
  rw [d.mixedPositionComponent_eq_iff_legInComponent,
    d.1.legInComponent_iff_unflattened,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]
  change (Sum.inr ⟨v.1, Finset.mem_univ v.1⟩ :
      Common.TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
    (C : Finset (Common.TwoPointVertex
      (Finset.univ : Finset (Fin n))))
  exact (Common.TwoPointDiagram.mem_interactionPart_subtype
    (C : Finset (Common.TwoPointVertex
      (Finset.univ : Finset (Fin n))))
    ⟨v.1, Finset.mem_univ v.1⟩).1 v.2

private noncomputable def FixedExternalTwoPointWickDiagram.directMixedVacuumInteractionPosition
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.MixedComponentPosition τ τ' σ C :=
  ⟨mixedTimeOrderedAtomicLegPosition τ τ' σ
      (mixedTimeOrderedInteractionLeg v.1 l),
    d.mixedPositionComponent_interactionLegPosition τ τ' σ C v l⟩

private theorem FixedExternalTwoPointWickDiagram.mixedVacuumPositionDataEquiv_direct
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.mixedVacuumPositionDataEquiv τ τ' σ C hVac
        (d.directMixedVacuumInteractionPosition τ τ' σ C v l) = (v, l) := by
  simp only [FixedExternalTwoPointWickDiagram.mixedVacuumPositionDataEquiv,
    FixedExternalTwoPointWickDiagram.mixedVacuumPositionEquiv,
    FixedExternalTwoPointWickDiagram.mixedComponentPositionEquiv,
    Common.TwoPointDiagram.vacuumBlockLegEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  let leg :
      {leg : OrderedTwoPointLeg n // d.1.unflattenedLegInComponent C leg} :=
    ((Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).subtypeEquiv
      (fun q => d.1.legInComponent_iff_unflattened C q))
      (((mixedTimeAmbientPositionEquiv τ τ' σ).subtypeEquiv
        (fun q => d.mixedPositionComponent_eq_iff_legInComponent τ τ' σ C q))
        (d.directMixedVacuumInteractionPosition τ τ' σ C v l))
  have hlegVal : leg.1 = mixedTimeOrderedInteractionLeg v.1 l := by
    change Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
        (mixedTimeAmbientPositionEquiv τ τ' σ
          (mixedTimeOrderedAtomicLegPosition τ τ' σ
            (mixedTimeOrderedInteractionLeg v.1 l))) =
      mixedTimeOrderedInteractionLeg v.1 l
    rw [twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
      mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]
  have htarget : d.1.unflattenedLegInComponent C
      (mixedTimeOrderedInteractionLeg v.1 l) := by
    change (Sum.inr ⟨v.1, Finset.mem_univ v.1⟩ :
        Common.TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n))))
    exact (Common.TwoPointDiagram.mem_interactionPart_subtype
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n))))
      ⟨v.1, Finset.mem_univ v.1⟩).1 v.2
  have hleg : leg = ⟨mixedTimeOrderedInteractionLeg v.1 l, htarget⟩ :=
    Subtype.ext hlegVal
  change d.1.vacuumLegDataEquiv C hVac leg = (v, l)
  rw [hleg]
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

private theorem FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition_eq_direct
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.mixedVacuumInteractionPosition τ τ' σ C hVac v l =
      d.directMixedVacuumInteractionPosition τ τ' σ C v l := by
  apply (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).injective
  unfold FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition
  rw [Equiv.apply_symm_apply,
    d.mixedVacuumPositionDataEquiv_direct τ τ' σ C hVac v l]

@[simp]
private theorem FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition_val
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 =
      mixedTimeOrderedAtomicLegPosition τ τ' σ
        (mixedTimeOrderedInteractionLeg v.1 l) := by
  rw [d.mixedVacuumInteractionPosition_eq_direct]
  rfl

private theorem
    FixedExternalTwoPointWickDiagram.mixedComponentPosition_leg_not_mem_interactionEventBlock
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (p : d.MixedComponentPosition τ τ' σ B)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) :
    mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 ∉
      twoPointTimedEventAtomicLegs (Sum.inr v.1 : TwoPointTimedEvent n) := by
  intro hmem
  have hpos :
      mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) = p.1 :=
    mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1
  have hcontr (l : Fin 4)
      (hleg : mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 =
        mixedTimeOrderedInteractionLeg v.1 l) : False := by
    have hcomp : d.mixedPositionComponent τ τ' σ p.1 = C := by
      calc
        d.mixedPositionComponent τ τ' σ p.1 =
            d.mixedPositionComponent τ τ' σ
              (mixedTimeOrderedAtomicLegPosition τ τ' σ
                (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1)) := by rw [hpos]
        _ = d.mixedPositionComponent τ τ' σ
              (mixedTimeOrderedAtomicLegPosition τ τ' σ
                (mixedTimeOrderedInteractionLeg v.1 l)) := by rw [hleg]
        _ = C := d.mixedPositionComponent_interactionLegPosition τ τ' σ C v l
    exact hBC (p.2.symm.trans hcomp)
  rw [twoPointTimedEventAtomicLegs_interaction] at hmem
  simp only [List.mem_ofFn] at hmem
  rcases hmem with ⟨l, hleg⟩
  apply hcontr l
  simpa only [mixedTimeOrderedInteractionLeg] using hleg.symm

private theorem FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition_lt_uniform
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (hVac : d.1.ComponentIsVacuum C)
    (p : d.MixedComponentPosition τ τ' σ B)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    ((d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1) =
      ((d.mixedVacuumInteractionPosition τ τ' σ C hVac v 0).1 < p.1) := by
  let z := mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1
  have h := mixedTimeOrderedAtomicLegPosition_lt_uniform τ τ' σ
    (Sum.inr v.1 : TwoPointTimedEvent n)
    (mixedTimeOrderedInteractionLeg v.1 l)
    (mixedTimeOrderedInteractionLeg v.1 0) z
    (interactionEvent_mem_orderedTwoPointTimedEvents τ τ' σ v.1)
    (mixedTimeOrderedInteractionLeg_mem_eventBlock v.1 l)
    (mixedTimeOrderedInteractionLeg_mem_eventBlock v.1 0)
    (mixedTimeOrderedAtomicLegs_all_mem τ τ' σ z)
    (d.mixedComponentPosition_leg_not_mem_interactionEventBlock
      τ τ' σ B C hBC p v)
  simpa [z, d.mixedVacuumInteractionPosition_val] using h

private theorem
    FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (hVac : d.1.ComponentIsVacuum C) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0 := by
  rw [d.mixedComponentGeometricCrossingCount_mod_two_eq_positionInversionCount
    τ τ' σ B C hBC]
  exact d.mixedComponentPositionInversionCount_mod_two_eq_zero_of_vacuumBlockUniform
    τ τ' σ B C hVac
    (d.mixedVacuumInteractionPosition_lt_uniform τ τ' σ B C hBC hVac)

private theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_comm
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C =
      d.mixedComponentGeometricCrossingCount τ τ' σ C B := by
  rw [d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ B C,
    d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ C B]
  omega

private theorem
    FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_zero
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0 := by
  by_cases hC : C = d.1.externalComponentPart
  · have hB : B ≠ d.1.externalComponentPart := by
      intro h
      apply hBC
      exact h.trans hC.symm
    have hBVac : d.1.ComponentIsVacuum B :=
      (d.1.componentIsVacuum_iff_ne_externalComponentPart B).2 hB
    rw [d.mixedComponentGeometricCrossingCount_comm τ τ' σ B C]
    exact d.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_vacuum
      τ τ' σ C B (Ne.symm hBC) hBVac
  · have hCVac : d.1.ComponentIsVacuum C :=
      (d.1.componentIsVacuum_iff_ne_externalComponentPart C).2 hC
    exact d.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_vacuum
      τ τ' σ B C hBC hCVac

theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_weight_eq_prod_components_unconditional
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder τ τ' σ).weight s =
      ∏ B : d.1.componentPartition.parts,
        d.mixedComponentWeight s τ τ' σ B :=
  d.pairingInMixedOrder_weight_eq_prod_components s τ τ' σ
    (d.mixedComponentGeometricCrossingCount_mod_two_eq_zero τ τ' σ)

theorem
    FixedExternalTwoPointWickDiagram.pairingInMixedOrder_weight_eq_external_mul_prod_vacuum_unconditional
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder τ τ' σ).weight s =
      d.mixedComponentWeight s τ τ' σ d.1.externalComponentPart *
        d.1.vacuumComponentParts.prod
          (d.mixedComponentWeight s τ τ' σ) := by
  rw [d.pairingInMixedOrder_weight_eq_prod_components_unconditional s τ τ' σ,
    d.prod_mixedComponentWeight_eq_external_mul_prod_vacuum s τ τ' σ]

end Fermionic
end SecondQuantization
