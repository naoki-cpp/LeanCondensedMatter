import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity

set_option linter.style.header false

/-!
# Even mixed-time crossings between distinct components

For a full two-point quartic diagram, every vacuum interaction vertex contributes four consecutive
atomic legs in mixed-time order. Therefore the geometric crossing count between two distinct full
components is even. Combined with the generic component-crossing decomposition, this removes the
off-diagonal parity hypothesis from the statistics-weight factorization for any exchange statistics.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- Unoriented geometric crossing count between two mixed-time components. -/
private noncomputable def TwoPointDiagram.mixedComponentGeometricCrossingCount
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B C : d.vertexGraph.componentPartition.parts) : ℕ :=
  ∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
    if Crosses x.1.1.1 x.2.1.1 ∨ Crosses x.2.1.1 x.1.1.1 then 1 else 0

/-- Geometric crossings split into the two oriented component-crossing counts. -/
private theorem TwoPointDiagram.mixedComponentGeometricCrossingCount_eq_oriented_add
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B C : d.vertexGraph.componentPartition.parts) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C =
      d.mixedComponentOrientedCrossingCount τ τ' σ B C +
        d.mixedComponentOrientedCrossingCount τ τ' σ C B := by
  change
    (d.pairingInMixedOrder τ τ' σ).componentGeometricCrossingCount
        (Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)) B C =
      (d.pairingInMixedOrder τ τ' σ).componentCrossingCount
          (Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)) B C +
        (d.pairingInMixedOrder τ τ' σ).componentCrossingCount
          (Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)) C B
  exact
    (d.pairingInMixedOrder τ τ' σ).componentGeometricCrossingCount_eq_oriented_add
      (Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)) B C

private theorem TwoPointDiagram.mixedComponentPair_endpoints_ne
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C)
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
    TwoPointDiagram.mixedComponentPairEndpointInversionCount_mod_two_eq_indicator
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C)
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

private noncomputable def TwoPointDiagram.mixedComponentPositionInversionCount
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) : ℕ :=
  ∑ p : d.MixedComponentPosition τ τ' σ B,
    ∑ q : d.MixedComponentPosition τ τ' σ C,
      if q.1 < p.1 then 1 else 0

private theorem TwoPointDiagram.mixedComponentPairEndpointInversionCount_eq_sum
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts)
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
  have endpointVal (D : d.vertexGraph.componentPartition.parts)
      (r : d.MixedComponentPair τ τ' σ D) (k : Fin 2) :
      (d.mixedComponentPairEndpointEquiv τ τ' σ D (r, k)).1 =
        (d.pairingInMixedOrder τ τ' σ).pairEndpoint (r.1, k) := by
    unfold TwoPointDiagram.mixedComponentPairEndpointEquiv
    exact Pairing.normalizedPairSubtypeEndpointEquiv_apply_val
      (d.pairingInMixedOrder τ τ' σ)
      (fun x => d.mixedPositionComponent τ τ' σ x = D) _ r k
  rw [endpointVal C q b, endpointVal B p a]
  rfl

private theorem
    TwoPointDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_positionInversionCount
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C) :
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
            rw [TwoPointDiagram.mixedComponentPositionInversionCount,
              Fintype.sum_prod_type]
  calc
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 =
        (∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
          pairEndpointInversionCount x.1.1.1 x.2.1.1) % 2 := by
          symm
          simpa [Nat.ModEq, TwoPointDiagram.mixedComponentGeometricCrossingCount] using
            (Nat.ModEq.sum
              (n := 2)
              (s := (Finset.univ : Finset
                (d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C)))
              (f := fun x => pairEndpointInversionCount x.1.1.1 x.2.1.1)
              (g := fun x =>
                if Crosses x.1.1.1 x.2.1.1 ∨ Crosses x.2.1.1 x.1.1.1 then 1 else 0)
              (fun x _ => by
                change pairEndpointInversionCount x.1.1.1 x.2.1.1 % 2 =
                  (if Crosses x.1.1.1 x.2.1.1 ∨ Crosses x.2.1.1 x.1.1.1 then 1 else 0) % 2
                have h := d.mixedComponentPairEndpointInversionCount_mod_two_eq_indicator
                  τ τ' σ B C hBC x.1 x.2
                split_ifs at h ⊢ <;> simpa using h))
    _ = d.mixedComponentPositionInversionCount τ τ' σ B C % 2 := by rw [hpositions]

private noncomputable def TwoPointDiagram.mixedVacuumPositionDataEquiv
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.vertexGraph.componentPartition.parts) (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))) :
    d.MixedComponentPosition τ τ' σ C ≃
      ↥(interactionSector
        (C : Finset (TwoPointVertex
          (Finset.univ : Finset (Fin n))))) × Fin 4 :=
  (d.mixedVacuumPositionEquiv τ τ' σ C hVac).trans
    (quarticLegEquiv
      (interactionSector
        (C : Finset (TwoPointVertex
          (Finset.univ : Finset (Fin n))))))

private noncomputable def TwoPointDiagram.mixedVacuumInteractionPosition
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.vertexGraph.componentPartition.parts) (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))))
    (v : ↥(interactionSector
      (C : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.MixedComponentPosition τ τ' σ C :=
  (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).symm (v, l)

private theorem
    TwoPointDiagram.mixedComponentPositionInversionCount_eq_sum_vacuumBlocks
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))) :
    d.mixedComponentPositionInversionCount τ τ' σ B C =
      ∑ p : d.MixedComponentPosition τ τ' σ B,
        ∑ v : ↥(interactionSector
          (C : Finset (TwoPointVertex
            (Finset.univ : Finset (Fin n))))),
          ∑ l : Fin 4,
            if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1
            then 1 else 0 := by
  classical
  rw [TwoPointDiagram.mixedComponentPositionInversionCount]
  apply Finset.sum_congr rfl
  intro p _
  calc
    (∑ q : d.MixedComponentPosition τ τ' σ C,
        if q.1 < p.1 then 1 else 0) =
      ∑ x : ↥(interactionSector
          (C : Finset (TwoPointVertex
            (Finset.univ : Finset (Fin n))))) × Fin 4,
        if ((d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).symm x).1 < p.1
        then 1 else 0 :=
      (Equiv.sum_comp (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).symm
        (fun q => if q.1 < p.1 then 1 else 0)).symm
    _ = ∑ v : ↥(interactionSector
          (C : Finset (TwoPointVertex
            (Finset.univ : Finset (Fin n))))),
        ∑ l : Fin 4,
          if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1
          then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      rfl

private theorem
    TwoPointDiagram.mixedComponentPositionInversionCount_mod_two_eq_zero_of_vacuumBlockUniform
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))))
    (hUniform : ∀ p : d.MixedComponentPosition τ τ' σ B,
      ∀ v : ↥(interactionSector
        (C : Finset (TwoPointVertex
          (Finset.univ : Finset (Fin n))))), ∀ l : Fin 4,
        ((d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1) =
          ((d.mixedVacuumInteractionPosition τ τ' σ C hVac v 0).1 < p.1)) :
    d.mixedComponentPositionInversionCount τ τ' σ B C % 2 = 0 := by
  classical
  rw [d.mixedComponentPositionInversionCount_eq_sum_vacuumBlocks τ τ' σ B C hVac]
  apply Nat.mod_eq_zero_of_dvd
  refine Finset.dvd_sum fun p _ => ?_
  let V := ↥(interactionSector
    (C : Finset (TwoPointVertex
      (Finset.univ : Finset (Fin n)))))
  let f : V → ℕ := fun v =>
    if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v 0).1 < p.1 then 1 else 0
  change 2 ∣ ∑ v : V, ∑ l : Fin 4,
    if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1 then 1 else 0
  have hcount :
      (∑ v : V, ∑ l : Fin 4,
        if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1 then 1 else 0) =
        4 * ∑ v : V, f v := by
    calc
      (∑ v : V, ∑ l : Fin 4,
          if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1 then 1 else 0) =
          ∑ v : V, ∑ _l : Fin 4, f v := by
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro l _
        simp [f, hUniform p v l]
      _ = 4 * ∑ v : V, f v := by
        simpa [Fintype.sum_prod_type] using
          (Fintype.sum_equiv_fst_eq_card_mul_sum
            (e := Equiv.refl (V × Fin 4)) (f := f))
  rw [hcount]
  refine ⟨2 * ∑ v : V, f v, ?_⟩
  ring

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

private theorem TwoPointDiagram.mixedPositionComponent_interactionLegPosition
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.vertexGraph.componentPartition.parts)
    (v : ↥(interactionSector
      (C : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.mixedPositionComponent τ τ' σ
        (mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedInteractionLeg v.1 l)) = C := by
  rw [d.mixedPositionComponent_eq_iff_legInComponent,
    d.legInComponent_iff_unflattened,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]
  change (Sum.inr ⟨v.1, Finset.mem_univ v.1⟩ :
      TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
    (C : Finset (TwoPointVertex
      (Finset.univ : Finset (Fin n))))
  exact (mem_interactionSector_subtype
    (C : Finset (TwoPointVertex
      (Finset.univ : Finset (Fin n))))
    ⟨v.1, Finset.mem_univ v.1⟩).1 v.2

private noncomputable def TwoPointDiagram.directMixedVacuumInteractionPosition
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.vertexGraph.componentPartition.parts)
    (v : ↥(interactionSector
      (C : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.MixedComponentPosition τ τ' σ C :=
  ⟨mixedTimeOrderedAtomicLegPosition τ τ' σ
      (mixedTimeOrderedInteractionLeg v.1 l),
    d.mixedPositionComponent_interactionLegPosition τ τ' σ C v l⟩

private theorem TwoPointDiagram.mixedVacuumPositionDataEquiv_direct
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.vertexGraph.componentPartition.parts) (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))))
    (v : ↥(interactionSector
      (C : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.mixedVacuumPositionDataEquiv τ τ' σ C hVac
        (d.directMixedVacuumInteractionPosition τ τ' σ C v l) = (v, l) := by
  simp only [TwoPointDiagram.mixedVacuumPositionDataEquiv,
    TwoPointDiagram.mixedVacuumPositionEquiv,
    TwoPointDiagram.mixedComponentPositionEquiv,
    TwoPointDiagram.vacuumBlockLegEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  let leg :
      {leg : OrderedTwoPointLeg n // d.unflattenedLegInComponent C leg} :=
    ((twoPointLegEquiv (Finset.univ : Finset (Fin n))).subtypeEquiv
      (fun q => d.legInComponent_iff_unflattened C q))
      (((mixedTimeAmbientPositionEquiv τ τ' σ).subtypeEquiv
        (fun q => d.mixedPositionComponent_eq_iff_legInComponent τ τ' σ C q))
        (d.directMixedVacuumInteractionPosition τ τ' σ C v l))
  have hlegVal : leg.1 = mixedTimeOrderedInteractionLeg v.1 l := by
    change twoPointLegEquiv (Finset.univ : Finset (Fin n))
        (mixedTimeAmbientPositionEquiv τ τ' σ
          (mixedTimeOrderedAtomicLegPosition τ τ' σ
            (mixedTimeOrderedInteractionLeg v.1 l))) =
      mixedTimeOrderedInteractionLeg v.1 l
    rw [twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
      mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]
  have htarget : d.unflattenedLegInComponent C
      (mixedTimeOrderedInteractionLeg v.1 l) := by
    change (Sum.inr ⟨v.1, Finset.mem_univ v.1⟩ :
        TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
      (C : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n))))
    exact (mem_interactionSector_subtype
      (C : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n))))
      ⟨v.1, Finset.mem_univ v.1⟩).1 v.2
  have hleg : leg = ⟨mixedTimeOrderedInteractionLeg v.1 l, htarget⟩ :=
    Subtype.ext hlegVal
  change d.vacuumLegDataEquiv C hVac leg = (v, l)
  rw [hleg]
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

private theorem TwoPointDiagram.mixedVacuumInteractionPosition_eq_direct
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.vertexGraph.componentPartition.parts) (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))))
    (v : ↥(interactionSector
      (C : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.mixedVacuumInteractionPosition τ τ' σ C hVac v l =
      d.directMixedVacuumInteractionPosition τ τ' σ C v l := by
  apply (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).injective
  unfold TwoPointDiagram.mixedVacuumInteractionPosition
  rw [Equiv.apply_symm_apply,
    d.mixedVacuumPositionDataEquiv_direct τ τ' σ C hVac v l]

@[simp]
private theorem TwoPointDiagram.mixedVacuumInteractionPosition_val
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.vertexGraph.componentPartition.parts) (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))))
    (v : ↥(interactionSector
      (C : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 =
      mixedTimeOrderedAtomicLegPosition τ τ' σ
        (mixedTimeOrderedInteractionLeg v.1 l) := by
  rw [d.mixedVacuumInteractionPosition_eq_direct]
  rfl

private theorem
    TwoPointDiagram.mixedComponentPosition_leg_not_mem_interactionEventBlock
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C)
    (p : d.MixedComponentPosition τ τ' σ B)
    (v : ↥(interactionSector
      (C : Finset (TwoPointVertex
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

private theorem TwoPointDiagram.mixedVacuumInteractionPosition_lt_uniform
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C)
    (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))))
    (p : d.MixedComponentPosition τ τ' σ B)
    (v : ↥(interactionSector
      (C : Finset (TwoPointVertex
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
    TwoPointDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_vacuum
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C)
    (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0 := by
  rw [d.mixedComponentGeometricCrossingCount_mod_two_eq_positionInversionCount
    τ τ' σ B C hBC]
  exact d.mixedComponentPositionInversionCount_mod_two_eq_zero_of_vacuumBlockUniform
    τ τ' σ B C hVac
    (d.mixedVacuumInteractionPosition_lt_uniform τ τ' σ B C hBC hVac)

/-- For full quartic two-point diagrams, mixed-time pairing weights factor unconditionally into the
external component and all vacuum components, for arbitrary exchange statistics. -/
theorem TwoPointDiagram.pairingInMixedOrder_weight_eq_external_mul_prod_vacuum
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder τ τ' σ).weight s =
      d.mixedComponentWeight s τ τ' σ d.externalComponentPart *
        (vacuumComponentParts d.vertexGraph).prod
          (d.mixedComponentWeight s τ τ' σ) := by
  have hEven : ∀ B C : d.vertexGraph.componentPartition.parts, B ≠ C →
      d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0 := by
    intro B C hBC
    by_cases hC : C = d.externalComponentPart
    · have hB : B ≠ d.externalComponentPart := by
        intro h
        apply hBC
        exact h.trans hC.symm
      have hBVac : ComponentIsVacuum (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))) :=
        (d.componentIsVacuum_iff_ne_externalComponentPart B).2 hB
      have hcomm :
          d.mixedComponentGeometricCrossingCount τ τ' σ B C =
            d.mixedComponentGeometricCrossingCount τ τ' σ C B := by
        rw [d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ B C,
          d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ C B]
        omega
      rw [hcomm]
      exact d.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_vacuum
        τ τ' σ C B (Ne.symm hBC) hBVac
    · have hCVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))) :=
        (d.componentIsVacuum_iff_ne_externalComponentPart C).2 hC
      exact d.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_vacuum
        τ τ' σ B C hBC hCVac
  have hparity :
      (d.pairingInMixedOrder τ τ' σ).crossingCount % 2 =
        (∑ B : d.vertexGraph.componentPartition.parts,
          d.mixedComponentCrossingCount τ τ' σ B) % 2 :=
    Combinatorics.Pairing.crossingCount_mod_two_eq_sum_componentCrossingCount
      (d.pairingInMixedOrder τ τ' σ)
      (Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ))
      (fun B C hBC => by
        change (d.mixedComponentOrientedCrossingCount τ τ' σ B C +
          d.mixedComponentOrientedCrossingCount τ τ' σ C B) % 2 = 0
        rw [← d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ B C]
        exact hEven B C hBC)
  have hcomponents :
      (d.pairingInMixedOrder τ τ' σ).weight s =
        ∏ B : d.vertexGraph.componentPartition.parts, d.mixedComponentWeight s τ τ' σ B := by
    simpa only [Combinatorics.Pairing.weight, TwoPointDiagram.mixedComponentWeight] using
      BlochDeDominicis.zetaInt_pow_eq_prod_of_sum_mod_two_eq s
        (d.pairingInMixedOrder τ τ' σ).crossingCount
        (fun B : d.vertexGraph.componentPartition.parts => d.mixedComponentCrossingCount τ τ' σ B)
        hparity
  rw [hcomponents,
    d.prod_componentParts_eq_external_mul_prod_vacuum
      (d.mixedComponentWeight s τ τ' σ)]

end Common
end SecondQuantization
