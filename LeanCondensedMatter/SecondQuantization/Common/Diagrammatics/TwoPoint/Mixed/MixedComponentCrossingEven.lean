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

private noncomputable def TwoPointDiagram.mixedVacuumPositionDataEquiv
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.vertexGraph.componentPartition.parts) (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))) :
    d.MixedComponentPosition τ τ' σ C ≃
      ↥(interactionSector
        (C : Finset (TwoPointVertex
          (Finset.univ : Finset (Fin n))))) × Fin 4 :=
  ((d.mixedComponentPositionEquiv τ τ' σ C).trans
    ((twoPointLegEquiv (Finset.univ : Finset (Fin n))).subtypeEquiv
      (fun q => d.legInComponent_iff_unflattened C q))).trans
    (d.vacuumLegDataEquiv C hVac)

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

private theorem TwoPointDiagram.mixedVacuumInteractionPosition_val
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.vertexGraph.componentPartition.parts)
    (hVac : ComponentIsVacuum (C : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))))
    (v : ↥(interactionSector
      (C : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 =
      mixedTimeOrderedAtomicLegPosition τ τ' σ
        (mixedTimeOrderedInteractionLeg v.1 l) := by
  let direct : d.MixedComponentPosition τ τ' σ C :=
    ⟨mixedTimeOrderedAtomicLegPosition τ τ' σ
        (mixedTimeOrderedInteractionLeg v.1 l),
      d.mixedPositionComponent_interactionLegPosition τ τ' σ C v l⟩
  have hdata :
      d.mixedVacuumPositionDataEquiv τ τ' σ C hVac direct = (v, l) := by
    simp only [TwoPointDiagram.mixedVacuumPositionDataEquiv,
      TwoPointDiagram.mixedComponentPositionEquiv, Equiv.trans_apply]
    let leg :
        {leg : OrderedTwoPointLeg n // d.unflattenedLegInComponent C leg} :=
      ((twoPointLegEquiv (Finset.univ : Finset (Fin n))).subtypeEquiv
        (fun q => d.legInComponent_iff_unflattened C q))
        (((mixedTimeAmbientPositionEquiv τ τ' σ).subtypeEquiv
          (fun q => d.mixedPositionComponent_eq_iff_legInComponent τ τ' σ C q))
          direct)
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
  have hs :
      (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).symm (v, l) = direct := by
    apply (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).injective
    rw [Equiv.apply_symm_apply]
    exact hdata.symm
  exact congrArg Subtype.val hs

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
  rw [twoPointTimedEventAtomicLegs_interaction] at hmem
  simp only [List.mem_ofFn] at hmem
  obtain ⟨l, hl⟩ := hmem
  have hleg : mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 =
      mixedTimeOrderedInteractionLeg v.1 l := by
    simpa only [mixedTimeOrderedInteractionLeg] using hl.symm
  have hcomp := d.mixedPositionComponent_interactionLegPosition τ τ' σ C v l
  rw [← hleg, mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv] at hcomp
  exact hBC (p.2.symm.trans hcomp)

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
    (d.pairingInMixedOrder τ τ' σ).componentGeometricCrossingCount
        (Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)) B C % 2 = 0 := by
  classical
  have endpointVal (D : d.vertexGraph.componentPartition.parts)
      (p : d.MixedComponentPair τ τ' σ D) (k : Fin 2) :
      (d.mixedComponentPairEndpointEquiv τ τ' σ D (p, k)).1 =
        (d.pairingInMixedOrder τ τ' σ).pairEndpoint (p.1, k) := by
    unfold TwoPointDiagram.mixedComponentPairEndpointEquiv
    exact Pairing.normalizedPairSubtypeEndpointEquiv_apply_val
      (d.pairingInMixedOrder τ τ' σ)
      (fun x => d.mixedPositionComponent τ τ' σ x = D) _ p k
  have hcross :=
    Combinatorics.Pairing.componentGeometricCrossingCount_mod_two_eq_endpointInversionCount
      (d.pairingInMixedOrder τ τ' σ)
      (Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ))
      (fun D => d.mixedComponentPairEndpointEquiv τ τ' σ D)
      (fun _ p => p.1)
      (fun D p k => by
        simpa [Combinatorics.Pairing.pairEndpoint, Combinatorics.pairEndpointAt] using
          endpointVal D p k)
      B C hBC
  rw [hcross]
  apply Nat.mod_eq_zero_of_dvd
  refine Finset.dvd_sum fun p _ => ?_
  have hdiv := Fintype.dvd_sum_equiv_fst_of_dvd_card
    (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac)
    (fun v =>
      if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v 0).1 < p.1 then 1 else 0)
    (d := 2) (by decide)
  convert hdiv using 1
  apply Finset.sum_congr rfl
  intro q _
  let vl := d.mixedVacuumPositionDataEquiv τ τ' σ C hVac q
  have hq : d.mixedVacuumInteractionPosition τ τ' σ C hVac vl.1 vl.2 = q :=
    (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).symm_apply_apply q
  have huniform :=
    d.mixedVacuumInteractionPosition_lt_uniform τ τ' σ B C hBC hVac p vl.1 vl.2
  rw [hq] at huniform
  change (if q.1 < p.1 then (1 : ℕ) else 0) =
    (if (d.mixedVacuumInteractionPosition τ τ' σ C hVac vl.1 0).1 < p.1 then 1 else 0)
  by_cases h : q.1 < p.1
  · have h0 : (d.mixedVacuumInteractionPosition τ τ' σ C hVac vl.1 0).1 < p.1 :=
      huniform ▸ h
    simp [h, h0]
  · have h0 : ¬ (d.mixedVacuumInteractionPosition τ τ' σ C hVac vl.1 0).1 < p.1 := by
      intro hz
      exact h (huniform.symm ▸ hz)
    simp [h, h0]

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
  let pairing := d.pairingInMixedOrder τ τ' σ
  let components := Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)
  have hEven : ∀ B C : d.vertexGraph.componentPartition.parts, B ≠ C →
      pairing.componentGeometricCrossingCount components B C % 2 = 0 := by
    intro B C hBC
    by_cases hC : C = d.externalComponentPart
    · have hB : B ≠ d.externalComponentPart := by
        intro h
        apply hBC
        exact h.trans hC.symm
      have hBVac : ComponentIsVacuum (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))) :=
        (d.componentIsVacuum_iff_ne_externalComponentPart B).2 hB
      have hcomm :
          pairing.componentGeometricCrossingCount components B C =
            pairing.componentGeometricCrossingCount components C B := by
        rw [pairing.componentGeometricCrossingCount_eq_oriented_add components B C,
          pairing.componentGeometricCrossingCount_eq_oriented_add components C B]
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
        change (pairing.componentCrossingCount components B C +
          pairing.componentCrossingCount components C B) % 2 = 0
        rw [← pairing.componentGeometricCrossingCount_eq_oriented_add components B C]
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
