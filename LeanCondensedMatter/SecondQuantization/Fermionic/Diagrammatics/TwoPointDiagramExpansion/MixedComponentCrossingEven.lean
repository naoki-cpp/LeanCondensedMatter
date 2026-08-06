import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedVacuumEventBlockOrder

set_option linter.style.header false

/-!
# Even mixed-time crossings between distinct components

A quartic interaction event contributes four consecutive atomic legs to the mixed-time flattened
list.  A position belonging to a distinct full diagram component lies outside that event block, so
all four local legs have the same order comparison with it.  Each vacuum interaction block therefore
contributes either zero or four endpoint inversions.

This proves that the geometric crossing count between any two distinct full components is even and
removes the parity hypothesis from the component factorization of the mixed pairing weight.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- The atomic leg identity of a mixed position in one component cannot lie in an interaction-event
block belonging to a distinct component. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPosition_leg_not_mem_interactionEventBlock
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

/-- All four local legs of one vacuum interaction event have the same comparison with a position in
a distinct component. -/
theorem FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition_lt_uniform
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

/-- Geometric crossings with a distinct vacuum component are even. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (hVac : d.1.ComponentIsVacuum C) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0 := by
  exact d.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_vacuumBlockUniform
    τ τ' σ B C hBC hVac
    (d.mixedVacuumInteractionPosition_lt_uniform τ τ' σ B C hBC hVac)

/-- The mixed geometric crossing count is symmetric in its two component arguments. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_comm
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C =
      d.mixedComponentGeometricCrossingCount τ τ' σ C B := by
  rw [d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ B C,
    d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ C B]
  omega

/-- Geometric crossings between any two distinct full components are even. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_zero
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

/-- The global mixed-order exchange-statistics weight factors over all full components without an
additional parity hypothesis. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_weight_eq_prod_components_unconditional
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder τ τ' σ).weight s =
      ∏ B : d.1.componentPartition.parts,
        d.mixedComponentWeight s τ τ' σ B :=
  d.pairingInMixedOrder_weight_eq_prod_components s τ τ' σ
    (d.mixedComponentGeometricCrossingCount_mod_two_eq_zero τ τ' σ)

/-- Unconditional external/vacuum factorization of the global mixed-order pairing weight. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_weight_eq_external_mul_prod_vacuum_unconditional
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
