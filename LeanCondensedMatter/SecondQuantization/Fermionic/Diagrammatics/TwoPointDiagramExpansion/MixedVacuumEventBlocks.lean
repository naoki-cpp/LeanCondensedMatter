import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossingParity

set_option linter.style.header false

/-!
# Four-leg event blocks in mixed-time vacuum components

Every vacuum component contains only quartic interaction vertices.  Its mixed-time position fiber is
therefore equivalent to an interaction vertex together with one of its four local legs.  This module
uses that equivalence to rewrite component-position inversion counts as sums over complete four-leg
blocks.

The final theorem isolates the remaining order-theoretic fact: for a position in a distinct
component, all four legs of one interaction event lie on the same side of that position.  Once this
block-uniformity statement is supplied, every block contributes either zero or four inversions and
the mixed geometric crossing count is even.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- Mixed positions of a vacuum component are exactly its interaction vertices together with their
four local legs. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedVacuumPositionDataEquiv
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

/-- The mixed atomic position of one local leg of a vacuum-component interaction vertex. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.MixedComponentPosition τ τ' σ C :=
  (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).symm (v, l)

/-- Reindex the position-inversion count against a vacuum component as a sum over complete
interaction-vertex four-leg blocks. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount_eq_sum_vacuumBlocks
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

/-- If every vacuum interaction block contributes an even number of comparisons, then the complete
component-position inversion count is even. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount_mod_two_eq_zero_of_vacuumBlocks
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (hBlock : ∀ p : d.MixedComponentPosition τ τ' σ B,
      ∀ v : ↥(Common.TwoPointDiagram.interactionPart
        (C : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n))))),
        (∑ l : Fin 4,
          if (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1
          then 1 else 0) % 2 = 0) :
    d.mixedComponentPositionInversionCount τ τ' σ B C % 2 = 0 := by
  rw [d.mixedComponentPositionInversionCount_eq_sum_vacuumBlocks τ τ' σ B C hVac]
  apply Nat.mod_eq_zero_of_dvd
  apply Finset.dvd_sum
  intro p _
  apply Finset.dvd_sum
  intro v _
  exact (Nat.dvd_iff_mod_eq_zero).2 (hBlock p v)

/-- Block-uniform ordering implies evenness: all four local legs of one interaction event contribute
identically against a fixed position in another component. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount_mod_two_eq_zero_of_vacuumBlockUniform
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
  apply d.mixedComponentPositionInversionCount_mod_two_eq_zero_of_vacuumBlocks
    τ τ' σ B C hVac
  intro p v
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
  rw [hsum]
  by_cases h0 : (d.mixedVacuumInteractionPosition τ τ' σ C hVac v 0).1 < p.1 <;>
    simp [h0]

/-- Under block-uniform ordering, the geometric crossing count against a distinct vacuum component
is even. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_vacuumBlockUniform
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (hVac : d.1.ComponentIsVacuum C)
    (hUniform : ∀ p : d.MixedComponentPosition τ τ' σ B,
      ∀ v : ↥(Common.TwoPointDiagram.interactionPart
        (C : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n))))), ∀ l : Fin 4,
        ((d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 < p.1) =
          ((d.mixedVacuumInteractionPosition τ τ' σ C hVac v 0).1 < p.1)) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0 := by
  apply d.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_positionInversionCount
    τ τ' σ B C hBC
  exact d.mixedComponentPositionInversionCount_mod_two_eq_zero_of_vacuumBlockUniform
    τ τ' σ B C hVac hUniform

end Fermionic
end SecondQuantization
