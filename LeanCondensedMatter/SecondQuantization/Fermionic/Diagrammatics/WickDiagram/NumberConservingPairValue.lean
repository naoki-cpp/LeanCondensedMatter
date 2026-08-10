import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.NumberConservingMatching
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsGreenFunction

set_option linter.style.header false

/-!
# Anomalous quartic contractions vanish

A creation leg of a quartic vertex carries a creation operator, up to the scalar produced by the
free imaginary-time evolution. Two creation operators have vanishing free Gibbs expectation, so the
contraction of two creation legs is zero.

This is the physical selection rule behind number conservation: it is the hypothesis of
`Combinatorics.sum_pairings_eq_det`, and it is what makes a quartic Wick pairing a matching of
creation legs to annihilation legs, hence a permutation.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- A creator slot of a quartic vertex carries a creation operator. -/
theorem exists_quarticLocalLegOperator_quarticCreatorLocalLeg
    (q : Common.QuarticVertexLabel Mode) (s : Fin 2) :
    ∃ mo : Mode, quarticLocalLegOperator q (quarticCreatorLocalLeg s) = create mo := by
  fin_cases s
  · exact ⟨q.create₁, rfl⟩
  · exact ⟨q.create₂, rfl⟩

/-- The time-evolved operator at a flattened creation leg is a scalar multiple of a creation
operator: the local leg is a creation operator and the free evolution only rescales it. -/
theorem exists_orderedQuarticLegOperator_quarticCreatorLeg (ε : Mode → ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S)
    (τ : Fin S.card → ℝ) (i : Fin (2 * S.card)) :
    ∃ (c : ℂ) (mo : Mode),
      orderedQuarticLegOperator ε d order τ (quarticCreatorLeg S.card i) = c • create mo := by
  obtain ⟨mo, hmo⟩ := exists_quarticLocalLegOperator_quarticCreatorLocalLeg
    (d.vertexLabel (order (quarticCreatorIndexEquiv S.card i).1))
    (quarticCreatorIndexEquiv S.card i).2
  refine ⟨Complex.exp (((τ (quarticCreatorIndexEquiv S.card i).1 : ℝ) : ℂ) * (ε mo : ℂ)), mo, ?_⟩
  simp only [orderedQuarticLegOperator, quarticLegOperatorForSequence, quarticCreatorLeg,
    Equiv.apply_symm_apply]
  rw [hmo, imaginaryTimeEvolve_create]

/-- **Anomalous quartic contractions vanish.** Two creation legs contract to zero in the free Gibbs
state, by the particle-number selection rule: two creation operators change the particle number by
two while the state is diagonal in the occupation basis.

This is exactly the hypothesis `Combinatorics.sum_pairings_eq_det` needs for the side splitting
`quarticLegSideSplitting`. -/
theorem orderedQuarticPairValue_quarticCreatorLeg_quarticCreatorLeg (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S)
    (τ : Fin S.card → ℝ) (i i' : Fin (2 * S.card)) :
    orderedQuarticPairValue ε β d order τ
      (quarticCreatorLeg S.card i) (quarticCreatorLeg S.card i') = 0 := by
  obtain ⟨c, mo, hc⟩ := exists_orderedQuarticLegOperator_quarticCreatorLeg ε d order τ i
  obtain ⟨c', mo', hc'⟩ := exists_orderedQuarticLegOperator_quarticCreatorLeg ε d order τ i'
  rw [orderedQuarticPairValue, hc, hc', LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
    Common.finiteHilbertOperator_smul, map_smul, smul_eq_mul,
    freeGibbsDensityOperator_expectation_create_comp_create, mul_zero]

/-- The vanishing rule, in the form taken by the left-side hypothesis of
`Combinatorics.sum_pairings_eq_det` for the quartic leg splitting. -/
theorem orderedQuarticPairValue_quarticLegSideSplitting_inl_inl (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S)
    (τ : Fin S.card → ℝ) (i i' : Fin (2 * S.card)) :
    orderedQuarticPairValue ε β d order τ
        (quarticLegSideSplitting S.card (Sum.inl i))
        (quarticLegSideSplitting S.card (Sum.inl i')) = 0 :=
  orderedQuarticPairValue_quarticCreatorLeg_quarticCreatorLeg ε β d order τ i i'

end Fermionic
end SecondQuantization
