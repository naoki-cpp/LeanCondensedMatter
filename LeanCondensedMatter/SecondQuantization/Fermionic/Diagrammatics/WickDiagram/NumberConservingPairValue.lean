import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.NumberConservingMatching
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsGreenFunction

set_option linter.style.header false

/-!
# Anomalous quartic contractions vanish

A creation leg of a quartic vertex carries a creation operator, up to the scalar produced by the
free imaginary-time evolution. Two creation operators have vanishing free Gibbs expectation, so the
contraction of two creation legs is zero.

This is the physical selection rule behind number conservation. It supplies the left-left
vanishing hypothesis of `Combinatorics.pairingSum_eq_permutationSum_of_inl_vanishing`, which turns
the exchange-weighted pairing sum into a permutation sum without exposing a fermion-specific
determinant theorem in the combinatorics API.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] {N : ℕ}

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

variable [Fintype Mode]

/-- **Anomalous quartic contractions vanish.** Two creation legs contract to zero in the free Gibbs
state, by the particle-number selection rule: two creation operators change the particle number by
two while the state is diagonal in the occupation basis.

This is exactly the left-left vanishing input expected by the generic exchange-sum reduction for
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

/-- The vanishing rule in the side-splitting shape consumed by the generic exchange-sum endpoint. -/
theorem orderedQuarticPairValue_quarticLegSideSplitting_inl_inl (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S)
    (τ : Fin S.card → ℝ) (i i' : Fin (2 * S.card)) :
    orderedQuarticPairValue ε β d order τ
        (quarticLegSideSplitting S.card (Sum.inl i))
        (quarticLegSideSplitting S.card (Sum.inl i')) = 0 :=
  orderedQuarticPairValue_quarticCreatorLeg_quarticCreatorLeg ε β d order τ i i'

end Fermionic
end SecondQuantization
