import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram

set_option linter.style.header false

/-!
# Number-conserving quartic matching

A number-conserving quartic Wick pairing matches the `2 * n` creation legs bijectively with the
`2 * n` annihilation legs. This file extracts that bipartite matching as a permutation without
changing the stored `Pairing` representation yet.
-/

namespace SecondQuantization
namespace Fermionic

/-- Flatten the two creation-leg slots of each quartic vertex into `Fin (2 * n)`. -/
noncomputable def quarticCreatorIndexEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n × Fin 2 :=
  (finCongr (by ring)).trans (finProdFinEquiv (m := n) (n := 2)).symm

/-- Embed a local creation-leg index into the fixed four-leg vertex convention. -/
def quarticCreatorLocalLeg (i : Fin 2) : Fin 4 :=
  ⟨i.val, by omega⟩

/-- Embed a local annihilation-leg index into the fixed four-leg vertex convention. -/
def quarticAnnihilatorLocalLeg (i : Fin 2) : Fin 4 :=
  ⟨i.val + 2, by omega⟩

/-- The global flattened quartic leg corresponding to a creation-leg index. -/
noncomputable def quarticCreatorLeg (n : ℕ) (i : Fin (2 * n)) : Fin (2 * (2 * n)) :=
  (Common.orderedQuarticLegEquiv n).symm
    ((quarticCreatorIndexEquiv n i).1,
      quarticCreatorLocalLeg (quarticCreatorIndexEquiv n i).2)

/-- The global flattened quartic leg corresponding to an annihilation-leg index. -/
noncomputable def quarticAnnihilatorLeg (n : ℕ) (i : Fin (2 * n)) : Fin (2 * (2 * n)) :=
  (Common.orderedQuarticLegEquiv n).symm
    ((quarticCreatorIndexEquiv n i).1,
      quarticAnnihilatorLocalLeg (quarticCreatorIndexEquiv n i).2)

private theorem quarticCreatorLocalLeg_injective : Function.Injective quarticCreatorLocalLeg := by
  intro i j h
  apply Fin.ext
  simpa [quarticCreatorLocalLeg] using congrArg (fun x : Fin 4 => x.val) h

private theorem quarticAnnihilatorLocalLeg_injective :
    Function.Injective quarticAnnihilatorLocalLeg := by
  intro i j h
  apply Fin.ext
  have hval := congrArg (fun x : Fin 4 => x.val) h
  simp only [quarticAnnihilatorLocalLeg] at hval
  omega

/-- Distinct creation indices give distinct flattened quartic legs. -/
theorem quarticCreatorLeg_injective (n : ℕ) : Function.Injective (quarticCreatorLeg n) := by
  intro i j h
  apply (quarticCreatorIndexEquiv n).injective
  have hcoords := congrArg (Common.orderedQuarticLegEquiv n) h
  simp only [quarticCreatorLeg, Equiv.apply_symm_apply] at hcoords
  apply Prod.ext
  · exact congrArg (fun x : Fin n × Fin 4 => x.1) hcoords
  · apply quarticCreatorLocalLeg_injective
    exact congrArg (fun x : Fin n × Fin 4 => x.2) hcoords

/-- Distinct annihilation indices give distinct flattened quartic legs. -/
theorem quarticAnnihilatorLeg_injective (n : ℕ) : Function.Injective (quarticAnnihilatorLeg n) := by
  intro i j h
  apply (quarticCreatorIndexEquiv n).injective
  have hcoords := congrArg (Common.orderedQuarticLegEquiv n) h
  simp only [quarticAnnihilatorLeg, Equiv.apply_symm_apply] at hcoords
  apply Prod.ext
  · exact congrArg (fun x : Fin n × Fin 4 => x.1) hcoords
  · apply quarticAnnihilatorLocalLeg_injective
    exact congrArg (fun x : Fin n × Fin 4 => x.2) hcoords

/-- A quartic Wick pairing is number-conserving when every creation leg is paired with an
annihilation leg. The converse follows automatically because both finite leg families have the same
cardinality and the pairing partner map is injective. -/
def QuarticWickDiagram.HasNumberConservingPairing {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) : Prop :=
  ∀ i : Fin (2 * S.card), ∃ j : Fin (2 * S.card),
    d.pairing.partner (quarticCreatorLeg S.card i) = quarticAnnihilatorLeg S.card j

private noncomputable def QuarticWickDiagram.matchingTo {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing)
    (i : Fin (2 * S.card)) : Fin (2 * S.card) :=
  Classical.choose (h i)

private theorem QuarticWickDiagram.matchingTo_spec {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing)
    (i : Fin (2 * S.card)) :
    d.pairing.partner (quarticCreatorLeg S.card i) =
      quarticAnnihilatorLeg S.card (d.matchingTo h i) :=
  Classical.choose_spec (h i)

private theorem QuarticWickDiagram.matchingTo_injective {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing) :
    Function.Injective (d.matchingTo h) := by
  intro i j hij
  apply quarticCreatorLeg_injective S.card
  apply d.pairing.partner.injective
  rw [d.matchingTo_spec h i, d.matchingTo_spec h j, hij]

/-- The creator-to-annihilator matching permutation determined by a number-conserving quartic
pairing. -/
noncomputable def QuarticWickDiagram.matching {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing) :
    Equiv.Perm (Fin (2 * S.card)) :=
  Equiv.ofBijective (d.matchingTo h) (d.matchingTo_injective h).bijective_of_finite

/-- Applying the extracted matching gives exactly the annihilation leg paired to a creator. -/
@[simp]
theorem QuarticWickDiagram.partner_creatorLeg_eq_annihilatorLeg_matching {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing)
    (i : Fin (2 * S.card)) :
    d.pairing.partner (quarticCreatorLeg S.card i) =
      quarticAnnihilatorLeg S.card (d.matching h i) :=
  d.matchingTo_spec h i

end Fermionic
end SecondQuantization
