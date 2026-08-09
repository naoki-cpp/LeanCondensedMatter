import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram

set_option linter.style.header false

/-!
# Number-conserving quartic matching

A number-conserving quartic Wick pairing matches the `2 * n` creation legs bijectively with the
`2 * n` annihilation legs. This file extracts that bipartite matching as a permutation without
changing the stored `Pairing` representation yet.

The construction is intentionally minimal: it is the bridge needed to test whether the existing
fermionic crossing-parity sign machinery can be replaced by `Equiv.Perm.sign` with net code deletion.
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
annihilation leg and conversely. -/
def QuarticWickDiagram.HasNumberConservingPairing {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) : Prop :=
  (∀ i : Fin (2 * S.card), ∃ j : Fin (2 * S.card),
      d.pairing.partner (quarticCreatorLeg S.card i) = quarticAnnihilatorLeg S.card j) ∧
    (∀ j : Fin (2 * S.card), ∃ i : Fin (2 * S.card),
      d.pairing.partner (quarticAnnihilatorLeg S.card j) = quarticCreatorLeg S.card i)

private noncomputable def QuarticWickDiagram.matchingTo {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing)
    (i : Fin (2 * S.card)) : Fin (2 * S.card) :=
  Classical.choose (h.1 i)

private theorem QuarticWickDiagram.matchingTo_spec {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing)
    (i : Fin (2 * S.card)) :
    d.pairing.partner (quarticCreatorLeg S.card i) =
      quarticAnnihilatorLeg S.card (d.matchingTo h i) :=
  Classical.choose_spec (h.1 i)

private noncomputable def QuarticWickDiagram.matchingFrom {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing)
    (j : Fin (2 * S.card)) : Fin (2 * S.card) :=
  Classical.choose (h.2 j)

private theorem QuarticWickDiagram.matchingFrom_spec {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing)
    (j : Fin (2 * S.card)) :
    d.pairing.partner (quarticAnnihilatorLeg S.card j) =
      quarticCreatorLeg S.card (d.matchingFrom h j) :=
  Classical.choose_spec (h.2 j)

/-- The creator-to-annihilator matching permutation determined by a number-conserving quartic
pairing. -/
noncomputable def QuarticWickDiagram.matching {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing) :
    Equiv.Perm (Fin (2 * S.card)) where
  toFun := d.matchingTo h
  invFun := d.matchingFrom h
  left_inv i := by
    apply quarticCreatorLeg_injective S.card
    calc
      quarticCreatorLeg S.card (d.matchingFrom h (d.matchingTo h i)) =
          d.pairing.partner (quarticAnnihilatorLeg S.card (d.matchingTo h i)) :=
        (d.matchingFrom_spec h (d.matchingTo h i)).symm
      _ = d.pairing.partner (d.pairing.partner (quarticCreatorLeg S.card i)) := by
        rw [← d.matchingTo_spec h i]
      _ = quarticCreatorLeg S.card i := d.pairing.partner_partner _
  right_inv j := by
    apply quarticAnnihilatorLeg_injective S.card
    calc
      quarticAnnihilatorLeg S.card (d.matchingTo h (d.matchingFrom h j)) =
          d.pairing.partner (quarticCreatorLeg S.card (d.matchingFrom h j)) :=
        (d.matchingTo_spec h (d.matchingFrom h j)).symm
      _ = d.pairing.partner (d.pairing.partner (quarticAnnihilatorLeg S.card j)) := by
        rw [← d.matchingFrom_spec h j]
      _ = quarticAnnihilatorLeg S.card j := d.pairing.partner_partner _

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
