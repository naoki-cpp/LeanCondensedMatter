import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Bipartite

set_option linter.style.header false

/-!
# Number-conserving quartic matching

The creation and annihilation legs of a quartic diagram split its flattened legs into two labelled
sides of equal size. A number-conserving Wick pairing is exactly a pairing that matches the two
sides, so `Combinatorics.sidePairingEquiv` identifies such pairings with permutations of the
creation legs, without changing the stored `Pairing` representation.
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

/-- A creation leg is never an annihilation leg: their local slots lie on opposite sides of the
four-leg vertex convention. -/
theorem quarticCreatorLeg_ne_quarticAnnihilatorLeg (n : ℕ) (i j : Fin (2 * n)) :
    quarticCreatorLeg n i ≠ quarticAnnihilatorLeg n j := by
  intro h
  have hcoord := congrArg (Common.orderedQuarticLegEquiv n) h
  simp only [quarticCreatorLeg, quarticAnnihilatorLeg, Equiv.apply_symm_apply] at hcoord
  have hslot := congrArg (fun x : Fin n × Fin 4 => x.2.val) hcoord
  simp only [quarticCreatorLocalLeg, quarticAnnihilatorLocalLeg] at hslot
  have hlt := (quarticCreatorIndexEquiv n i).2.isLt
  omega

/-- **Creation and annihilation legs split the flattened quartic legs.** Every leg is either a
creation leg or an annihilation leg, and never both, so the two families label the two sides of the
ambient positions. -/
noncomputable def quarticLegSideSplitting (n : ℕ) : Combinatorics.SideSplitting (2 * n) :=
  Equiv.ofBijective (Sum.elim (quarticCreatorLeg n) (quarticAnnihilatorLeg n)) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) hij
      · exact congrArg Sum.inl (quarticCreatorLeg_injective n hij)
      · exact absurd hij (quarticCreatorLeg_ne_quarticAnnihilatorLeg n i j)
      · exact absurd hij.symm (quarticCreatorLeg_ne_quarticAnnihilatorLeg n j i)
      · exact congrArg Sum.inr (quarticAnnihilatorLeg_injective n hij)
    · simp only [Fintype.card_sum, Fintype.card_fin]
      omega

@[simp]
theorem quarticLegSideSplitting_inl (n : ℕ) (i : Fin (2 * n)) :
    quarticLegSideSplitting n (Sum.inl i) = quarticCreatorLeg n i :=
  rfl

@[simp]
theorem quarticLegSideSplitting_inr (n : ℕ) (j : Fin (2 * n)) :
    quarticLegSideSplitting n (Sum.inr j) = quarticAnnihilatorLeg n j :=
  rfl

/-- A quartic Wick pairing is number-conserving when every creation leg is paired with an
annihilation leg. -/
def QuarticWickDiagram.HasNumberConservingPairing {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) : Prop :=
  d.pairing.IsBipartite (quarticLegSideSplitting S.card)

/-- The creator-to-annihilator matching permutation determined by a number-conserving quartic
pairing. Through `Combinatorics.sidePairingEquiv` this correspondence is a bijection: the
number-conserving pairings of the quartic legs are exactly the permutations of the creation legs. -/
noncomputable def QuarticWickDiagram.matching {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing) :
    Equiv.Perm (Fin (2 * S.card)) :=
  d.pairing.sideMatching (quarticLegSideSplitting S.card) h

/-- Applying the extracted matching gives exactly the annihilation leg paired to a creator. -/
@[simp]
theorem QuarticWickDiagram.partner_creatorLeg_eq_annihilatorLeg_matching {Mode : Type*} {N : ℕ}
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (h : d.HasNumberConservingPairing)
    (i : Fin (2 * S.card)) :
    d.pairing.partner (quarticCreatorLeg S.card i) =
      quarticAnnihilatorLeg S.card (d.matching h i) :=
  d.pairing.partner_sideMatching (quarticLegSideSplitting S.card) h i

end Fermionic
end SecondQuantization
