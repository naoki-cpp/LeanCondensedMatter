import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Bipartite

set_option linter.style.header false

/-!
# Number-conserving quartic matching structure

The four local quartic legs split canonically into the first two and last two slots.  This file
records that split and the corresponding bipartite-pairing/matching structure for an arbitrary
`QuarticDiagram`.

Nothing here depends on an operator realization, Gibbs state, exchange sign, or particle statistics.
Fermionic and bosonic specializations may assign creation/annihilation semantics to the two sides in
their own amplitude layers.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- Flatten the first two local-leg slots of each quartic vertex into `Fin (2 * n)`. -/
noncomputable def quarticCreatorIndexEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n × Fin 2 :=
  (finCongr (by ring)).trans (finProdFinEquiv (m := n) (n := 2)).symm

/-- Embed a local index into the first two slots of the fixed four-leg convention. -/
def quarticCreatorLocalLeg (i : Fin 2) : Fin 4 :=
  ⟨i.val, by omega⟩

/-- Embed a local index into the last two slots of the fixed four-leg convention. -/
def quarticAnnihilatorLocalLeg (i : Fin 2) : Fin 4 :=
  ⟨i.val + 2, by omega⟩

/-- The global flattened quartic leg corresponding to a first-side index. -/
noncomputable def quarticCreatorLeg (n : ℕ) (i : Fin (2 * n)) : Fin (2 * (2 * n)) :=
  (orderedQuarticLegEquiv n).symm
    ((quarticCreatorIndexEquiv n i).1,
      quarticCreatorLocalLeg (quarticCreatorIndexEquiv n i).2)

/-- The global flattened quartic leg corresponding to a second-side index. -/
noncomputable def quarticAnnihilatorLeg (n : ℕ) (i : Fin (2 * n)) : Fin (2 * (2 * n)) :=
  (orderedQuarticLegEquiv n).symm
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

/-- Distinct first-side indices give distinct flattened quartic legs. -/
theorem quarticCreatorLeg_injective (n : ℕ) : Function.Injective (quarticCreatorLeg n) := by
  intro i j h
  apply (quarticCreatorIndexEquiv n).injective
  have hcoords := congrArg (orderedQuarticLegEquiv n) h
  simp only [quarticCreatorLeg, Equiv.apply_symm_apply] at hcoords
  apply Prod.ext
  · exact congrArg (fun x : Fin n × Fin 4 => x.1) hcoords
  · apply quarticCreatorLocalLeg_injective
    exact congrArg (fun x : Fin n × Fin 4 => x.2) hcoords

/-- Distinct second-side indices give distinct flattened quartic legs. -/
theorem quarticAnnihilatorLeg_injective (n : ℕ) : Function.Injective (quarticAnnihilatorLeg n) := by
  intro i j h
  apply (quarticCreatorIndexEquiv n).injective
  have hcoords := congrArg (orderedQuarticLegEquiv n) h
  simp only [quarticAnnihilatorLeg, Equiv.apply_symm_apply] at hcoords
  apply Prod.ext
  · exact congrArg (fun x : Fin n × Fin 4 => x.1) hcoords
  · apply quarticAnnihilatorLocalLeg_injective
    exact congrArg (fun x : Fin n × Fin 4 => x.2) hcoords

/-- A first-side leg is never a second-side leg. -/
theorem quarticCreatorLeg_ne_quarticAnnihilatorLeg (n : ℕ) (i j : Fin (2 * n)) :
    quarticCreatorLeg n i ≠ quarticAnnihilatorLeg n j := by
  intro h
  have hcoord := congrArg (orderedQuarticLegEquiv n) h
  simp only [quarticCreatorLeg, quarticAnnihilatorLeg, Equiv.apply_symm_apply] at hcoord
  have hslot := congrArg (fun x : Fin n × Fin 4 => x.2.val) hcoord
  simp only [quarticCreatorLocalLeg, quarticAnnihilatorLocalLeg] at hslot
  have hlt := (quarticCreatorIndexEquiv n i).2.isLt
  omega

/-- The first two and last two local slots split the flattened quartic legs into two equal sides. -/
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

/-- A quartic diagram has a number-conserving pairing when every first-side leg is paired with a
second-side leg. The interpretation of the two sides as creation/annihilation is supplied by a
statistics-specific operator realization. -/
def QuarticDiagram.HasNumberConservingPairing {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) : Prop :=
  d.pairing.IsBipartite (quarticLegSideSplitting S.card)

/-- The side-to-side matching permutation determined by a number-conserving quartic pairing. -/
noncomputable def QuarticDiagram.matching {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (h : d.HasNumberConservingPairing) :
    Equiv.Perm (Fin (2 * S.card)) :=
  d.pairing.sideMatching (quarticLegSideSplitting S.card) h

/-- Applying the extracted matching gives exactly the second-side leg paired to a first-side leg. -/
@[simp]
theorem QuarticDiagram.partner_creatorLeg_eq_annihilatorLeg_matching {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (h : d.HasNumberConservingPairing)
    (i : Fin (2 * S.card)) :
    d.pairing.partner (quarticCreatorLeg S.card i) =
      quarticAnnihilatorLeg S.card (d.matching h i) :=
  d.pairing.partner_sideMatching (quarticLegSideSplitting S.card) h i

end Common
end SecondQuantization
