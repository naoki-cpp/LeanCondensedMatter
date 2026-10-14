import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumAmplitude
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.SlotCongr

set_option linter.style.header false

/-!
# Canonical support coordinates for external/vacuum splitting

The support-side local mixed-to-fixed map should agree with the canonical
mixed-time permutation of a standalone external-insertion diagram indexed
by the increasing enumeration of the supported interaction slots.
-/

namespace SecondQuantization
namespace Fermionic

open Common

/-- In increasing support-slot coordinates, the external sector's mixed-to-fixed
position map is the inverse of the standard standalone mixed-time permutation. -/
theorem externalInsertionLeftMixedToFixedEquiv_eq_standardMixedPosition_symm
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    externalInsertionLeftMixedToFixedEquiv T externalTime σ =
      (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm := by
  classical
  let supportFixed :
      OrderedExternalInsertionLeg E T.card ≃ Fin (2 * (2 * T.card + E)) :=
    ((Equiv.sumCongr (Equiv.refl (Fin (2 * E)))
      (((Equiv.subtypeUnivEquiv (fun i : Fin T.card => Finset.mem_univ i)).trans
        (T.orderIsoOfFin rfl).toEquiv).prodCongr (Equiv.refl (Fin 4)))).trans
      (externalInsertionLegEquiv E T).symm)
  let standardFixed :
      OrderedExternalInsertionLeg E T.card ≃ Fin (2 * (2 * T.card + E)) :=
    (externalInsertionLegEquiv E (Finset.univ : Finset (Fin T.card))).symm.trans
      (finCongr (by simp))
  have hfixed : supportFixed = standardFixed := by
    apply Equiv.ext
    intro leg
    cases leg with
    | inl e =>
        apply Fin.ext
        change (externalInsertionExternalLeg E T e).val =
          (Fin.cast (by simp)
            (externalInsertionExternalLeg E
              (Finset.univ : Finset (Fin T.card)) e)).val
        simp only [Fin.val_cast, externalInsertionExternalLeg_val]
    | inr vl =>
        rcases vl with ⟨v, l⟩
        apply Fin.ext
        change (externalInsertionInteractionLeg (E := E)
            (T.orderIsoOfFin rfl v.1) l).val =
          (Fin.cast (by simp)
            (externalInsertionInteractionLeg (E := E) v l)).val
        simp only [Fin.val_cast, externalInsertionInteractionLeg_val]
        have huniv :
            (((Finset.univ : Finset (Fin T.card)).orderIsoOfFin rfl).symm v).val =
              v.1.val := by
          rw [Finset.orderIsoOfFin_symm_apply, Fin.sort_univ, List.idxOf_finRange]
        have hT :
            (((T.orderIsoOfFin rfl).symm (T.orderIsoOfFin rfl v.1)).val) =
              v.1.val := by
          simp
        rw [huniv, hT]
  apply Equiv.ext
  intro p
  change supportFixed
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1) p) =
    standardFixed
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1) p)
  rw [hfixed]


/-- The external-sector sign left after cancelling the ambient/vacuum crossing
parity is exactly the standalone mixed-time ordering sign, even when the
supported interaction slots are not consecutive. -/
theorem externalInsertionLeftMixedSign_eq_standalone
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ((Equiv.Perm.sign
        (Equiv.sumCongr (externalInsertionLeftMixedToFixedEquiv T externalTime σ)
          (Equiv.refl
            (Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))))) : ℤ) : ℂ) =
      externalInsertionMixedAtomicOrderSign externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1) := by
  classical
  have hsign :
      Equiv.Perm.sign
          (Equiv.sumCongr (externalInsertionLeftMixedToFixedEquiv T externalTime σ)
            (Equiv.refl
              (Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))))) =
        Equiv.Perm.sign
          (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
            (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)) := by
    rw [externalInsertionLeftMixedToFixedEquiv_eq_standardMixedPosition_symm]
    simp only [Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl,
      mul_one, Equiv.Perm.sign_symm]
  change ((Equiv.Perm.sign
      (Equiv.sumCongr (externalInsertionLeftMixedToFixedEquiv T externalTime σ)
        (Equiv.refl
          (Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))))) : ℤ) : ℂ) =
    ((Equiv.Perm.sign
      (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)) : ℤ) : ℂ)
  exact congrArg (fun s : ℤˣ => ((s : ℤ) : ℂ)) hsign

end Fermionic
end SecondQuantization
