import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.CutIntervals
import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport

set_option linter.style.header false

/-!
# Interaction legs of a separating-cut interval

The vertices between two nested separating cuts are a finite interaction sector.
Here we identify the incident ambient legs with the standard four legs of each
interaction vertex. The original external vertices are outside this region.

This is the incidence equivalence needed to turn an interval's restricted
pairing, together with its two boundary ends, into a standalone two-point
diagram. Pairing transport and the reconstruction theorem are separate steps.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S : Finset (Fin N)}

/-- The flattened interaction-leg map is injective: distinct interaction
slots or local legs are never identified by flattening. -/
theorem twoPointInteractionLeg_injective (S : Finset (Fin N)) :
    Function.Injective
      (fun p : ↥S × Fin 4 => twoPointInteractionLeg p.1 p.2) := by
  intro p q hpq
  have h := congrArg (twoPointLegEquiv S) hpq
  simpa [twoPointInteractionLeg] using h

/-- The interaction legs of the finite vertex interval, in their original
ambient flattened coordinates.

The only inputs are the two cuts and the fact that the later cut separates
the external vertices. The source external vertex is never in the interval;
the separation hypothesis excludes the target external vertex. -/
noncomputable def TwoPointDiagram.intervalInteractionLegEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    (↥(interactionSector (d.verticesBetweenCuts earlier later)) × Fin 4) ≃
      {leg : Fin (2 * (2 * S.card + 1)) //
        twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later} := by
  classical
  let f :
      ↥(interactionSector (d.verticesBetweenCuts earlier later)) × Fin 4 →
        {leg : Fin (2 * (2 * S.card + 1)) //
          twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later} := fun p => by
    let v : ↥S :=
      ⟨p.1.1, interactionSector_subset (d.verticesBetweenCuts earlier later) p.1.2⟩
    refine ⟨twoPointInteractionLeg v p.2, ?_⟩
    simpa only [twoPointVertexOfLeg_interactionLeg] using
      (d.mem_interactionSector_verticesBetweenCuts_iff earlier later v).1 p.1.2
  refine Equiv.ofBijective f ?_
  constructor
  · intro p q hpq
    have hflat : (f p).1 = (f q).1 := congrArg Subtype.val hpq
    have hpair :
        ((⟨p.1.1, interactionSector_subset
          (d.verticesBetweenCuts earlier later) p.1.2⟩ : ↥S), p.2) =
        ((⟨q.1.1, interactionSector_subset
          (d.verticesBetweenCuts earlier later) q.1.2⟩ : ↥S), q.2) :=
      twoPointInteractionLeg_injective S (by simpa [f] using hflat)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun x => (x.1 : ↥S).1) hpair
    · exact congrArg (fun x : ↥S × Fin 4 => x.2) hpair
  · rintro ⟨leg, hleg⟩
    cases h : twoPointLegEquiv S leg with
    | inl e =>
        have hv : twoPointVertexOfLeg leg = (Sum.inl e : TwoPointVertex S) := by
          simp [twoPointVertexOfLeg, h]
        fin_cases e
        · exact False.elim
            (d.externalZero_not_mem_verticesBetweenCuts earlier later (hv ▸ hleg))
        · exact False.elim
            (d.externalOne_not_mem_verticesBetweenCuts earlier later hsep (hv ▸ hleg))
    | inr p =>
        obtain ⟨v, l⟩ := p
        have hv : twoPointVertexOfLeg leg = (Sum.inr v : TwoPointVertex S) := by
          simp [twoPointVertexOfLeg, h]
        have hmem : (v : Fin N) ∈
            interactionSector (d.verticesBetweenCuts earlier later) :=
          (d.mem_interactionSector_verticesBetweenCuts_iff earlier later v).2
            (hv ▸ hleg)
        refine ⟨(⟨(v : Fin N), hmem⟩, l), ?_⟩
        apply Subtype.ext
        apply (twoPointLegEquiv S).injective
        simp [f, twoPointInteractionLeg, h]

end Common
end SecondQuantization
