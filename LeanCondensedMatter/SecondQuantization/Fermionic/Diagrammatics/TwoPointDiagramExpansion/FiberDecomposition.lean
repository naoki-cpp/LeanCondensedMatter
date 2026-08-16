import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitConnectivity

set_option linter.style.header false

/-!
# The fiber decomposition for fixed external labels

`Common.TwoPointDiagram.externalFiberEquiv` decomposes the diagrams whose external component owns
exactly the slots `T` into an externally connected piece on `T` and an arbitrary quartic diagram on
the complement. Both halves of the splitting keep the external label — the piece carries the ambient
one, and reassembling carries the piece's — so the decomposition restricts to diagrams with the
external labels fixed to `Tτ cᵢ(τ) cⱼ†(τ')`.

The same owner records how the standalone external piece behaves under this fiber equivalence. That
restricted form is what the linked-cluster convolution sums over.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

/-- Fixed-external version of the Common external-fiber equivalence. -/
noncomputable def fixedExternalFiberEquiv (T : Finset (Fin n)) :
    {d : FixedExternalTwoPointWickDiagram Mode n i j // d.1.externalInteractionPart = T} ≃
      FixedExternalTwoPointWickDiagramOn Mode n T i j ×
        QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T) := by
  let e := Common.TwoPointDiagram.externalFiberEquiv
    (VertexLabel := QuarticVertexLabel Mode) (WickContractible := WickContraction.Sign) T
  refine Equiv.ofBijective
    (fun d => ⟨⟨(e d.1.1).1, ?_⟩, (e d.1.1).2⟩) ?_
  · have h := d.1.2
    change (e d.1.1).1.externalLabel = twoPointExternalLabels i j
    simpa [e, Common.TwoPointDiagram.externalFiberEquiv] using h
  · constructor
    · intro d₁ d₂ h
      apply Subtype.ext
      apply Subtype.ext
      exact e.injective (Prod.ext (congrArg (fun x => x.1.1) h) (congrArg Prod.snd h))
    · intro p
      let d : TwoPointDiagram (QuarticVertexLabel Mode) n WickContraction.Sign := e.symm ⟨p.1.1, p.2⟩
      have hdPart : d.externalInteractionPart = T := by
        simpa [d] using congrArg (fun x => x.1.externalInteractionPart) (e.apply_symm_apply ⟨p.1.1, p.2⟩)
      have hdLabel : d.externalLabel = twoPointExternalLabels i j := by
        have hp : p.1.1.externalLabel = twoPointExternalLabels i j := p.1.2
        simpa [d] using hp
      refine ⟨⟨⟨d, hdLabel⟩, hdPart⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst (e.apply_symm_apply ⟨p.1.1, p.2⟩)
      · exact congrArg Prod.snd (e.apply_symm_apply ⟨p.1.1, p.2⟩)

/-- Under the fixed-external fiber equivalence, the reassembled diagram's standalone external piece
is the standardized external piece of the left fiber factor. -/
theorem fixedExternalFiberEquiv_symm_externalPiece_heq
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T)) :
    HEq ((fixedExternalFiberEquiv T).symm ⟨ext, vac⟩).1.externalPiece
      ext.1.externalPiece := by
  classical
  let e := Common.TwoPointDiagram.externalFiberEquiv
    (VertexLabel := QuarticVertexLabel Mode) (WickContractible := WickContraction.Sign) T
  let d := (fixedExternalFiberEquiv T).symm ⟨ext, vac⟩
  have hd : e d.1.1 = ⟨ext.1, vac⟩ := by
    have h := (fixedExternalFiberEquiv T).apply_symm_apply ⟨ext, vac⟩
    exact Prod.ext (congrArg (fun x => x.1.1) h) (congrArg Prod.snd h)
  have hRaw := Common.TwoPointDiagram.externalFiberEquiv_symm_externalPiece_heq
    (VertexLabel := QuarticVertexLabel Mode) (WickContractible := WickContraction.Sign)
    T ext.1 vac
  have hAmbient : HEq d.1.1.externalPiece ext.1.externalPiece := by
    rw [show d.1.1 = e.symm ⟨ext.1, vac⟩ by exact e.injective (by simpa using hd)]
    exact hRaw
  exact hAmbient

/-- Sum over all fixed-external diagrams can be decomposed into external-slot fibers. -/
theorem sum_eq_sum_powerset_fixedExternalFiber
    {R : Type*} [AddCommMonoid R]
    (F : FixedExternalTwoPointWickDiagram Mode n i j → R) :
    (∑ d : FixedExternalTwoPointWickDiagram Mode n i j, F d) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ p : FixedExternalTwoPointWickDiagramOn Mode n T i j ×
          QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T),
          F ((fixedExternalFiberEquiv T).symm p).1 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)))
    (t := (Finset.univ : Finset (Fin n)).powerset)
    (g := fun d : FixedExternalTwoPointWickDiagram Mode n i j => d.1.externalInteractionPart)
    (fun d _ => by simp)]
  apply Finset.sum_congr rfl
  intro T hT
  have hTmem : T ⊆ (Finset.univ : Finset (Fin n)) := by simp
  rw [Finset.sum_subtype
    (p := fun d : FixedExternalTwoPointWickDiagram Mode n i j => d.1.externalInteractionPart = T)
    (Finset.filter (fun d : FixedExternalTwoPointWickDiagram Mode n i j =>
      d.1.externalInteractionPart = T) Finset.univ)
    (fun d => by simp)
    F]
  exact Equiv.sum_comp (fixedExternalFiberEquiv T) F

end Fermionic
end SecondQuantization
