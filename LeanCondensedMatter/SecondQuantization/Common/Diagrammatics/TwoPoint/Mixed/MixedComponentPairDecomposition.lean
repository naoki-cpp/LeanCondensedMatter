import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv

set_option linter.style.header false

/-!
# Mixed-time component-pair decomposition

The normalized pairs of a generic mixed-order two-point pairing decompose by full connected
component. This dependent-sum equivalence is shared by crossing, slot-split, external-piece, and
product reindexing consumers, so it is independent of any particular downstream factorization.
-/

namespace SecondQuantization
namespace Common

/-- The dependent family of mixed component pairs is equivalent to all normalized mixed pairs. -/
noncomputable def TwoPointDiagram.mixedComponentPairSigmaEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (Σ B : d.componentPartition.parts, d.MixedComponentPair τ τ' σ B) ≃
      (d.pairingInMixedOrder τ τ' σ).NormalizedPair :=
  Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)

@[simp]
theorem TwoPointDiagram.mixedComponentPairSigmaEquiv_apply
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedComponentPairSigmaEquiv τ τ' σ ⟨B, pr⟩ = pr.1 :=
  rfl

end Common
end SecondQuantization
