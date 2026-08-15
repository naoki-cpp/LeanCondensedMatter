import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentVertexProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentProduct

set_option linter.style.header false

/-!
# Products over mixed-time two-point component pairs

The normalized pairs of a generic mixed-order two-point pairing partition by full connected
component. This module provides the corresponding dependent-sum equivalence and commutative-product
factorizations. No field, operator, Gibbs, or statistics-specific data enter these statements.
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

/-- Reindex a commutative product over normalized mixed pairs as an iterated product over full
components and their mixed-pair fibers. -/
private theorem TwoPointDiagram.prod_mixedComponentPairs
    {M : Type*} [CommMonoid M]
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (F : (d.pairingInMixedOrder τ τ' σ).NormalizedPair → M) :
    (∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair, F pr) =
      ∏ B : d.componentPartition.parts,
        ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1 := by
  simpa only [TwoPointDiagram.mixedComponentPairSigmaEquiv_apply] using
    (d.pairingInMixedOrder τ τ' σ).prod_componentDecomposition
      (d.mixedComponentPairSigmaEquiv τ τ' σ) F

/-- A mixed pair-local product splits into the canonical external component and all vacuum
components. -/
theorem TwoPointDiagram.prod_mixedComponentPairs_eq_external_mul_prod_vacuum
    {M : Type*} [CommMonoid M]
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (F : (d.pairingInMixedOrder τ τ' σ).NormalizedPair → M) :
    (∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair, F pr) =
      (∏ pr : d.MixedComponentPair τ τ' σ d.externalComponentPart, F pr.1) *
        d.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1) := by
  rw [d.prod_mixedComponentPairs τ τ' σ F,
    d.prod_componentParts_eq_external_mul_prod_vacuum]

/-- Nested-Finset form of the mixed pair-product factorization. -/
theorem TwoPointDiagram.prod_mixedPairValues_eq_external_mul_prod_vacuum
    {M : Type*} [CommMonoid M]
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (F : Fin (2 * (2 * n + 1)) × Fin (2 * (2 * n + 1)) → M) :
    (∏ pr ∈ (d.pairingInMixedOrder τ τ' σ).pairs, F pr) =
      (∏ pr : d.MixedComponentPair τ τ' σ d.externalComponentPart, F pr.1.1) *
        d.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1.1) := by
  classical
  calc
    (∏ pr ∈ (d.pairingInMixedOrder τ τ' σ).pairs, F pr) =
        ∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair, F pr.1 :=
      Finset.prod_subtype (d.pairingInMixedOrder τ τ' σ).pairs (fun _ => Iff.rfl) F
    _ = (∏ pr : d.MixedComponentPair τ τ' σ d.externalComponentPart, F pr.1.1) *
        d.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1.1) :=
      d.prod_mixedComponentPairs_eq_external_mul_prod_vacuum τ τ' σ (fun pr => F pr.1)

end Common
end SecondQuantization
