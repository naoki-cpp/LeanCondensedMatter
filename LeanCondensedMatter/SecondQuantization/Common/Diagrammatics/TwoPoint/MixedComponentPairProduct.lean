import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairEquiv

set_option linter.style.header false

/-!
# Products over mixed-time two-point component pairs

The normalized pairs of a generic mixed-order two-point pairing partition by full connected
component. This module provides the corresponding dependent-sum equivalence and commutative-product
factorizations. No field, operator, Gibbs, or statistics-specific data enter these statements.
-/

namespace SecondQuantization
namespace Common

/-- A type is equivalent to the dependent sum of the fibers of any function out of it. -/
private def sigmaFiberEquiv {α ι : Type*} (f : α → ι) :
    (Σ i, {x : α // f x = i}) ≃ α where
  toFun x := x.2.1
  invFun x := ⟨f x, ⟨x, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨i, ⟨x, hx⟩⟩
    cases hx
    rfl
  right_inv _ := rfl

/-- The dependent family of mixed component pairs is equivalent to all normalized mixed pairs. -/
noncomputable def TwoPointDiagram.mixedComponentPairSigmaEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (Σ B : d.componentPartition.parts, d.MixedComponentPair τ τ' σ B) ≃
      (d.pairingInMixedOrder τ τ' σ).NormalizedPair :=
  sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)

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
theorem TwoPointDiagram.prod_mixedComponentPairs
    {M : Type*} [CommMonoid M]
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (F : (d.pairingInMixedOrder τ τ' σ).NormalizedPair → M) :
    (∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair, F pr) =
      ∏ B : d.componentPartition.parts,
        ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1 := by
  classical
  calc
    (∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair, F pr) =
        ∏ x : Σ B : d.componentPartition.parts, d.MixedComponentPair τ τ' σ B,
          F (d.mixedComponentPairSigmaEquiv τ τ' σ x) :=
      (Equiv.prod_comp (d.mixedComponentPairSigmaEquiv τ τ' σ) F).symm
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1 := by
      rw [Fintype.prod_sigma]
      rfl

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
