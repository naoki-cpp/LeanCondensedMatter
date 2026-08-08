import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentVertexProduct

set_option linter.style.header false

/-!
# Pair products over external and vacuum components of two-point diagrams

Every normalized pair of a two-point diagram belongs to the unique full component containing either
endpoint.  Partner stability implies that both endpoints determine the same component.  Reindexing
normalized pairs by this component map factors arbitrary pair-local sums and commutative products
over all components, and then over the canonical external component and the vacuum components.
The resulting equivalence is independent of statistics and of the eventual pair-value semantics.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

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

/-- The full connected component containing a normalized pair.  The first endpoint is used to choose
it; partner stability shows that the second endpoint lies in the same component. -/
noncomputable def TwoPointDiagram.pairComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (pr : d.pairing.NormalizedPair) : d.componentPartition.parts :=
  ⟨d.componentBlock (twoPointVertexOfLeg pr.1.1),
    d.componentBlock_mem_componentPartition (twoPointVertexOfLeg pr.1.1)⟩

/-- Normalized ambient pairs assigned to one full component. -/
abbrev TwoPointDiagram.ComponentPair {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :=
  {pr : d.pairing.NormalizedPair // d.pairComponent pr = B}

/-- The first endpoint of a component pair belongs to that component. -/
theorem TwoPointDiagram.componentPair_first_legInComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (pr : d.ComponentPair B) :
    d.legInComponent (B : Finset (TwoPointVertex S)) pr.1.1.1 := by
  change d.componentBlock (twoPointVertexOfLeg pr.1.1.1) =
    (B : Finset (TwoPointVertex S))
  exact congrArg Subtype.val pr.2

/-- The two endpoints of a normalized pair determine the same full component. -/
theorem TwoPointDiagram.componentBlock_second_eq_first_of_normalizedPair
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (pr : d.pairing.NormalizedPair) :
    d.componentBlock (twoPointVertexOfLeg pr.1.2) =
      d.componentBlock (twoPointVertexOfLeg pr.1.1) := by
  have hpr := pr.2
  rw [Combinatorics.Pairing.mem_pairs_iff] at hpr
  rw [← hpr.2]
  exact d.componentBlock_vertexOfLeg_partner pr.1.1

/-- The second endpoint of a component pair belongs to that component. -/
theorem TwoPointDiagram.componentPair_second_legInComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (pr : d.ComponentPair B) :
    d.legInComponent (B : Finset (TwoPointVertex S)) pr.1.1.2 := by
  change d.componentBlock (twoPointVertexOfLeg pr.1.1.2) =
    (B : Finset (TwoPointVertex S))
  exact (d.componentBlock_second_eq_first_of_normalizedPair pr.1).trans
    (congrArg Subtype.val pr.2)

/-- The dependent family of component pairs is equivalent to all normalized ambient pairs. -/
noncomputable def TwoPointDiagram.componentPairEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    (Σ B : d.componentPartition.parts, d.ComponentPair B) ≃
      d.pairing.NormalizedPair :=
  sigmaFiberEquiv d.pairComponent

@[simp]
theorem TwoPointDiagram.componentPairEquiv_apply {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (pr : d.ComponentPair B) :
    d.componentPairEquiv ⟨B, pr⟩ = pr.1 :=
  rfl

/-- Reindex a sum over normalized pairs as an iterated sum over full components. -/
theorem TwoPointDiagram.sum_componentPairs
    {A : Type*} [AddCommMonoid A]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (F : d.pairing.NormalizedPair → A) :
    (∑ pr : d.pairing.NormalizedPair, F pr) =
      ∑ B : d.componentPartition.parts,
        ∑ pr : d.ComponentPair B, F pr.1 := by
  classical
  calc
    (∑ pr : d.pairing.NormalizedPair, F pr) =
        ∑ x : Σ B : d.componentPartition.parts, d.ComponentPair B,
          F (d.componentPairEquiv x) :=
      (Equiv.sum_comp d.componentPairEquiv F).symm
    _ = ∑ B : d.componentPartition.parts,
        ∑ pr : d.ComponentPair B, F pr.1 := by
      rw [Fintype.sum_sigma]
      rfl

/-- Reindex a commutative product over normalized pairs as an iterated product over full
components. -/
theorem TwoPointDiagram.prod_componentPairs
    {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (F : d.pairing.NormalizedPair → M) :
    (∏ pr : d.pairing.NormalizedPair, F pr) =
      ∏ B : d.componentPartition.parts,
        ∏ pr : d.ComponentPair B, F pr.1 := by
  classical
  calc
    (∏ pr : d.pairing.NormalizedPair, F pr) =
        ∏ x : Σ B : d.componentPartition.parts, d.ComponentPair B,
          F (d.componentPairEquiv x) :=
      (Equiv.prod_comp d.componentPairEquiv F).symm
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr : d.ComponentPair B, F pr.1 := by
      rw [Fintype.prod_sigma]
      rfl

/-- A pair-local sum splits into the canonical external component and all vacuum components. -/
theorem TwoPointDiagram.sum_componentPairs_eq_external_add_sum_vacuum
    {A : Type*} [AddCommMonoid A]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (F : d.pairing.NormalizedPair → A) :
    (∑ pr : d.pairing.NormalizedPair, F pr) =
      (∑ pr : d.ComponentPair d.externalComponentPart, F pr.1) +
        d.vacuumComponentParts.sum (fun B =>
          ∑ pr : d.ComponentPair B, F pr.1) := by
  rw [d.sum_componentPairs F,
    d.sum_componentParts_eq_external_add_sum_vacuum]

/-- A pair-local commutative product splits into the canonical external component and all vacuum
components. -/
theorem TwoPointDiagram.prod_componentPairs_eq_external_mul_prod_vacuum
    {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (F : d.pairing.NormalizedPair → M) :
    (∏ pr : d.pairing.NormalizedPair, F pr) =
      (∏ pr : d.ComponentPair d.externalComponentPart, F pr.1) *
        d.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.ComponentPair B, F pr.1) := by
  rw [d.prod_componentPairs F,
    d.prod_componentParts_eq_external_mul_prod_vacuum]

/-- Nested-Finset form of pair-product factorization, matching the pair products used by Wick
amplitudes. -/
theorem TwoPointDiagram.prod_pairValues_eq_external_mul_prod_vacuum
    {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (F : Fin (2 * (2 * S.card + 1)) × Fin (2 * (2 * S.card + 1)) → M) :
    (∏ pr ∈ d.pairing.pairs, F pr) =
      (∏ pr : d.ComponentPair d.externalComponentPart, F pr.1.1) *
        d.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.ComponentPair B, F pr.1.1) := by
  classical
  calc
    (∏ pr ∈ d.pairing.pairs, F pr) =
        ∏ pr : d.pairing.NormalizedPair, F pr.1 :=
      Finset.prod_subtype d.pairing.pairs (fun _ => Iff.rfl) F
    _ = (∏ pr : d.ComponentPair d.externalComponentPart, F pr.1.1) *
        d.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.ComponentPair B, F pr.1.1) :=
      d.prod_componentPairs_eq_external_mul_prod_vacuum (fun pr => F pr.1)

end Common
end SecondQuantization
