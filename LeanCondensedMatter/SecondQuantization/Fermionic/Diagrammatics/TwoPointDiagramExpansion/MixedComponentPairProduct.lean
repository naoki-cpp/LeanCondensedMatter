import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairEquiv

set_option linter.style.header false

/-!
# Products over mixed-time two-point component pairs

The canonical two-point pairing value evaluates contractions on normalized pairs of
`pairingInMixedOrder`.  This module partitions those pairs by the full diagram component containing
their endpoints, factors arbitrary commutative pair products into the external component and vacuum
components, and specializes the result to the canonical free Gibbs density-state contraction product.

Vacuum restricted-pair equivalences are used only by pullback: local restricted pair values are
defined from the corresponding original mixed-time pair. This avoids assuming that a component-
position equivalence preserves the normalized endpoint order. The external component is related to
the standalone external piece downstream in `ExternalPiecePairing`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

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
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPairSigmaEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (Σ B : d.1.componentPartition.parts, d.MixedComponentPair τ τ' σ B) ≃
      (d.pairingInMixedOrder τ τ' σ).NormalizedPair :=
  sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)

@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairSigmaEquiv_apply
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedComponentPairSigmaEquiv τ τ' σ ⟨B, pr⟩ = pr.1 :=
  rfl

/-- Reindex a commutative product over normalized mixed pairs as an iterated product over full
components and their mixed pair fibers. -/
theorem FixedExternalTwoPointWickDiagram.prod_mixedComponentPairs
    {M : Type*} [CommMonoid M]
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (F : (d.pairingInMixedOrder τ τ' σ).NormalizedPair → M) :
    (∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair, F pr) =
      ∏ B : d.1.componentPartition.parts,
        ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1 := by
  classical
  calc
    (∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair, F pr) =
        ∏ x : Σ B : d.1.componentPartition.parts,
          d.MixedComponentPair τ τ' σ B,
          F (d.mixedComponentPairSigmaEquiv τ τ' σ x) :=
      (Equiv.prod_comp (d.mixedComponentPairSigmaEquiv τ τ' σ) F).symm
    _ = ∏ B : d.1.componentPartition.parts,
        ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1 := by
      rw [Fintype.prod_sigma]
      rfl

/-- A mixed pair-local product splits into the canonical external component and all vacuum
components. -/
theorem FixedExternalTwoPointWickDiagram.prod_mixedComponentPairs_eq_external_mul_prod_vacuum
    {M : Type*} [CommMonoid M]
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (F : (d.pairingInMixedOrder τ τ' σ).NormalizedPair → M) :
    (∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair, F pr) =
      (∏ pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart, F pr.1) *
        d.1.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1) := by
  rw [d.prod_mixedComponentPairs τ τ' σ F,
    d.1.prod_componentParts_eq_external_mul_prod_vacuum]

/-- Nested-Finset form of the mixed pair-product factorization. -/
theorem FixedExternalTwoPointWickDiagram.prod_mixedPairValues_eq_external_mul_prod_vacuum
    {M : Type*} [CommMonoid M]
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (F : Fin (2 * (2 * n + 1)) × Fin (2 * (2 * n + 1)) → M) :
    (∏ pr ∈ (d.pairingInMixedOrder τ τ' σ).pairs, F pr) =
      (∏ pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart, F pr.1.1) *
        d.1.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1.1) := by
  classical
  calc
    (∏ pr ∈ (d.pairingInMixedOrder τ τ' σ).pairs, F pr) =
        ∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair, F pr.1 :=
      Finset.prod_subtype (d.pairingInMixedOrder τ τ' σ).pairs
        (fun _ => Iff.rfl) F
    _ = (∏ pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart, F pr.1.1) *
        d.1.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.MixedComponentPair τ τ' σ B, F pr.1.1) :=
      d.prod_mixedComponentPairs_eq_external_mul_prod_vacuum τ τ' σ
        (fun pr => F pr.1)

section Fermionic

variable [LinearOrder Mode] [Fintype Mode]

/-- Canonical free Gibbs density-state contraction attached to one normalized pair in the actual
mixed-time pairing. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair) : ℂ :=
  mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ d.vertexLabelSequence
    pr.1.1 pr.1.2

/-- The mixed-time contraction product factors into the external component and all vacuum
components. -/
theorem FixedExternalTwoPointWickDiagram.prod_mixedPairContractionValue_eq_external_mul_prod_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (∏ pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair,
      d.mixedPairContractionValue ε β τ τ' σ pr) =
      (∏ pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart,
        d.mixedPairContractionValue ε β τ τ' σ pr.1) *
        d.1.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.MixedComponentPair τ τ' σ B,
            d.mixedPairContractionValue ε β τ τ' σ pr.1) :=
  d.prod_mixedComponentPairs_eq_external_mul_prod_vacuum τ τ' σ
    (d.mixedPairContractionValue ε β τ τ' σ)

/-- The canonical pairing value exposes the component-factorized contraction product while retaining
the global mixed-order fermionic pairing weight. -/
theorem FixedExternalTwoPointWickDiagram.orderedTwoPointPairingValue_eq_weight_mul_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    orderedTwoPointPairingValue ε β i j τ τ' σ d.vertexLabelSequence
        (d.pairingInMixedOrder τ τ' σ) =
      (d.pairingInMixedOrder τ τ' σ).weight Common.Statistics.fermion *
        ((∏ pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart,
          d.mixedPairContractionValue ε β τ τ' σ pr.1) *
          d.1.vacuumComponentParts.prod (fun B =>
            ∏ pr : d.MixedComponentPair τ τ' σ B,
              d.mixedPairContractionValue ε β τ τ' σ pr.1)) := by
  unfold orderedTwoPointPairingValue Combinatorics.Pairing.evaluation
  rw [d.prod_mixedPairValues_eq_external_mul_prod_vacuum τ τ' σ]
  rfl

/-- A restricted vacuum-pair value is defined by pulling back to its unique original mixed-time
pair. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedVacuumRestrictedPairContractionValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum B)
    (pr : (d.1.restrictedVacuumPairing B hVac).NormalizedPair) : ℂ :=
  d.mixedPairContractionValue ε β τ τ' σ
    ((d.mixedVacuumComponentPairEquiv τ τ' σ B hVac).symm pr).1

/-- One vacuum-component contraction product reindexes to its restricted vacuum pairing without an
endpoint-orientation assumption. -/
theorem FixedExternalTwoPointWickDiagram.prod_mixedVacuumPairContractionValue_eq_restricted
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum B) :
    (∏ pr : d.MixedComponentPair τ τ' σ B,
      d.mixedPairContractionValue ε β τ τ' σ pr.1) =
      ∏ pr : (d.1.restrictedVacuumPairing B hVac).NormalizedPair,
        d.mixedVacuumRestrictedPairContractionValue ε β τ τ' σ B hVac pr := by
  calc
    (∏ pr : d.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' σ pr.1) =
      ∏ pr : d.MixedComponentPair τ τ' σ B,
        d.mixedVacuumRestrictedPairContractionValue ε β τ τ' σ B hVac
          (d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr) := by
        apply Fintype.prod_congr
        intro pr
        simp [FixedExternalTwoPointWickDiagram.mixedVacuumRestrictedPairContractionValue]
    _ = ∏ pr : (d.1.restrictedVacuumPairing B hVac).NormalizedPair,
        d.mixedVacuumRestrictedPairContractionValue ε β τ τ' σ B hVac pr :=
      Equiv.prod_comp (d.mixedVacuumComponentPairEquiv τ τ' σ B hVac)
        (d.mixedVacuumRestrictedPairContractionValue ε β τ τ' σ B hVac)

end Fermionic

end Fermionic
end SecondQuantization
