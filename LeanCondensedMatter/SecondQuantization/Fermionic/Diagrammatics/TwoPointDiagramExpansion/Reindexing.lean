import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointWickDiagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel
import Mathlib.Data.List.NodupEquivFin

set_option linter.style.header false

/-!
# Reindexing the two-point pairing expansion

The Bloch--de Dominicis theorem pairs the atomic operators in their mixed imaginary-time order.
A `TwoPointWickDiagram`, however, stores a pairing on the standard leg enumeration consisting of
two external legs and four legs at every interaction vertex.

This module records the atomic leg identity parallel to the operator list, proves that the resulting
list enumerates every two-point leg exactly once, and transports pairings between the mixed-time and
standard diagram enumerations. Crossing weights are deliberately evaluated only after transporting
a diagram pairing back to mixed-time order.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

/-- The standard two-point leg type for `n` interaction slots. -/
abbrev OrderedTwoPointLeg (n : ℕ) : Type :=
  Common.TwoPointLeg (Finset.univ : Finset (Fin n))

/-- The standard two-point vertex type for `n` interaction slots. -/
abbrev OrderedTwoPointVertex (n : ℕ) : Type :=
  Common.TwoPointVertex (Finset.univ : Finset (Fin n))

/-- The leg identities contributed by one external or interaction event. -/
def twoPointTimedEventAtomicLegs {n : ℕ} :
    TwoPointTimedEvent n → List (OrderedTwoPointLeg n)
  | .inl e => [Sum.inl e]
  | .inr v => List.ofFn fun l : Fin 4 =>
      Sum.inr (⟨v, Finset.mem_univ v⟩, l)

@[simp]
theorem twoPointTimedEventAtomicLegs_external {n : ℕ} (e : Fin 2) :
    twoPointTimedEventAtomicLegs (n := n) (Sum.inl e) = [Sum.inl e] :=
  rfl

@[simp]
theorem twoPointTimedEventAtomicLegs_interaction {n : ℕ} (v : Fin n) :
    twoPointTimedEventAtomicLegs (Sum.inr v) =
      List.ofFn (fun l : Fin 4 => Sum.inr (⟨v, Finset.mem_univ v⟩, l)) :=
  rfl

/-- The canonical event order expanded to standard two-point leg identities. -/
def canonicalTwoPointAtomicLegs (n : ℕ) : List (OrderedTwoPointLeg n) :=
  ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n).flatMap
    twoPointTimedEventAtomicLegs

/-- The leg identities parallel to `mixedTimeOrderedAtomicOperators`. -/
noncomputable def mixedTimeOrderedAtomicLegs {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List (OrderedTwoPointLeg n) :=
  (orderedTwoPointTimedEvents τ τ' σ).flatMap twoPointTimedEventAtomicLegs

/-- Mixed time ordering only permutes the complete standard two-point leg list. -/
theorem mixedTimeOrderedAtomicLegs_perm_canonical {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List.Perm (mixedTimeOrderedAtomicLegs τ τ' σ) (canonicalTwoPointAtomicLegs n) := by
  simpa [mixedTimeOrderedAtomicLegs, canonicalTwoPointAtomicLegs] using
    (orderedTwoPointTimedEvents_perm τ τ' σ).flatMap
      (fun event _ => List.Perm.refl (twoPointTimedEventAtomicLegs event))

private theorem canonicalTwoPointTimedEvents_nodup (n : ℕ) :
    ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n).Nodup := by
  rw [twoPointInteractionEventList]
  change ((Sum.inl (0 : Fin 2) : TwoPointTimedEvent n) ::
    (Sum.inl (1 : Fin 2) : TwoPointTimedEvent n) ::
      List.ofFn (fun v : Fin n => (Sum.inr v : TwoPointTimedEvent n))).Nodup
  refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ?_⟩⟩
  · simp
  · simp
  · exact List.nodup_ofFn_ofInjective Sum.inr_injective

private theorem twoPointTimedEventAtomicLegs_nodup {n : ℕ}
    (event : TwoPointTimedEvent n) :
    (twoPointTimedEventAtomicLegs event).Nodup := by
  cases event with
  | inl e => simp
  | inr v =>
      rw [twoPointTimedEventAtomicLegs]
      apply List.nodup_ofFn_ofInjective
      intro a b h
      exact congrArg Prod.snd (Sum.inr.inj h)

private theorem twoPointTimedEventAtomicLegs_disjoint {n : ℕ}
    {a b : TwoPointTimedEvent n} (h : a ≠ b) :
    List.Disjoint (twoPointTimedEventAtomicLegs a) (twoPointTimedEventAtomicLegs b) := by
  cases a with
  | inl e =>
      cases b with
      | inl e' => simpa using h.symm
      | inr v => simp
  | inr v =>
      cases b with
      | inl e => simp
      | inr v' =>
          have hv : v ≠ v' := by
            intro hv
            apply h
            cases hv
            rfl
          simpa using hv.symm

private theorem canonicalTwoPointAtomicLegs_nodup (n : ℕ) :
    (canonicalTwoPointAtomicLegs n).Nodup := by
  rw [canonicalTwoPointAtomicLegs, List.nodup_flatMap]
  refine ⟨fun event _ => twoPointTimedEventAtomicLegs_nodup event, ?_⟩
  exact (canonicalTwoPointTimedEvents_nodup n).pairwise_of_forall_ne
    (fun _ _ _ _ h => twoPointTimedEventAtomicLegs_disjoint h)

private theorem canonicalTwoPointAtomicLegs_all_mem (n : ℕ) :
    ∀ leg : OrderedTwoPointLeg n, leg ∈ canonicalTwoPointAtomicLegs n := by
  intro leg
  cases leg with
  | inl e =>
      fin_cases e <;>
        simp [canonicalTwoPointAtomicLegs, twoPointTimedEventAtomicLegs,
          twoPointInteractionEventList]
  | inr p =>
      rcases p with ⟨⟨v, hv⟩, l⟩
      fin_cases l <;>
        simp [canonicalTwoPointAtomicLegs, twoPointTimedEventAtomicLegs,
          twoPointInteractionEventList]

/-- The mixed-time leg list has no duplicate leg identities. -/
theorem mixedTimeOrderedAtomicLegs_nodup {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicLegs τ τ' σ).Nodup :=
  (mixedTimeOrderedAtomicLegs_perm_canonical τ τ' σ).nodup_iff.mpr
    (canonicalTwoPointAtomicLegs_nodup n)

/-- Every standard external or interaction leg occurs in the mixed-time leg list. -/
theorem mixedTimeOrderedAtomicLegs_all_mem {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    ∀ leg : OrderedTwoPointLeg n, leg ∈ mixedTimeOrderedAtomicLegs τ τ' σ := by
  intro leg
  exact (mixedTimeOrderedAtomicLegs_perm_canonical τ τ' σ).symm.subset
    (canonicalTwoPointAtomicLegs_all_mem n leg)

/-- The mixed-time leg list has exactly `4n + 2` entries. -/
theorem mixedTimeOrderedAtomicLegs_length {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicLegs τ τ' σ).length = 2 * (2 * n + 1) := by
  let l := mixedTimeOrderedAtomicLegs τ τ' σ
  have hcard : l.length = Fintype.card (OrderedTwoPointLeg n) := by
    simpa using Fintype.card_congr
      (List.Nodup.getEquivOfForallMemList l
        (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
        (mixedTimeOrderedAtomicLegs_all_mem τ τ' σ))
  rw [hcard]
  simp [OrderedTwoPointLeg]
  omega

/-- The exact bijection from mixed-time atomic positions to standard two-point legs. -/
noncomputable def mixedTimeOrderedAtomicLegEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) ≃ OrderedTwoPointLeg n :=
  (finCongr (mixedTimeOrderedAtomicLegs_length τ τ' σ).symm).trans
    (List.Nodup.getEquivOfForallMemList (mixedTimeOrderedAtomicLegs τ τ' σ)
      (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
      (mixedTimeOrderedAtomicLegs_all_mem τ τ' σ))

/-- The ambient permutation mapping a standard diagram-leg position to the corresponding
mixed-time atomic position. -/
noncomputable def standardToMixedAtomicPositionEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + 1))) :=
  (finCongr (by simp)).trans
    ((Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).trans
      (mixedTimeOrderedAtomicLegEquiv τ τ' σ).symm)

variable {Mode : Type*}

/-- Two-point Wick diagrams whose external labels are fixed to
`Tτ cᵢ(τ) cⱼ†(τ')`. -/
def FixedExternalTwoPointWickDiagram (Mode : Type*) (n : ℕ) (i j : Mode) : Type _ :=
  {d : TwoPointWickDiagram Mode n (Finset.univ : Finset (Fin n)) //
    d.externalLabel = twoPointExternalLabels i j}

/-- Slot-indexed quartic labels together with a pairing in mixed-time atomic order. -/
abbrev OrderedTwoPointWickDiagramData (Mode : Type*) (n : ℕ) : Type _ :=
  (Fin n → QuarticVertexLabel Mode) × Pairing (2 * n + 1)

/-- Cast the standard diagram pairing cardinality from `univ.card` to the explicit slot count. -/
noncomputable def orderedTwoPointPairingCastEquiv (n : ℕ) :
    Pairing (2 * (Finset.univ : Finset (Fin n)).card + 1) ≃ Pairing (2 * n + 1) :=
  Equiv.cast (by simp)

/-- The slot-indexed interaction labels of a fixed-external two-point diagram. -/
def FixedExternalTwoPointWickDiagram.vertexLabelSequence {n : ℕ} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    Fin n → QuarticVertexLabel Mode :=
  fun v => d.1.vertexLabel ⟨v, Finset.mem_univ v⟩

/-- A diagram pairing transported from standard diagram-leg order back to mixed-time atomic order. -/
noncomputable def FixedExternalTwoPointWickDiagram.pairingInMixedOrder {n : ℕ} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : Pairing (2 * n + 1) :=
  (orderedTwoPointPairingCastEquiv n d.1.pairing).relabel
    (standardToMixedAtomicPositionEquiv τ τ' σ).symm

/-- Fixed-external two-point diagrams are equivalent to slot-indexed vertex labels and a pairing
in the mixed-time atomic enumeration. -/
noncomputable def fixedExternalTwoPointWickDiagramEquivOrderedData
    {n : ℕ} (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    FixedExternalTwoPointWickDiagram Mode n i j ≃
      OrderedTwoPointWickDiagramData Mode n where
  toFun d := (d.vertexLabelSequence, d.pairingInMixedOrder τ τ' σ)
  invFun x :=
    ⟨{
      externalLabel := twoPointExternalLabels i j
      vertexLabel := fun v => x.1 v.1
      pairing := (orderedTwoPointPairingCastEquiv n).symm
        (x.2.relabel (standardToMixedAtomicPositionEquiv τ τ' σ))
    }, rfl⟩
  left_inv d := by
    apply Subtype.ext
    apply Common.TwoPointDiagram.ext
    · exact d.2.symm
    · funext _
      rfl
    · rw [Pairing.relabel_relabel_symm]
      exact (orderedTwoPointPairingCastEquiv n).left_inv d.1.pairing
  right_inv x := by
    obtain ⟨labels, pairing⟩ := x
    apply Prod.ext
    · funext _
      rfl
    · rw [(orderedTwoPointPairingCastEquiv n).right_inv]
      exact Pairing.relabel_symm_relabel pairing
        (standardToMixedAtomicPositionEquiv τ τ' σ)

noncomputable instance FixedExternalTwoPointWickDiagram.instFintype
    [Fintype Mode] {n : ℕ} {i j : Mode} :
    Fintype (FixedExternalTwoPointWickDiagram Mode n i j) :=
  Fintype.ofInjective
    (fun d : FixedExternalTwoPointWickDiagram Mode n i j => d.1)
    (fun _ _ h => Subtype.ext h)

/-- Reindex a finite sum over fixed-external diagrams as a sum over slot labels and mixed-order
pairings. -/
theorem sum_fixedExternalTwoPointWickDiagram_eq_sum_orderedData
    [Fintype Mode] {n : ℕ} (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (F : OrderedTwoPointWickDiagramData Mode n → ℂ) :
    ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        F (fixedExternalTwoPointWickDiagramEquivOrderedData i j τ τ' σ d) =
      ∑ x : OrderedTwoPointWickDiagramData Mode n, F x :=
  Equiv.sum_comp (fixedExternalTwoPointWickDiagramEquivOrderedData i j τ τ' σ) F

end Fermionic
end SecondQuantization
