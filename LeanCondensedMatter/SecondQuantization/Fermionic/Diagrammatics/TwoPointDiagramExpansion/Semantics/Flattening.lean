import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Flattening
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedTimeOrdering

set_option linter.style.header false

/-!
# Flattening a two-point insertion with quartic vertices

This module refines the mixed event-level time ordering of a fermionic two-point function into its
atomic creation/annihilation operator list. Each external event contributes one atomic operator and
each quartic interaction event contributes its four local legs in the fixed
`create₁, create₂, annihilate₂, annihilate₁` order.

The resulting list has exactly `4n + 2 = 2 * (2n + 1)` entries, which is the even finite family
required by the existing Bloch--de Dominicis pairing theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode]

/-- The atomic operator list contributed by one time-ordered external or quartic interaction event. -/
noncomputable def twoPointTimedEventAtomicOperators {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → List (OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
  | .inl e =>
      [externalFieldOperator ε (twoPointExternalTimes τ τ' e) (twoPointExternalLabels i j e)]
  | .inr v =>
      List.ofFn fun l : Fin 4 =>
        imaginaryTimeEvolve ε (σ v) (quarticLocalLegOperator (q v) l)

@[simp]
theorem twoPointTimedEventAtomicOperators_external {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) (e : Fin 2) :
    twoPointTimedEventAtomicOperators ε i j τ τ' q σ (Sum.inl e) =
      [externalFieldOperator ε (twoPointExternalTimes τ τ' e) (twoPointExternalLabels i j e)] :=
  rfl

@[simp]
theorem twoPointTimedEventAtomicOperators_interaction {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) (v : Fin n) :
    twoPointTimedEventAtomicOperators ε i j τ τ' q σ (Sum.inr v) =
      List.ofFn (fun l : Fin 4 =>
        imaginaryTimeEvolve ε (σ v) (quarticLocalLegOperator (q v) l)) :=
  rfl

/-- The number of atomic operators contributed by one mixed event. -/
def twoPointTimedEventAtomicArity {n : ℕ} : TwoPointTimedEvent n → ℕ
  | .inl _ => 1
  | .inr _ => 4

@[simp]
theorem twoPointTimedEventAtomicOperators_length {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    (twoPointTimedEventAtomicOperators ε i j τ τ' q σ event).length =
      twoPointTimedEventAtomicArity event := by
  cases event <;> simp [twoPointTimedEventAtomicArity]

/-- Expanding one mixed event into atomic operators preserves its represented operator product. -/
theorem prodComp_twoPointTimedEventAtomicOperators {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    Common.prodComp (twoPointTimedEventAtomicOperators ε i j τ τ' q σ event) =
      twoPointTimedEventOperator ε i j τ τ' q σ event := by
  cases event with
  | inl e =>
      rw [twoPointTimedEventAtomicOperators_external]
      simp [twoPointTimedEventOperator, Common.prodComp]
  | inr v =>
      rw [twoPointTimedEventAtomicOperators_interaction,
        twoPointTimedEventOperator_interaction]
      exact (interactionPicture_quarticVertexOperator_eq_prodComp ε (q v) (σ v)).symm

/-- The complete atomic operator list in mixed imaginary-time order. -/
noncomputable def mixedTimeOrderedAtomicOperators {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    List (OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :=
  (orderedTwoPointTimedEvents τ τ' σ).flatMap
    (twoPointTimedEventAtomicOperators ε i j τ τ' q σ)

private theorem canonicalTwoPointTimedEventAtomicAritySum (n : ℕ) :
    (([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n).map
      twoPointTimedEventAtomicArity).sum = 2 * (2 * n + 1) := by
  have hinteraction :
      ((twoPointInteractionEventList n).map twoPointTimedEventAtomicArity).sum = 4 * n := by
    rw [twoPointInteractionEventList, List.map_ofFn]
    change (List.ofFn (fun _ : Fin n => 4)).sum = 4 * n
    simp [Nat.mul_comm]
  rw [List.map_append, List.sum_append, hinteraction]
  simp [twoPointTimedEventAtomicArity]
  omega

/-- A two-point insertion with `n` quartic vertices contains exactly `4n + 2` atomic operators. -/
@[simp]
theorem mixedTimeOrderedAtomicOperators_length {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicOperators ε i j τ τ' q σ).length = 2 * (2 * n + 1) := by
  rw [mixedTimeOrderedAtomicOperators, List.length_flatMap]
  simp_rw [twoPointTimedEventAtomicOperators_length]
  calc
    ((orderedTwoPointTimedEvents τ τ' σ).map twoPointTimedEventAtomicArity).sum =
        (([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n).map
          twoPointTimedEventAtomicArity).sum :=
      ((orderedTwoPointTimedEvents_perm τ τ' σ).map twoPointTimedEventAtomicArity).sum_eq
    _ = 2 * (2 * n + 1) := canonicalTwoPointTimedEventAtomicAritySum n

/-- The event-level mixed time-ordered product is exactly the fermionic external-order sign times
the composed product of its `4n + 2` atomic creation/annihilation operators. -/
theorem mixedTimeOrderedVertexComp_eq_prodComp_atomicOperators {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ =
      twoPointExternalOrderSign τ τ' •
        Common.prodComp (mixedTimeOrderedAtomicOperators ε i j τ τ' q σ) := by
  have hprod : ∀ events : List (TwoPointTimedEvent n),
      Common.prodComp
          (events.flatMap (twoPointTimedEventAtomicOperators ε i j τ τ' q σ)) =
        Common.prodComp
          (events.map (twoPointTimedEventOperator ε i j τ τ' q σ)) := by
    intro events
    induction events with
    | nil => rfl
    | cons event events ih =>
        rw [List.flatMap_cons, List.map_cons, Common.prodComp_append, Common.prodComp_cons,
          prodComp_twoPointTimedEventAtomicOperators, ih]
  rw [mixedTimeOrderedVertexComp, mixedTimeOrderedAtomicOperators, hprod]

end Fermionic
end SecondQuantization
