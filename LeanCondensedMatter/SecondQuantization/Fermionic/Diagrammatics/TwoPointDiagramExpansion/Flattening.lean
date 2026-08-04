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

variable {Mode : Type*} [LinearOrder Mode]

/-- The atomic operator list contributed by one time-ordered external or quartic interaction event. -/
noncomputable def twoPointTimedEventAtomicOperators {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → List (FockSpace Mode →ₗ[ℂ] FockSpace Mode)
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

omit [LinearOrder Mode] in
private theorem prodComp_singleton (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.prodComp [A] = A := by
  rw [Common.prodComp_cons, Common.prodComp_nil, LinearMap.comp_id]

private theorem twoPointTimedEventOperator_external {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) (e : Fin 2) :
    twoPointTimedEventOperator ε i j τ τ' q σ (Sum.inl e) =
      externalFieldOperator ε (twoPointExternalTimes τ τ' e) (twoPointExternalLabels i j e) :=
  rfl

/-- Expanding one mixed event into atomic operators preserves its represented operator product. -/
theorem prodComp_twoPointTimedEventAtomicOperators {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    Common.prodComp (twoPointTimedEventAtomicOperators ε i j τ τ' q σ event) =
      twoPointTimedEventOperator ε i j τ τ' q σ event := by
  cases event with
  | inl e =>
      rw [twoPointTimedEventAtomicOperators_external, twoPointTimedEventOperator_external,
        prodComp_singleton]
  | inr v =>
      rw [twoPointTimedEventAtomicOperators_interaction,
        twoPointTimedEventOperator_interaction]
      exact (interactionPicture_quarticVertexOperator_eq_prodComp ε (q v) (σ v)).symm

/-- The complete atomic operator list in mixed imaginary-time order. -/
noncomputable def mixedTimeOrderedAtomicOperators {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    List (FockSpace Mode →ₗ[ℂ] FockSpace Mode) :=
  (orderedTwoPointTimedEvents τ τ' σ).flatMap
    (twoPointTimedEventAtomicOperators ε i j τ τ' q σ)

private theorem length_flatMap_twoPointTimedEventAtomicOperators {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (events : List (TwoPointTimedEvent n)) :
    (events.flatMap (twoPointTimedEventAtomicOperators ε i j τ τ' q σ)).length =
      (events.map twoPointTimedEventAtomicArity).sum := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      simp [ih]

private theorem sum_map_eq_of_perm {α : Type*} (f : α → ℕ) {l₁ l₂ : List α}
    (h : List.Perm l₁ l₂) : (l₁.map f).sum = (l₂.map f).sum := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [ih]
  | swap x y l => simp [Nat.add_left_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem sum_ofFn_const_four :
    ∀ n : ℕ, (List.ofFn (fun _ : Fin n => 4)).sum = 4 * n
  | 0 => rfl
  | n + 1 => by
      rw [List.ofFn_succ, List.sum_cons, sum_ofFn_const_four n]
      omega

private theorem canonicalTwoPointTimedEventAtomicAritySum (n : ℕ) :
    (([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n).map
      twoPointTimedEventAtomicArity).sum = 2 * (2 * n + 1) := by
  have hinteraction :
      ((twoPointInteractionEventList n).map twoPointTimedEventAtomicArity).sum = 4 * n := by
    rw [twoPointInteractionEventList, List.map_ofFn]
    change (List.ofFn (fun _ : Fin n => 4)).sum = 4 * n
    exact sum_ofFn_const_four n
  rw [List.map_append, List.sum_append, hinteraction]
  simp [twoPointTimedEventAtomicArity]
  omega

/-- A two-point insertion with `n` quartic vertices contains exactly `4n + 2` atomic operators. -/
@[simp]
theorem mixedTimeOrderedAtomicOperators_length {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicOperators ε i j τ τ' q σ).length = 2 * (2 * n + 1) := by
  rw [mixedTimeOrderedAtomicOperators,
    length_flatMap_twoPointTimedEventAtomicOperators]
  calc
    ((orderedTwoPointTimedEvents τ τ' σ).map twoPointTimedEventAtomicArity).sum =
        (([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n).map
          twoPointTimedEventAtomicArity).sum :=
      sum_map_eq_of_perm twoPointTimedEventAtomicArity
        (orderedTwoPointTimedEvents_perm τ τ' σ)
    _ = 2 * (2 * n + 1) := canonicalTwoPointTimedEventAtomicAritySum n

private theorem prodComp_flatMap_twoPointTimedEventAtomicOperators {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (events : List (TwoPointTimedEvent n)) :
    Common.prodComp
        (events.flatMap (twoPointTimedEventAtomicOperators ε i j τ τ' q σ)) =
      Common.prodComp
        (events.map (twoPointTimedEventOperator ε i j τ τ' q σ)) := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      rw [List.flatMap_cons, List.map_cons, Common.prodComp_append, Common.prodComp_cons,
        prodComp_twoPointTimedEventAtomicOperators, ih]

/-- The event-level mixed time-ordered product is exactly the fermionic external-order sign times
the composed product of its `4n + 2` atomic creation/annihilation operators. -/
theorem mixedTimeOrderedVertexComp_eq_prodComp_atomicOperators {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ =
      twoPointExternalOrderSign τ τ' •
        Common.prodComp (mixedTimeOrderedAtomicOperators ε i j τ τ' q σ) := by
  rw [mixedTimeOrderedVertexComp, mixedTimeOrderedAtomicOperators,
    prodComp_flatMap_twoPointTimedEventAtomicOperators]

end Fermionic
end SecondQuantization
