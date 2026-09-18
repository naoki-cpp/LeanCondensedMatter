import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Flattening
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Pairing expansion for a two-point insertion

This module applies the finite-temperature Bloch--de Dominicis theorem to the `4n + 2` atomic
operator list constructed by `TwoPointDiagramExpansion.Flattening` and exposes its physical result
through the shared pairing evaluator with a canonical free Gibbs density-state pair kernel. Generic
time-labelled external-field semantics are owned by `Fermionic.ImaginaryTime.TimedField`.

Finite-Gibbs product formulas stay local to the physical endpoint proof. Reindexing the pairing sum
into `TwoPointWickDiagram` is intentionally left to the next layer.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode]

/-- The field descriptors contributed by one external or quartic interaction event. -/
noncomputable def twoPointTimedEventAtomicFields {n : ℕ} (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → List (TimedField Mode)
  | .inl e => [⟨twoPointExternalTimes τ τ' e, twoPointExternalLabels i j e⟩]
  | .inr v => List.ofFn fun l : Fin 4 =>
      ⟨σ v, quarticLocalLegExternalFieldLabel (q v) l⟩

private theorem twoPointTimedEventAtomicFields_length {n : ℕ} (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    (twoPointTimedEventAtomicFields i j τ τ' q σ event).length =
      (twoPointTimedEventAtomicLegs event).length := by
  cases event <;> simp [twoPointTimedEventAtomicFields, twoPointTimedEventAtomicLegs]

/-- Mapping one event's field descriptors to operators recovers its atomic operator list. -/
private theorem map_timedFieldOperator_twoPointTimedEventAtomicFields {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    (twoPointTimedEventAtomicFields i j τ τ' q σ event).map (timedFieldOperator ε) =
      twoPointTimedEventAtomicOperators ε i j τ τ' q σ event := by
  cases event with
  | inl e =>
      simp [twoPointTimedEventAtomicFields, timedFieldOperator]
  | inr v =>
      rw [twoPointTimedEventAtomicFields, twoPointTimedEventAtomicOperators_interaction,
        List.map_ofFn]
      exact congrArg List.ofFn (funext fun l => by
        simpa [Function.comp_def] using timedFieldOperator_quarticLocalLeg ε (σ v) (q v) l)

/-- The complete mixed-time-ordered list of time-labelled atomic fields. -/
noncomputable def mixedTimeOrderedAtomicFields {n : ℕ} (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    List (TimedField Mode) :=
  (orderedTwoPointTimedEvents τ τ' σ).flatMap
    (twoPointTimedEventAtomicFields i j τ τ' q σ)

/-- Mapping all mixed-time-ordered field descriptors to operators recovers the atomic operator list. -/
private theorem map_timedFieldOperator_mixedTimeOrderedAtomicFields {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicFields i j τ τ' q σ).map (timedFieldOperator ε) =
      mixedTimeOrderedAtomicOperators ε i j τ τ' q σ := by
  rw [mixedTimeOrderedAtomicFields, mixedTimeOrderedAtomicOperators]
  induction orderedTwoPointTimedEvents τ τ' σ with
  | nil => rfl
  | cons event events ih =>
      rw [List.flatMap_cons, List.map_append, List.flatMap_cons,
        map_timedFieldOperator_twoPointTimedEventAtomicFields, ih]

/-- The descriptor list has exactly the statistics-independent `4n + 2` atomic positions. -/
theorem mixedTimeOrderedAtomicFields_length {n : ℕ} (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicFields i j τ τ' q σ).length = 2 * (2 * n + 1) := by
  have hlen :
      (mixedTimeOrderedAtomicFields i j τ τ' q σ).length =
        (mixedTimeOrderedAtomicLegs τ τ' σ).length := by
    unfold mixedTimeOrderedAtomicFields mixedTimeOrderedAtomicLegs
    induction orderedTwoPointTimedEvents τ τ' σ with
    | nil => rfl
    | cons event events ih =>
        rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append,
          twoPointTimedEventAtomicFields_length, ih]
  rw [hlen, mixedTimeOrderedAtomicLegs_length]

/-- The `Fin (4n + 2)`-indexed time-labelled field family underlying the mixed operator list. -/
noncomputable def mixedTimeOrderedAtomicFieldFamily {n : ℕ} (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) → TimedField Mode :=
  fun p => (mixedTimeOrderedAtomicFields i j τ τ' q σ).get
    (Fin.cast (mixedTimeOrderedAtomicFields_length i j τ τ' q σ).symm p)

/-- The corresponding `Fin (4n + 2)`-indexed atomic operator family. -/
noncomputable def mixedTimeOrderedAtomicOperatorFamily {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  fun p => timedFieldOperator ε (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ p)

/-- The eigenvalue-shift family used by the general pairing theorem. -/
noncomputable def mixedTimeOrderedAtomicEnergyShift {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) → ℝ :=
  fun p => externalFieldLabelEnergyShift ε
    (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ p).label

/-- The scalar zeta-commutator coefficient family used by the general pairing theorem. -/
noncomputable def mixedTimeOrderedAtomicCommutatorCoeff {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) → Fin (2 * (2 * n + 1)) → ℂ :=
  fun a b => timedFieldCommutatorCoeff ε
    (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ a)
    (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ b)

/-- Rebuilding the descriptor list from its fixed-cardinality family recovers the original list. -/
private theorem ofFn_mixedTimeOrderedAtomicFieldFamily_eq {n : ℕ}
    (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    List.ofFn (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ) =
      mixedTimeOrderedAtomicFields i j τ τ' q σ := by
  let l := mixedTimeOrderedAtomicFields i j τ τ' q σ
  have h : l.length = 2 * (2 * n + 1) :=
    mixedTimeOrderedAtomicFields_length i j τ τ' q σ
  simpa [mixedTimeOrderedAtomicFieldFamily, l] using
    (List.ofFn_congr h l.get).symm.trans (List.ofFn_get l)

/-- Rebuilding the operator list from its fixed-cardinality family recovers the flattened list. -/
private theorem ofFn_mixedTimeOrderedAtomicOperatorFamily_eq {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    List.ofFn (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ) =
      mixedTimeOrderedAtomicOperators ε i j τ τ' q σ := by
  change List.ofFn (fun p => timedFieldOperator ε
    (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ p)) = _
  rw [List.ofFn_comp', ofFn_mixedTimeOrderedAtomicFieldFamily_eq,
    map_timedFieldOperator_mixedTimeOrderedAtomicFields]

variable [Fintype Mode]

/-- Canonical free Gibbs density-state contraction of two mixed-time atomic positions. -/
noncomputable def mixedTimeOrderedAtomicPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (a b : Fin (2 * (2 * n + 1))) : ℂ :=
  (freeGibbsDensityOperator ε β).expectation
    (Common.finiteHilbertOperatorAlgEquiv
      ((mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ a).comp
        (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ b)))

/-- Canonical scalar value of one mixed-time pairing through the shared generic evaluator. -/
noncomputable def orderedTwoPointPairingValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Pairing (2 * n + 1)) : ℂ :=
  pairing.evaluation (pairing.weight Common.Statistics.fermion)
    (mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ q)

/-- The mixed event-level density-state expectation is the external-order sign times the sum of
canonical pairing evaluations. -/
theorem freeGibbsDensityOperator_expectation_mixedTimeOrderedVertexComp_eq_sum_pairingValue
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv (mixedTimeOrderedVertexComp ε i j τ τ' q σ)) =
      twoPointExternalOrderSign τ τ' *
        ∑ pairing : Pairing (2 * n + 1),
          orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    mixedTimeOrderedVertexComp_eq_prodComp_atomicOperators,
    Common.finiteGibbsExpectation_smul]
  have hgen :=
    Common.BlochDeDominicis.finiteGibbsExpectation_prodComp_eq_sum_pairing
      Common.Statistics.fermion (fermionEnergy ε) β (2 * n + 1)
      (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ)
      (mixedTimeOrderedAtomicEnergyShift ε i j τ τ' q σ)
      (mixedTimeOrderedAtomicCommutatorCoeff ε i j τ τ' q σ)
      (fun p => heisenbergEvolve_timedFieldOperator ε β
        (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ p))
      (fun a b _ => zetaCommutator_timedFieldOperator ε
        (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ a)
        (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ b))
      (fun p => one_sub_zetaInt_fermion_mul_exp_ne_zero
        (mixedTimeOrderedAtomicEnergyShift ε i j τ τ' q σ p) β)
  rw [ofFn_mixedTimeOrderedAtomicOperatorFamily_eq] at hgen
  rw [hgen]
  simp only [orderedTwoPointPairingValue, Combinatorics.Pairing.evaluation,
    mixedTimeOrderedAtomicPairValue,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]

end Fermionic
end SecondQuantization
