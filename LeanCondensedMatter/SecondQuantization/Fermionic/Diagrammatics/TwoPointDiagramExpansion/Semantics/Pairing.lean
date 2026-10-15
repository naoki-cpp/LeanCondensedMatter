import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Flattening
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction

set_option linter.style.header false

/-!
# Mixed-time two-point field families and pairing values

Time-labelled field descriptors and the canonical density-state pair kernel define
one scalar value for each pairing. Reindexing these positions into diagrams is
separate from the physical Gibbs expectation expansion in Integration.DysonCoefficient.
The kernel itself retains its density-state meaning.
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
      ⟨σ v, quarticLocalLegExternalFieldLabel (Common.quarticLocalLeg (q v) l)⟩

omit [LinearOrder Mode] in
private theorem twoPointTimedEventAtomicFields_length {n : ℕ} (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    (twoPointTimedEventAtomicFields i j τ τ' q σ event).length =
      (twoPointTimedEventAtomicLegs event).length := by
  cases event <;> simp [twoPointTimedEventAtomicFields, twoPointTimedEventAtomicLegs]

/-- The complete mixed-time-ordered list of time-labelled atomic fields. -/
noncomputable def mixedTimeOrderedAtomicFields {n : ℕ} (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    List (TimedField Mode) :=
  (orderedTwoPointTimedEvents τ τ' σ).flatMap
    (twoPointTimedEventAtomicFields i j τ τ' q σ)

omit [LinearOrder Mode] in
/-- The descriptor list has exactly the statistics-independent `4n + 2` atomic positions. -/
theorem mixedTimeOrderedAtomicFields_length {n : ℕ} (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicFields i j τ τ' q σ).length = 2 * (2 * n + 1) := by
  have hlen :
      (mixedTimeOrderedAtomicFields i j τ τ' q σ).length =
        (mixedTimeOrderedAtomicLegs τ τ' σ).length := by
    simp only [mixedTimeOrderedAtomicFields, mixedTimeOrderedAtomicLegs,
      List.length_flatMap]
    simp_rw [twoPointTimedEventAtomicFields_length]
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

variable [Fintype Mode]

/-- Canonical free Gibbs density-state contraction of two mixed-time atomic positions. -/
noncomputable def mixedTimeOrderedAtomicPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (a b : Fin (2 * (2 * n + 1))) : ℂ :=
  timedFieldPairContraction ε β
    (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ a)
    (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ b)

/-- Canonical scalar value of one mixed-time pairing through the shared generic evaluator. -/
noncomputable def orderedTwoPointPairingValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Pairing (2 * n + 1)) : ℂ :=
  pairing.evaluation (pairing.weight Common.Statistics.fermion)
    (mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ q)


end Fermionic
end SecondQuantization
