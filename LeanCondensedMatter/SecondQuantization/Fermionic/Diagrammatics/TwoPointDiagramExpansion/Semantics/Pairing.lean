import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Flattening
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Pairing expansion for a two-point insertion

This module applies the finite-temperature Bloch--de Dominicis theorem to the `4n + 2` atomic
operator list constructed by `TwoPointDiagramExpansion.Flattening` and exposes its physical result
through the shared pairing evaluator with a canonical free Gibbs density-state pair kernel.

Finite-Gibbs product formulas remain private coordinate proof infrastructure. Reindexing the pairing
sum into `TwoPointWickDiagram` is intentionally left to the next layer.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode]

/-- A single creation or annihilation field together with its imaginary time. -/
structure TimedField (Mode : Type*) where
  /-- The imaginary time attached to the field. -/
  time : ℝ
  /-- The creation or annihilation label carried by the field. -/
  label : ExternalFieldLabel Mode

/-- The mode carried by an external fermionic field label. -/
def externalFieldLabelMode : ExternalFieldLabel Mode → Mode
  | .annihilation i => i
  | .creation i => i

/-- Whether an external fermionic field label is a creation field. -/
def externalFieldLabelIsCreate : ExternalFieldLabel Mode → Bool
  | .annihilation _ => false
  | .creation _ => true

/-- The bare creation or annihilation operator represented by an external field label. -/
noncomputable def bareExternalFieldOperator :
    ExternalFieldLabel Mode → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode
  | .annihilation i => annihilate i
  | .creation i => create i

/-- The free-evolution eigenvalue shift of an external field label. -/
def externalFieldLabelEnergyShift (ε : Mode → ℝ) : ExternalFieldLabel Mode → ℝ
  | .annihilation i => -ε i
  | .creation i => ε i

/-- A time-labelled field as an evolved linear operator. -/
noncomputable def timedFieldOperator (ε : Mode → ℝ)
    (field : TimedField Mode) : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  externalFieldOperator ε field.time field.label

/-- Every evolved external field is its bare ladder operator times the expected exponential. -/
theorem externalFieldOperator_eq_smul_bare (ε : Mode → ℝ) (τ : ℝ)
    (label : ExternalFieldLabel Mode) :
    externalFieldOperator ε τ label =
      Complex.exp (((τ * externalFieldLabelEnergyShift ε label : ℝ) : ℂ)) •
        bareExternalFieldOperator label := by
  cases label with
  | annihilation i =>
      rw [externalFieldOperator_annihilation_eq_smul]
      change Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i =
        Complex.exp (((τ * -ε i : ℝ) : ℂ)) • annihilate i
      congr 2
      push_cast
      ring
  | creation i =>
      rw [externalFieldOperator_creation_eq_smul]
      change Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i =
        Complex.exp (((τ * ε i : ℝ) : ℂ)) • create i
      congr 2
      push_cast
      ring

/-- The bare fermionic zeta-commutator of two labelled fields is a scalar identity operator. -/
theorem zetaCommutator_bareExternalFieldOperator
    (A B : ExternalFieldLabel Mode) :
    Common.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (bareExternalFieldOperator A) (bareExternalFieldOperator B) =
      (if externalFieldLabelIsCreate A = externalFieldLabelIsCreate B then (0 : ℂ)
       else if externalFieldLabelMode A = externalFieldLabelMode B then 1 else 0) •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  have hbridge :
      Common.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
          (bareExternalFieldOperator A) (bareExternalFieldOperator B) =
        anticomm (bareExternalFieldOperator A) (bareExternalFieldOperator B) :=
    exchangeCommutator_fermion_eq_anticomm _ _
  rw [hbridge]
  cases A <;> cases B <;>
    simp [bareExternalFieldOperator, externalFieldLabelIsCreate, externalFieldLabelMode,
      anticomm_annihilate_annihilate, anticomm_annihilate_create,
      anticomm_create_annihilate, anticomm_create_create] <;>
    split <;> simp_all

/-- The scalar coefficient in the zeta-commutator of two evolved fields. -/
noncomputable def timedFieldCommutatorCoeff (ε : Mode → ℝ)
    (A B : TimedField Mode) : ℂ :=
  Complex.exp (((A.time * externalFieldLabelEnergyShift ε A.label : ℝ) : ℂ)) *
    Complex.exp (((B.time * externalFieldLabelEnergyShift ε B.label : ℝ) : ℂ)) *
    (if externalFieldLabelIsCreate A.label = externalFieldLabelIsCreate B.label then (0 : ℂ)
     else if externalFieldLabelMode A.label = externalFieldLabelMode B.label then 1 else 0)

/-- A time-labelled field has the expected scalar-times-bare normal form. -/
theorem timedFieldOperator_eq_smul (ε : Mode → ℝ) (field : TimedField Mode) :
    timedFieldOperator ε field =
      Complex.exp (((field.time * externalFieldLabelEnergyShift ε field.label : ℝ) : ℂ)) •
        bareExternalFieldOperator field.label :=
  externalFieldOperator_eq_smul_bare ε field.time field.label

/-- Two evolved fields satisfy the scalar zeta-commutator hypothesis. -/
theorem zetaCommutator_timedFieldOperator (ε : Mode → ℝ)
    (A B : TimedField Mode) :
    Common.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (timedFieldOperator ε A) (timedFieldOperator ε B) =
      timedFieldCommutatorCoeff ε A B •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  rw [timedFieldOperator_eq_smul, timedFieldOperator_eq_smul,
    Common.zetaCommutator_smul_smul, zetaCommutator_bareExternalFieldOperator, smul_smul,
    timedFieldCommutatorCoeff]

/-- A time-labelled field remains an eigenoperator after a further evolution by `-β`. -/
theorem heisenbergEvolve_timedFieldOperator (ε : Mode → ℝ) (β : ℝ)
    (field : TimedField Mode) :
    Common.heisenbergEvolve (fermionEnergy ε) (-β) (timedFieldOperator ε field) =
      Complex.exp (((externalFieldLabelEnergyShift ε field.label * (-β) : ℝ) : ℂ)) •
        timedFieldOperator ε field := by
  obtain ⟨τ, label⟩ := field
  cases label with
  | annihilation i =>
      change Common.heisenbergEvolve (fermionEnergy ε) (-β)
          (imaginaryTimeEvolve ε τ (annihilate i)) =
        Complex.exp ((((-ε i) * (-β) : ℝ) : ℂ)) •
          imaginaryTimeEvolve ε τ (annihilate i)
      have step : Common.heisenbergEvolve (fermionEnergy ε) (-β)
          (imaginaryTimeEvolve ε τ (annihilate i)) =
        imaginaryTimeEvolve ε (τ + -β) (annihilate i) :=
        Common.heisenbergEvolve_heisenbergEvolve (fermionEnergy ε) τ (-β) (annihilate i)
      rw [step, imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_annihilate, smul_smul,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring
  | creation i =>
      change Common.heisenbergEvolve (fermionEnergy ε) (-β)
          (imaginaryTimeEvolve ε τ (create i)) =
        Complex.exp ((((ε i) * (-β) : ℝ) : ℂ)) • imaginaryTimeEvolve ε τ (create i)
      have step : Common.heisenbergEvolve (fermionEnergy ε) (-β)
          (imaginaryTimeEvolve ε τ (create i)) =
        imaginaryTimeEvolve ε (τ + -β) (create i) :=
        Common.heisenbergEvolve_heisenbergEvolve (fermionEnergy ε) τ (-β) (create i)
      rw [step, imaginaryTimeEvolve_create, imaginaryTimeEvolve_create, smul_smul,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- View one quartic local leg as an external-style annihilation or creation field label. -/
def quarticLocalLegExternalFieldLabel (q : QuarticVertexLabel Mode) (l : Fin 4) :
    ExternalFieldLabel Mode :=
  if quarticLocalLegIsCreate l then
    .creation (quarticLocalLegMode q l)
  else
    .annihilation (quarticLocalLegMode q l)

@[simp]
theorem bareExternalFieldOperator_quarticLocalLegExternalFieldLabel
    (q : QuarticVertexLabel Mode) (l : Fin 4) :
    bareExternalFieldOperator (quarticLocalLegExternalFieldLabel q l) =
      quarticLocalLegOperator q l := by
  fin_cases l <;>
    simp [quarticLocalLegExternalFieldLabel, quarticLocalLegIsCreate, quarticLocalLegMode,
      bareExternalFieldOperator, quarticLocalLegOperator]

omit [LinearOrder Mode] in
@[simp]
theorem externalFieldLabelEnergyShift_quarticLocalLegExternalFieldLabel
    (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) (l : Fin 4) :
    externalFieldLabelEnergyShift ε (quarticLocalLegExternalFieldLabel q l) =
      quarticLocalLegEnergyShift ε q l := by
  fin_cases l <;>
    simp [quarticLocalLegExternalFieldLabel, quarticLocalLegIsCreate, quarticLocalLegMode,
      externalFieldLabelEnergyShift, quarticLocalLegEnergyShift]

/-- The time-labelled field corresponding to one quartic local leg has the existing local-leg
operator semantics. -/
theorem timedFieldOperator_quarticLocalLeg (ε : Mode → ℝ) (τ : ℝ)
    (q : QuarticVertexLabel Mode) (l : Fin 4) :
    timedFieldOperator ε ⟨τ, quarticLocalLegExternalFieldLabel q l⟩ =
      imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) := by
  rw [timedFieldOperator_eq_smul,
    bareExternalFieldOperator_quarticLocalLegExternalFieldLabel,
    externalFieldLabelEnergyShift_quarticLocalLegExternalFieldLabel,
    imaginaryTimeEvolve_quarticLocalLegOperator]

/-- The field descriptors contributed by one external or quartic interaction event. -/
noncomputable def twoPointTimedEventAtomicFields {n : ℕ} (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → List (TimedField Mode)
  | .inl e => [⟨twoPointExternalTimes τ τ' e, twoPointExternalLabels i j e⟩]
  | .inr v => List.ofFn fun l : Fin 4 =>
      ⟨σ v, quarticLocalLegExternalFieldLabel (q v) l⟩

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

/-- The descriptor list has the same `4n + 2` cardinality as the atomic operator list. -/
theorem mixedTimeOrderedAtomicFields_length {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicFields i j τ τ' q σ).length = 2 * (2 * n + 1) := by
  calc
    (mixedTimeOrderedAtomicFields i j τ τ' q σ).length =
        ((mixedTimeOrderedAtomicFields i j τ τ' q σ).map (timedFieldOperator ε)).length := by simp
    _ = (mixedTimeOrderedAtomicOperators ε i j τ τ' q σ).length :=
      congrArg List.length
        (map_timedFieldOperator_mixedTimeOrderedAtomicFields ε i j τ τ' q σ)
    _ = 2 * (2 * n + 1) := mixedTimeOrderedAtomicOperators_length ε i j τ τ' q σ

/-- The `Fin (4n + 2)`-indexed time-labelled field family underlying the mixed operator list. -/
noncomputable def mixedTimeOrderedAtomicFieldFamily {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) → TimedField Mode :=
  fun p => (mixedTimeOrderedAtomicFields i j τ τ' q σ).get
    (Fin.cast (mixedTimeOrderedAtomicFields_length ε i j τ τ' q σ).symm p)

/-- The corresponding `Fin (4n + 2)`-indexed atomic operator family. -/
noncomputable def mixedTimeOrderedAtomicOperatorFamily {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  fun p => timedFieldOperator ε (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ p)

/-- The eigenvalue-shift family used by the general pairing theorem. -/
noncomputable def mixedTimeOrderedAtomicEnergyShift {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) → ℝ :=
  fun p => externalFieldLabelEnergyShift ε
    (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ p).label

/-- The scalar zeta-commutator coefficient family used by the general pairing theorem. -/
noncomputable def mixedTimeOrderedAtomicCommutatorCoeff {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) → Fin (2 * (2 * n + 1)) → ℂ :=
  fun a b => timedFieldCommutatorCoeff ε
    (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ a)
    (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ b)

/-- Rebuilding the descriptor list from its fixed-cardinality family recovers the original list. -/
private theorem ofFn_mixedTimeOrderedAtomicFieldFamily_eq {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    List.ofFn (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ) =
      mixedTimeOrderedAtomicFields i j τ τ' q σ := by
  let l := mixedTimeOrderedAtomicFields i j τ τ' q σ
  have h : l.length = 2 * (2 * n + 1) :=
    mixedTimeOrderedAtomicFields_length ε i j τ τ' q σ
  simpa [mixedTimeOrderedAtomicFieldFamily, l] using
    (List.ofFn_congr h l.get).symm.trans (List.ofFn_get l)

/-- Rebuilding the operator list from its fixed-cardinality family recovers the flattened list. -/
private theorem ofFn_mixedTimeOrderedAtomicOperatorFamily_eq {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    List.ofFn (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ) =
      mixedTimeOrderedAtomicOperators ε i j τ τ' q σ := by
  change List.ofFn (fun p => timedFieldOperator ε
    (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ p)) = _
  rw [List.ofFn_comp', ofFn_mixedTimeOrderedAtomicFieldFamily_eq,
    map_timedFieldOperator_mixedTimeOrderedAtomicFields]

/-- Every member of the mixed atomic family satisfies the general theorem's eigenoperator
hypothesis. -/
private theorem heisenbergEvolve_mixedTimeOrderedAtomicOperatorFamily {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + 1))) :
    Common.heisenbergEvolve (fermionEnergy ε) (-β)
        (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ p) =
      Complex.exp (((mixedTimeOrderedAtomicEnergyShift ε i j τ τ' q σ p * (-β) : ℝ) : ℂ)) •
        mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ p :=
  heisenbergEvolve_timedFieldOperator ε β
    (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ p)

/-- Every pair of members of the mixed atomic family satisfies the scalar zeta-commutator
hypothesis. -/
private theorem zetaCommutator_mixedTimeOrderedAtomicOperatorFamily {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (a b : Fin (2 * (2 * n + 1))) :
    Common.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ a)
        (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ b) =
      mixedTimeOrderedAtomicCommutatorCoeff ε i j τ τ' q σ a b •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :=
  zetaCommutator_timedFieldOperator ε
    (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ a)
    (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ b)

variable [Fintype Mode]

/-- Canonical free Gibbs density-state contraction of two mixed-time atomic positions. -/
noncomputable def mixedTimeOrderedAtomicPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (a b : Fin (2 * (2 * n + 1))) : ℂ :=
  (freeGibbsDensityOperator ε β).expectation
    (Common.finiteHilbertOperator
      ((mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ a).comp
        (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ b)))

/-- Canonical scalar value of one mixed-time pairing through the shared generic evaluator. -/
noncomputable def orderedTwoPointPairingValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Pairing (2 * n + 1)) : ℂ :=
  pairing.evaluation (pairing.weight Common.Statistics.fermion)
    (mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ q)

private theorem finiteGibbsExpectation_prodComp_mixedTimeOrderedAtomicOperators_eq_sum_pairing
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β
        (Common.prodComp (mixedTimeOrderedAtomicOperators ε i j τ τ' q σ)) =
      ∑ pairing : Pairing (2 * n + 1),
        pairing.weight Common.Statistics.fermion *
          ∏ pr ∈ pairing.pairs,
            Common.finiteGibbsExpectation (fermionEnergy ε) β
              ((mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ pr.1).comp
                (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ pr.2)) := by
  have hgen :=
    Common.BlochDeDominicis.finiteGibbsExpectation_prodComp_eq_sum_pairing
      Common.Statistics.fermion (fermionEnergy ε) β
      (traceFock_diagonalEvolution_fermionEnergy_ne_zero ε β) (2 * n + 1)
      (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ)
      (mixedTimeOrderedAtomicEnergyShift ε i j τ τ' q σ)
      (mixedTimeOrderedAtomicCommutatorCoeff ε i j τ τ' q σ)
      (fun p => heisenbergEvolve_mixedTimeOrderedAtomicOperatorFamily ε β i j τ τ' q σ p)
      (fun a b _ => zetaCommutator_mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ a b)
      (fun p => one_sub_zetaInt_fermion_mul_exp_ne_zero
        (mixedTimeOrderedAtomicEnergyShift ε i j τ τ' q σ p) β)
  rw [← ofFn_mixedTimeOrderedAtomicOperatorFamily_eq]
  exact hgen

private theorem finiteGibbsExpectation_mixedTimeOrderedVertexComp_eq_sum_pairing
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β
        (mixedTimeOrderedVertexComp ε i j τ τ' q σ) =
      twoPointExternalOrderSign τ τ' *
        ∑ pairing : Pairing (2 * n + 1),
          pairing.weight Common.Statistics.fermion *
            ∏ pr ∈ pairing.pairs,
              Common.finiteGibbsExpectation (fermionEnergy ε) β
                ((mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ pr.1).comp
                  (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ pr.2)) := by
  rw [mixedTimeOrderedVertexComp_eq_prodComp_atomicOperators,
    Common.finiteGibbsExpectation_smul,
    finiteGibbsExpectation_prodComp_mixedTimeOrderedAtomicOperators_eq_sum_pairing]

/-- The mixed event-level density-state expectation is the external-order sign times the sum of
canonical pairing evaluations. -/
theorem freeGibbsDensityOperator_expectation_mixedTimeOrderedVertexComp_eq_sum_pairingValue
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (mixedTimeOrderedVertexComp ε i j τ τ' q σ)) =
      twoPointExternalOrderSign τ τ' *
        ∑ pairing : Pairing (2 * n + 1),
          orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
  simpa only [orderedTwoPointPairingValue, Combinatorics.Pairing.evaluation,
    mixedTimeOrderedAtomicPairValue,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
      finiteGibbsExpectation_mixedTimeOrderedVertexComp_eq_sum_pairing
        ε β i j τ τ' q σ

end Fermionic
end SecondQuantization
