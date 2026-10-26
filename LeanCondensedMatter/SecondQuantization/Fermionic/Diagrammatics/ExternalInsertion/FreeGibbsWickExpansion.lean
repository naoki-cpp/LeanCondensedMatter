import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator

set_option linter.style.header false

/-!
# Free-Gibbs Wick expansion for fixed external insertions

The mixed-time atomic product of free fermionic field operators has the same
finite-temperature Gibbs expectation as the full pairing sum entering the
fixed-external Wick diagrams. The mixed-order fermionic sign and the quartic
vertex weights are kept explicit; the Dyson sign and time integration are
separate downstream operations.

The state is the normalized *free* Gibbs state, not the interacting Gibbs state.
This is a pointwise statement about the mixed-time atomic operator product,
not yet an identification with a separately constructed time-ordered product
of quartic interaction operators.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Reindex a fixed-external diagram by its interaction-label sequence and its
pairing in the actual mixed-time atomic field order. -/
private noncomputable def fixedExternalInsertionWickDiagramEquivMixedData
    {E n : ℕ} (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    FixedExternalInsertionWickDiagram Mode E n externalLabel ≃
      (Fin n → QuarticVertexLabel Mode) × Pairing (2 * n + E) where
  toFun d := (d.1.vertexLabelSequence, d.1.pairingInMixedOrder externalTime σ)
  invFun x :=
    ⟨{
      externalLabel := externalLabel
      vertexLabel := fun v => x.1 v.1
      pairing := x.2.transport
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    }, rfl⟩
  left_inv d := by
    apply Subtype.ext
    apply ExternalInsertionDiagram.ext
    · exact d.2.symm
    · funext _
      rfl
    · change (d.1.pairing.transport
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ)).transport
          (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm =
            d.1.pairing
      exact PairingOn.transport_symm_transport _ _
  right_inv x := by
    obtain ⟨labels, pairing⟩ := x
    apply Prod.ext
    · funext _
      rfl
    · change (pairing.transport
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm).transport
          (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ) = pairing
      exact PairingOn.transport_transport_symm _ _

/-- The fixed-external Wick-diagram sum is the vertex-weighted free-Gibbs
expectation of the mixed-time atomic operator product, with the fermionic
permutation sign restoring the canonical external/interaction leg order. -/
theorem sum_fixedExternalInsertionWickDiagram_fixedTimeAmplitude_eq_mixedAtomicExpectation
    {E n : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (∑ d : FixedExternalInsertionWickDiagram Mode E n externalLabel,
      d.1.fixedTimeAmplitude ε β g externalTime σ) =
      externalInsertionMixedAtomicOrderSign externalTime σ *
        ∑ q : Fin n → QuarticVertexLabel Mode,
          (∏ i : Fin n, g (q i)) *
            (freeGibbsDensityOperator ε β).expectation
              (Common.finiteHilbertOperatorAlgEquiv
                (List.prod (List.ofFn (fun p : Fin (2 * (2 * n + E)) =>
                  timedFieldOperator ε
                    (externalInsertionMixedTimeOrderedAtomicFieldFamily
                      externalLabel externalTime q σ p))))) := by
  classical
  let e := fixedExternalInsertionWickDiagramEquivMixedData
    (Mode := Mode) externalLabel externalTime σ
  let sign := externalInsertionMixedAtomicOrderSign externalTime σ
  let F : ((Fin n → QuarticVertexLabel Mode) × Pairing (2 * n + E)) → ℂ :=
    fun x => sign * (∏ i : Fin n, g (x.1 i)) *
      x.2.evaluation (x.2.weight Common.Statistics.fermion)
        (externalInsertionMixedTimeOrderedAtomicPairValue ε β
          externalLabel externalTime x.1 σ)
  have hreindex :
      (∑ d : FixedExternalInsertionWickDiagram Mode E n externalLabel,
        d.1.fixedTimeAmplitude ε β g externalTime σ) =
        ∑ x : (Fin n → QuarticVertexLabel Mode) × Pairing (2 * n + E), F x := by
    calc
      _ = ∑ d : FixedExternalInsertionWickDiagram Mode E n externalLabel,
          F (e d) := by
        apply Finset.sum_congr rfl
        intro d _
        change
          sign * d.1.vertexWeight g *
            (d.1.pairingInMixedOrder externalTime σ).evaluation
              ((d.1.pairingInMixedOrder externalTime σ).weight Common.Statistics.fermion)
              (externalInsertionMixedTimeOrderedAtomicPairValue ε β
                d.1.externalLabel externalTime d.1.vertexLabelSequence σ) =
          sign * (∏ i : Fin n, g (d.1.vertexLabelSequence i)) *
            (d.1.pairingInMixedOrder externalTime σ).evaluation
              ((d.1.pairingInMixedOrder externalTime σ).weight Common.Statistics.fermion)
              (externalInsertionMixedTimeOrderedAtomicPairValue ε β
                externalLabel externalTime d.1.vertexLabelSequence σ)
        have hweight :
            d.1.vertexWeight g = ∏ i : Fin n, g (d.1.vertexLabelSequence i) := by
          change
            (∏ v : ↥(Finset.univ : Finset (Fin n)), g (d.1.vertexLabel v)) =
              ∏ i : Fin n, g (d.1.vertexLabel ⟨i, Finset.mem_univ i⟩)
          let e : Fin n ≃ ↥(Finset.univ : Finset (Fin n)) :=
            (Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)).symm
          exact (Equiv.prod_comp e (fun v => g (d.1.vertexLabel v))).symm
        rw [hweight, d.2]
      _ = _ := Equiv.sum_comp e F
  have hwick (q : Fin n → QuarticVertexLabel Mode) :
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv
          (List.prod (List.ofFn (fun p : Fin (2 * (2 * n + E)) =>
            timedFieldOperator ε
              (externalInsertionMixedTimeOrderedAtomicFieldFamily
                externalLabel externalTime q σ p))))) =
        ∑ pairing : Pairing (2 * n + E),
          pairing.evaluation (pairing.weight Common.Statistics.fermion)
            (externalInsertionMixedTimeOrderedAtomicPairValue ε β
              externalLabel externalTime q σ) := by
    have henergy : (fun i : Mode => ε i - (0 : ℝ)) = ε := by
      funext i
      simp
    have hgen := grandCanonicalGibbsExpectation_prod_timedFieldOperator_eq_sum_pairing
      ε β 0 (2 * n + E)
      (externalInsertionMixedTimeOrderedAtomicFieldFamily externalLabel externalTime q σ)
    rw [henergy] at hgen
    have hpair (A B : TimedField Mode) :
        Common.finiteGibbsExpectation (fermionEnergy ε) β
          ((timedFieldOperator ε A).comp (timedFieldOperator ε B)) =
        grandCanonicalTimedFieldPairContraction ε β 0 A B := by
      simp only [grandCanonicalTimedFieldPairContraction,
        freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]
    simp_rw [hpair] at hgen
    exact hgen
  calc
    _ = ∑ x : (Fin n → QuarticVertexLabel Mode) × Pairing (2 * n + E), F x :=
      hreindex
    _ = ∑ q : Fin n → QuarticVertexLabel Mode,
        ∑ pairing : Pairing (2 * n + E), F (q, pairing) :=
      Fintype.sum_prod_type _
    _ = sign * ∑ q : Fin n → QuarticVertexLabel Mode,
          (∏ i : Fin n, g (q i)) *
            ∑ pairing : Pairing (2 * n + E),
              pairing.evaluation (pairing.weight Common.Statistics.fermion)
                (externalInsertionMixedTimeOrderedAtomicPairValue ε β
                  externalLabel externalTime q σ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      simp only [F]
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    _ = _ := by
      apply congrArg (fun z : ℂ => sign * z)
      apply Finset.sum_congr rfl
      intro q _
      rw [hwick q]

end Fermionic
end SecondQuantization
