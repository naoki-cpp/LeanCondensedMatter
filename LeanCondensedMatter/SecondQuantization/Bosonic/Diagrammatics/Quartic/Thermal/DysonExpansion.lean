import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.Amplitude
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsBoundary
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticDysonExpansion
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcreteExpectationRecursion

set_option linter.style.header false

/-!
# Bosonic quartic Dyson-to-Wick bridge

The physical finite-order Dyson coefficient of a finitely supported quartic interaction is already a
finite sum of bare vertex-sequence operators with scalar ordered-simplex coefficients. The bosonic
thermal-field bridge identifies each bare vertex-sequence operator with an ordered product of free
thermal fields, whose convergence-aware Gibbs expectation has the concrete Bloch--de Dominicis
pairing expansion.

This file composes those existing boundaries. The ordered-simplex time integration remains entirely
inside `Common.quarticDysonSequenceCoeff`; no separate timed-diagram representation is introduced.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*} [Finite Mode]

/-- File-local classical equality matches the concrete free-thermal pair kernel. -/
local instance instDecidableEqQuarticDysonExpansion : DecidableEq Mode := Classical.decEq Mode

/-- The convergence-aware Gibbs expectation of a finite-order quartic Dyson coefficient is a finite
sum over support-valued vertex sequences and bosonic pairings. The scalar
`quarticDysonSequenceCoeff` carries the full ordered-simplex imaginary-time integration, while the
pairing evaluation is the existing static free-boson thermal Wick factor. -/
theorem freeGibbsDysonCoeff_quarticInteractionOn_eq_sum_pairingEvaluation
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (t : ℝ) :
    freeGibbsDysonCoeff ε β (quarticInteractionOn support g) n t =
      ∑ q : Fin n → ↥support,
        Common.quarticDysonSequenceCoeff ε g
            (fun i => (q i : QuarticVertexLabel Mode)) t *
          ∑ pairing : Pairing (2 * n),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily
                    (fun i => (q i : QuarticVertexLabel Mode)) a)
                  (quarticFreeThermalFieldFamily
                    (fun i => (q i : QuarticVertexLabel Mode)) b)) := by
  letI := Fintype.ofFinite Mode
  classical
  rw [freeGibbsDysonCoeff, dysonCoeff_quarticInteractionOn_eq_sum support ε g n t]
  have hsumm : ∀ q : Fin n → ↥support,
      freeGibbsSummable ε β
        (Common.quarticDysonSequenceCoeff ε g
            (fun i => (q i : QuarticVertexLabel Mode)) t •
          Common.quarticVertexSequenceOperator create annihilate
            (fun i => (q i : QuarticVertexLabel Mode))) := by
    intro q
    apply freeGibbsSummable_smul
    rw [← quarticFreeThermalOrderedProduct_eq_quarticVertexSequenceOperator]
    exact FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos _
  rw [freeGibbsExpectation_sum_of_summable ε β _ hsumm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [freeGibbsExpectation_smul]
  rw [← quarticFreeThermalOrderedProduct_eq_quarticVertexSequenceOperator,
    quarticFreeThermalOrderedProduct]
  have hwick := freeGibbsExpectation_eq_sum_pairing_concrete ε β hpos
    (2 * n) (quarticFreeThermalFieldFamily
      (fun i => (q i : QuarticVertexLabel Mode)))
  simpa only [Pairing.evaluation] using congrArg
    (fun z => Common.quarticDysonSequenceCoeff ε g
      (fun i => (q i : QuarticVertexLabel Mode)) t * z) hwick


/-- Fixed-order physical quartic Dyson diagram amplitude. The scalar Dyson sequence coefficient
contains the ordered-simplex time integration and coupling product, while the diagram contributes
one concrete bosonic thermal pairing value in the same vertex order. -/
noncomputable def QuarticDiagram.orderedDysonThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) (t : ℝ) : ℂ :=
  Common.quarticDysonSequenceCoeff ε g (fun i => d.vertexLabel (order i)) t *
    QuarticDiagram.orderedThermalPairingValue ε β d order

private theorem freeGibbsDysonCoeff_quarticInteraction_eq_sum_pairingEvaluation [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (t : ℝ) :
    freeGibbsDysonCoeff ε β (quarticInteraction g) n t =
      ∑ q : Fin n → QuarticVertexLabel Mode,
        Common.quarticDysonSequenceCoeff ε g q t *
          ∑ pairing : Pairing (2 * n),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily q a)
                  (quarticFreeThermalFieldFamily q b)) := by
  let e :
      (Fin n → ↥(Finset.univ : Finset (QuarticVertexLabel Mode))) ≃
        (Fin n → QuarticVertexLabel Mode) :=
    { toFun := fun q i => q i
      invFun := fun q i => ⟨q i, Finset.mem_univ _⟩
      left_inv := by
        intro q
        funext i
        apply Subtype.ext
        rfl
      right_inv := by
        intro q
        rfl }
  let F : (Fin n → QuarticVertexLabel Mode) → ℂ := fun q =>
    Common.quarticDysonSequenceCoeff ε g q t *
      ∑ pairing : Pairing (2 * n),
        pairing.evaluation (pairing.weight .boson)
          (fun a b =>
            freeThermalPairValue ε β
              (quarticFreeThermalFieldFamily q a)
              (quarticFreeThermalFieldFamily q b))
  have h := freeGibbsDysonCoeff_quarticInteractionOn_eq_sum_pairingEvaluation
    (support := (Finset.univ : Finset (QuarticVertexLabel Mode))) ε β hpos g n t
  calc
    freeGibbsDysonCoeff ε β (quarticInteraction g) n t =
        freeGibbsDysonCoeff ε β
          (quarticInteractionOn (Finset.univ : Finset (QuarticVertexLabel Mode)) g) n t := by
            rfl
    _ = ∑ q : Fin n → ↥(Finset.univ : Finset (QuarticVertexLabel Mode)),
        Common.quarticDysonSequenceCoeff ε g
            (fun i => (q i : QuarticVertexLabel Mode)) t *
          ∑ pairing : Pairing (2 * n),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily
                    (fun i => (q i : QuarticVertexLabel Mode)) a)
                  (quarticFreeThermalFieldFamily
                    (fun i => (q i : QuarticVertexLabel Mode)) b)) := h
    _ = ∑ q : Fin n → ↥(Finset.univ : Finset (QuarticVertexLabel Mode)), F (e q) := by
      apply Finset.sum_congr rfl
      intro q _
      rfl
    _ = ∑ q : Fin n → QuarticVertexLabel Mode, F q := Equiv.sum_comp e F
    _ = ∑ q : Fin n → QuarticVertexLabel Mode,
        Common.quarticDysonSequenceCoeff ε g q t *
          ∑ pairing : Pairing (2 * n),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily q a)
                  (quarticFreeThermalFieldFamily q b)) := rfl

/-- The physical finite-order bosonic quartic Dyson coefficient is the sum of fixed-order physical
quartic diagram amplitudes. This is the canonical reindexing of the concrete
`vertex sequence × pairing` expansion through `Common.quarticDiagramEquivOrderedData`. -/
theorem freeGibbsDysonCoeff_quarticInteraction_eq_sum_orderedDysonThermalAmplitude [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} (S : Finset (Fin N))
    (order : Common.QuarticVertexOrder S) (t : ℝ) :
    freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t =
      ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
  classical
  rw [freeGibbsDysonCoeff_quarticInteraction_eq_sum_pairingEvaluation ε β hpos g S.card t]
  let F : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card → ℂ := fun x =>
    Common.quarticDysonSequenceCoeff ε g x.1 t *
      x.2.evaluation (x.2.weight .boson)
        (fun a b =>
          freeThermalPairValue ε β
            (quarticFreeThermalFieldFamily x.1 a)
            (quarticFreeThermalFieldFamily x.1 b))
  calc
    (∑ q : Fin S.card → QuarticVertexLabel Mode,
        Common.quarticDysonSequenceCoeff ε g q t *
          ∑ pairing : Pairing (2 * S.card),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily q a)
                  (quarticFreeThermalFieldFamily q b))) =
      ∑ q : Fin S.card → QuarticVertexLabel Mode,
        ∑ pairing : Pairing (2 * S.card),
          Common.quarticDysonSequenceCoeff ε g q t *
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily q a)
                  (quarticFreeThermalFieldFamily q b)) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.mul_sum]
    _ = ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card, F x := by
      rw [Fintype.sum_prod_type]
    _ = ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        F (Common.quarticDiagramEquivOrderedData order d) :=
      (Common.sum_quarticDiagram_eq_sum_orderedData order F).symm
    _ = ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
      apply Finset.sum_congr rfl
      intro d _
      rfl


/-- Order-averaged physical bosonic quartic Dyson diagram amplitude. Averaging removes the arbitrary
choice of a global vertex enumeration while preserving the physical Dyson coefficient. -/
noncomputable def QuarticDiagram.dysonThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S) (t : ℝ) : ℂ :=
  (S.card.factorial : ℂ)⁻¹ *
    ∑ order : Common.QuarticVertexOrder S,
      QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t

/-- The convergence-aware physical bosonic quartic Dyson coefficient is exactly the total
order-averaged physical quartic-diagram weight. -/
theorem freeGibbsDysonCoeff_quarticInteraction_eq_sum_dysonThermalAmplitude [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} (S : Finset (Fin N)) (t : ℝ) :
    freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t =
      ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.dysonThermalAmplitude ε β g d t := by
  classical
  symm
  calc
    (∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.dysonThermalAmplitude ε β g d t) =
      ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        (S.card.factorial : ℂ)⁻¹ *
          ∑ order : Common.QuarticVertexOrder S,
            QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := rfl
    _ = (S.card.factorial : ℂ)⁻¹ *
        ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
          ∑ order : Common.QuarticVertexOrder S,
            QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
      rw [Finset.mul_sum]
    _ = (S.card.factorial : ℂ)⁻¹ *
        ∑ order : Common.QuarticVertexOrder S,
          ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
            QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
      rw [Finset.sum_comm]
    _ = (S.card.factorial : ℂ)⁻¹ *
        ∑ _order : Common.QuarticVertexOrder S,
          freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t := by
      congr 1
      apply Finset.sum_congr rfl
      intro order _
      exact
        (freeGibbsDysonCoeff_quarticInteraction_eq_sum_orderedDysonThermalAmplitude
          ε β hpos g S order t).symm
    _ = (S.card.factorial : ℂ)⁻¹ * (S.card.factorial : ℂ) *
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t := by
      rw [Finset.sum_const, Finset.card_univ, Common.card_quarticVertexOrder]
      simp [nsmul_eq_mul]
    _ = freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t := by
      have hfac : (S.card.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero S.card
      rw [← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

end
end Bosonic
end SecondQuantization
