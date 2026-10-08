import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.Amplitude
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsSeries
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticDysonExpansion
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcreteExpectationRecursion

set_option linter.style.header false

/-!
# Bosonic Dyson-to-Wick pairing and diagram expansion

Convergence-aware Gibbs expectation of finite quartic Dyson coefficients is expanded into
free-thermal pairings and reindexed as ordered quartic diagrams. The scalar
`Common.quarticDysonSequenceCoeff` already includes ordered-simplex integration.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*} [Finite Mode]

/-- File-local classical equality matches the concrete free-thermal pair kernel. -/
local instance instDecidableEqQuarticDysonExpansion : DecidableEq Mode := Classical.decEq Mode

/-- Every finite bare quartic vertex sequence has a summable free-Gibbs numerator under the
positive one-mode Boltzmann hypothesis. -/
theorem quarticVertexSequenceOperator_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    {n : ℕ} (q : Fin n → QuarticVertexLabel Mode) :
    Common.quarticVertexSequenceOperator create annihilate q ∈
      freeGibbsDomain ε β := by
  letI := Fintype.ofFinite Mode
  rw [mem_freeGibbsDomain_iff, ← quarticFreeThermalOrderedProduct_eq_quarticVertexSequenceOperator]
  exact FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos _

/-- Every finite Dyson coefficient of a finitely supported quartic interaction belongs to the
free-Gibbs domain. This is proved coefficientwise from the finite vertex-sequence expansion and does
not exchange the infinite Gibbs sum with the recursive Dyson integral. -/
theorem dysonCoeff_quarticInteractionOn_mem_freeGibbsDomain
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (t : ℝ) :
    Common.dysonCoeff (freeEigenvalue ε) (quarticInteractionOn support g) n t ∈
      freeGibbsDomain ε β := by
  letI := Fintype.ofFinite Mode
  classical
  rw [dysonCoeff_quarticInteractionOn_eq_sum support ε g n t]
  exact Submodule.sum_mem (freeGibbsDomain ε β) fun q _ =>
    (freeGibbsDomain ε β).smul_mem _
      (quarticVertexSequenceOperator_mem_freeGibbsDomain ε β hpos
        (fun i => (q i : QuarticVertexLabel Mode)))

omit [Finite Mode] in
/-- On a finite mode type, every finite Dyson coefficient of the full quartic interaction belongs to
the free-Gibbs domain. -/
theorem dysonCoeff_quarticInteraction_mem_freeGibbsDomain [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (t : ℝ) :
    Common.dysonCoeff (freeEigenvalue ε) (quarticInteraction g) n t ∈
      freeGibbsDomain ε β := by
  classical
  rw [dysonCoeff_quarticInteraction_eq_sum ε g n t]
  exact Submodule.sum_mem (freeGibbsDomain ε β) fun q _ =>
    (freeGibbsDomain ε β).smul_mem _
      (quarticVertexSequenceOperator_mem_freeGibbsDomain ε β hpos q)

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

omit [Finite Mode] in
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
  classical
  rw [freeGibbsDysonCoeff, dysonCoeff_quarticInteraction_eq_sum ε g n t]
  have hsumm : ∀ q : Fin n → QuarticVertexLabel Mode,
      freeGibbsSummable ε β
        (Common.quarticDysonSequenceCoeff ε g q t •
          Common.quarticVertexSequenceOperator create annihilate q) := by
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
    (2 * n) (quarticFreeThermalFieldFamily q)
  simpa only [Pairing.evaluation] using congrArg
    (fun z => Common.quarticDysonSequenceCoeff ε g q t * z) hwick


omit [Finite Mode] in
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
      (Equiv.sum_comp (Common.quarticDiagramEquivOrderedData order) F).symm
    _ = ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
      apply Finset.sum_congr rfl
      intro d _
      rfl


/-- Physical bosonic quartic Dyson diagram amplitude, summed over all global vertex orders.
The ordered-simplex regions associated with these orders are the pieces that shuffle-factorize over
connected components, so this physical amplitude is a sum over orders, with no factorial
averaging. -/
noncomputable def QuarticDiagram.dysonThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S) (t : ℝ) : ℂ :=
  ∑ order : Common.QuarticVertexOrder S,
    QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t

omit [Finite Mode] in
/-- The total physical quartic-diagram weight is the canonical vertex moment:
`|S|!` times the convergence-aware bosonic Dyson coefficient. The factorial counts the global
vertex orders; summing over them retains the ordered-simplex regions needed for subsequent
connected-component factorization. -/
theorem factorial_mul_freeGibbsDysonCoeff_quarticInteraction_eq_sum_dysonThermalAmplitude
    [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} (S : Finset (Fin N)) (t : ℝ) :
    (S.card.factorial : ℂ) *
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t =
      ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.dysonThermalAmplitude ε β g d t := by
  classical
  calc
    (S.card.factorial : ℂ) *
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t =
      ∑ _order : Common.QuarticVertexOrder S,
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t := by
          rw [Finset.sum_const, Finset.card_univ, Common.card_quarticVertexOrder]
          simp [nsmul_eq_mul]
    _ = ∑ order : Common.QuarticVertexOrder S,
        ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
          QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
      apply Finset.sum_congr rfl
      intro order _
      exact
        freeGibbsDysonCoeff_quarticInteraction_eq_sum_orderedDysonThermalAmplitude
          ε β hpos g S order t
    _ = ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        ∑ order : Common.QuarticVertexOrder S,
          QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
      rw [Finset.sum_comm]
    _ = ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.dysonThermalAmplitude ε β g d t := rfl

end
end Bosonic
end SecondQuantization
