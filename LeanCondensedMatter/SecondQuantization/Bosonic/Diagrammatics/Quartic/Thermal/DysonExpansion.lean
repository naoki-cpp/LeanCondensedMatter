import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.Amplitude
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsBoundary
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticDysonExpansion

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

variable {Mode : Type*} [Fintype Mode]

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

end
end Bosonic
end SecondQuantization
