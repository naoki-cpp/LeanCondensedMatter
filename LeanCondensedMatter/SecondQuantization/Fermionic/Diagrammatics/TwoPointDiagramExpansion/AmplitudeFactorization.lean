import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.IntegratedComponentFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.AmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment

set_option linter.style.header false

/-!
# External/vacuum factorization of labelled two-point amplitudes

This file owns the finite-sum assembly step of the external-leg linked-cluster theorem.  The analytic
input is the a.e. component-shuffle integral factorization from `IntegratedComponentFactorization`;
the remaining work is performed on the total finite diagram sum rather than by transporting
connectedness through every chosen vertex order.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- For any chosen order on a finite vacuum vertex set, the Dyson-signed sum of fixed-order Wick
contributions is already the normalized partition coefficient. The factorial in
`dysonVertexMoment` comes only from summing over all vertex orders. -/
theorem sum_vacuumFixedOrder_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (order : Common.QuarticVertexOrder S) :
    (-1 : ℂ) ^ S.card *
        (∑ d : QuarticWickDiagram Mode N S,
          d.couplingWeight g * d.orderedSimplexContribution ε β order) =
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) S.card := by
  rw [sum_couplingWeight_mul_orderedSimplexContribution_eq_pairingEvaluation
    ε β g order]
  have hmoment :=
    dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairingEvaluation ε β g S
  rw [dysonVertexMoment] at hmoment
  have hfac : (S.card.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero S.card
  apply mul_left_cancel₀ hfac
  calc
    (S.card.factorial : ℂ) *
        ((-1 : ℂ) ^ S.card *
          (∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
            ∑ pairing : Combinatorics.Pairing (2 * S.card),
              intervalIntegral.orderedSimplexIntegral S.card β
                (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing))) =
      (S.card.factorial : ℂ) * (-1 : ℂ) ^ S.card *
          (∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
            ∑ pairing : Combinatorics.Pairing (2 * S.card),
              intervalIntegral.orderedSimplexIntegral S.card β
                (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing)) := by ring
    _ = (S.card.factorial : ℂ) *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) S.card := hmoment.symm

end Fermionic
end SecondQuantization
