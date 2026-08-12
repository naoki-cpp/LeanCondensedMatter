import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing

set_option linter.style.header false

/-!
# Fixed-order quartic Wick-diagram sums

A quartic Wick-diagram amplitude sums over every vertex order.  In the two-point linked-cluster
fiber decomposition the vacuum piece inherits one fixed order from the ambient interaction slots,
so the relevant vacuum factor is instead the sum of one fixed-order contribution over all quartic
diagrams.

This module identifies that sum directly with the normalized Dyson partition coefficient.  Keeping
the vertex order fixed removes the factorial carried by `dysonVertexMoment` and is the form consumed
by the external-leg Cauchy product.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Summing the Dyson-signed contribution of one fixed vertex order over all quartic Wick diagrams
is the normalized Dyson partition coefficient at the corresponding perturbation order. -/
theorem sum_quarticWickDiagram_fixedOrderDysonContribution_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)} (order : Common.QuarticVertexOrder S) :
    (∑ d : QuarticWickDiagram Mode N S,
        (-1 : ℂ) ^ S.card * d.couplingWeight g * d.orderedSimplexContribution ε β order) =
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) S.card := by
  classical
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [sum_couplingWeight_mul_orderedSimplexContribution_eq_pairingEvaluation]
  have hfac : ((S.card.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero S.card
  apply mul_left_cancel₀ hfac
  simpa [dysonVertexMoment, mul_assoc] using
    (dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairingEvaluation
      ε β g S).symm

end Fermionic
end SecondQuantization
