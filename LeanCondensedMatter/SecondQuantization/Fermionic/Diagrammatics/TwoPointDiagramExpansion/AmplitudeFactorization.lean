import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedConnectivity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.IntegratedComponentFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.AmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment

set_option linter.style.header false

/-!
# External/vacuum factorization of labelled two-point amplitudes

This file owns the finite-sum assembly step of the external-leg linked-cluster theorem. The analytic
input is the a.e. component-shuffle integral factorization from `IntegratedComponentFactorization`;
the remaining work is performed on the total finite diagram sum rather than by diagram orbits.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- Explicit fixed-external diagrams whose complete graph is externally connected. -/
abbrev ExternallyConnectedFixedExternalTwoPointWickDiagram
    (Mode : Type*) (n : ℕ) (i j : Mode) :=
  {d : FixedExternalTwoPointWickDiagram Mode n i j // d.1.IsExternallyConnected}

/-- Arbitrary-set fixed-external diagrams whose complete graph is externally connected. -/
abbrev ExternallyConnectedFixedExternalTwoPointWickDiagramOn
    (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :=
  {d : FixedExternalTwoPointWickDiagramOn Mode N S i j // d.1.IsExternallyConnected}

noncomputable instance externallyConnectedFixedExternalTwoPointWickDiagramFintype
    (Mode : Type*) [Fintype Mode] (n : ℕ) (i j : Mode) :
    Fintype (ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j) :=
  Fintype.ofFinite _

noncomputable instance externallyConnectedFixedExternalTwoPointWickDiagramOnFintype
    (Mode : Type*) [Fintype Mode] (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :
    Fintype (ExternallyConnectedFixedExternalTwoPointWickDiagramOn Mode N S i j) :=
  Fintype.ofFinite _

omit [LinearOrder Mode] [Fintype Mode] in
/-- The explicit diagram produced by the fixed-order equivalence is exactly the Common ordered
reindexing of the underlying arbitrary-set diagram. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_val_eq_inInteractionOrder
    {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j) :
    (fixedExternalTwoPointWickDiagramOrderEquiv i j order d).1 =
      d.1.inInteractionOrder order := by
  apply Common.TwoPointDiagram.ext
  · exact d.2.symm
  · funext v
    rfl
  · apply Combinatorics.Pairing.ext
    apply Equiv.ext
    intro leg
    apply Fin.ext
    rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- External connectedness is preserved by the fixed-order diagram equivalence. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_isExternallyConnected_iff
    {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j) :
    (fixedExternalTwoPointWickDiagramOrderEquiv i j order d).1.IsExternallyConnected ↔
      d.1.IsExternallyConnected := by
  rw [fixedExternalTwoPointWickDiagramOrderEquiv_val_eq_inInteractionOrder]
  exact d.1.inInteractionOrder_isExternallyConnected_iff order

/-- Restrict the fixed-order diagram equivalence to externally connected diagrams. -/
noncomputable def externallyConnectedFixedExternalTwoPointWickDiagramOrderEquiv
    {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S) :
    ExternallyConnectedFixedExternalTwoPointWickDiagramOn Mode N S i j ≃
      ExternallyConnectedFixedExternalTwoPointWickDiagram Mode S.card i j :=
  (fixedExternalTwoPointWickDiagramOrderEquiv i j order).subtypeEquiv fun d =>
    (fixedExternalTwoPointWickDiagramOrderEquiv_isExternallyConnected_iff i j order d).symm

/-- At one fixed interaction order, the sum over connected arbitrary-set external cores is exactly
the explicit connected-diagram coefficient sum. -/
theorem sum_connected_orderedDysonAmplitude_eq_sum_connected_dysonAmplitude
    {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    (∑ d : ExternallyConnectedFixedExternalTwoPointWickDiagramOn Mode N S i j,
        d.1.orderedDysonAmplitude order ε β g τ τ') =
      ∑ d : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode S.card i j,
        d.1.dysonAmplitude ε β g τ τ' := by
  exact Equiv.sum_comp
    (externallyConnectedFixedExternalTwoPointWickDiagramOrderEquiv i j order)
    (fun d => d.1.dysonAmplitude ε β g τ τ')

/-- Summing the order-independent amplitudes of connected external cores gives `|S|!` copies of
the explicit-slot connected coefficient sum. -/
theorem sum_connected_fixedExternalTwoPointWickDiagramAmplitude_eq_factorial_mul_sum_dysonAmplitude
    {S : Finset (Fin N)} (i j : Mode)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    (∑ d : ExternallyConnectedFixedExternalTwoPointWickDiagramOn Mode N S i j,
        fixedExternalTwoPointWickDiagramAmplitude d.1 ε β g τ τ') =
      (S.card.factorial : ℂ) *
        ∑ d : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode S.card i j,
          d.1.dysonAmplitude ε β g τ τ' := by
  simp only [fixedExternalTwoPointWickDiagramAmplitude]
  rw [Finset.sum_comm]
  simp_rw [sum_connected_orderedDysonAmplitude_eq_sum_connected_dysonAmplitude
    i j _ ε β g τ τ']
  rw [Finset.sum_const, Finset.card_univ, Common.card_quarticVertexOrder]
  simp

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

/-- The total order-independent vacuum Wick amplitude on a labelled finite set is the factorial
normalization of the corresponding normalized Dyson partition coefficient. -/
theorem sum_quarticWickDiagramAmplitude_eq_factorial_mul_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} :
    (∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d) =
      (S.card.factorial : ℂ) *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) S.card := by
  rw [sum_quarticWickDiagramAmplitude_eq_dysonVertexMoment, dysonVertexMoment]

end Fermionic
end SecondQuantization
