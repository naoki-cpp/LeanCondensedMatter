import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalVacuumSlotReassemble
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.IntegratedComponentFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.AmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment

set_option linter.style.header false

/-!
# External/vacuum factorization of labelled two-point amplitudes

This file owns the finite-sum assembly step of the external-leg linked-cluster theorem. The analytic
input is the a.e. component-shuffle integral factorization from `IntegratedComponentFactorization`;
the structural input is the binary slot-shuffle reassembly from `ExternalVacuumSlotReassemble`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- The canonical increasing vertex order on explicit interaction slots. -/
noncomputable def explicitQuarticVertexOrder (n : ℕ) :
    Common.QuarticVertexOrder (Finset.univ : Finset (Fin n)) :=
  (finCongr (by simp)).trans (Common.finEquivUnivSubtype n)

/-- Fixed-order vacuum term on explicit slots, including its Dyson sign and coupling weight. -/
noncomputable def explicitVacuumFixedOrderAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {n : ℕ} (d : QuarticWickDiagram Mode n (Finset.univ : Finset (Fin n))) : ℂ :=
  (-1 : ℂ) ^ n * d.couplingWeight g *
    d.orderedSimplexContribution ε β (explicitQuarticVertexOrder n)

/-- For an externally connected fixed diagram the vacuum-component product is empty, so its
Dyson-signed fixed-time amplitude is exactly its external component factor. -/
theorem ExternallyConnectedFixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_external
    {n : ℕ} {i j : Mode}
    (d : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.1.dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.1.mixedExternalDysonFixedTimeValue ε β g τ τ' σ := by
  rw [d.1.dysonFixedTimeAmplitude_eq_external_mul_prod_vacuum]
  have hvac : d.1.1.vacuumComponentParts = ∅ :=
    (d.1.1.isExternallyConnected_iff_vacuumComponentParts_eq_empty).1 d.2
  rw [hvac]
  simp

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

/-- The finite sum over full diagrams with external-component order `k` is reindexed once by a
connected explicit external core, an explicit vacuum remainder, and the binary shuffle placing their
interaction slots in the ambient order. -/
theorem sum_fixedExternalTwoPointWickDiagramOfExternalOrder_eq_sum_slotData
    {k m : ℕ} (i j : Mode)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    (∑ d : FixedExternalTwoPointWickDiagramOfExternalOrder Mode k m i j,
        d.1.dysonAmplitude ε β g τ τ') =
      ∑ external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j,
        ∑ vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)),
          ∑ shuffle : Combinatorics.BinaryShuffle.SlotShuffle k m,
            (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).dysonAmplitude
              ε β g τ τ' := by
  classical
  calc
    (∑ d : FixedExternalTwoPointWickDiagramOfExternalOrder Mode k m i j,
        d.1.dysonAmplitude ε β g τ τ') =
      ∑ x : ExternalVacuumSlotData Mode k m i j,
        (externalVacuumSlotDataEquivOfExternalOrder i j x).1.dysonAmplitude
          ε β g τ τ' :=
      (Equiv.sum_comp (externalVacuumSlotDataEquivOfExternalOrder i j)
        (fun d => d.1.dysonAmplitude ε β g τ τ')).symm
    _ = ∑ external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j,
        ∑ vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)),
          ∑ shuffle : Combinatorics.BinaryShuffle.SlotShuffle k m,
            (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).dysonAmplitude
              ε β g τ τ' := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro external _
      rw [Fintype.sum_prod_type]
      rfl

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

/-- The explicit fixed-order vacuum terms sum to the normalized vacuum Dyson coefficient. -/
theorem sum_explicitVacuumFixedOrderAmplitude_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) :
    (∑ d : QuarticWickDiagram Mode n (Finset.univ : Finset (Fin n)),
      explicitVacuumFixedOrderAmplitude ε β g d) =
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) n := by
  simp only [explicitVacuumFixedOrderAmplitude]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simpa using
    sum_vacuumFixedOrder_eq_normalizedDysonPartitionCoeff
      (Mode := Mode) (N := n) ε β g (explicitQuarticVertexOrder n)

/-- Once the binary shuffle sum for each fixed external/vacuum pair is identified with the product
of their local integrated amplitudes, the whole external-order fiber factors immediately. -/
theorem sum_fixedExternalTwoPointWickDiagramOfExternalOrder_eq_connected_mul_vacuum_of_shuffle
    {k m : ℕ} (i j : Mode)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ)
    (hshuffle : ∀
      (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
      (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m))),
      (∑ shuffle : Combinatorics.BinaryShuffle.SlotShuffle k m,
        (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).dysonAmplitude
          ε β g τ τ') =
        external.1.dysonAmplitude ε β g τ τ' *
          explicitVacuumFixedOrderAmplitude ε β g vacuum) :
    (∑ d : FixedExternalTwoPointWickDiagramOfExternalOrder Mode k m i j,
        d.1.dysonAmplitude ε β g τ τ') =
      (∑ external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j,
        external.1.dysonAmplitude ε β g τ τ') *
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) m := by
  rw [sum_fixedExternalTwoPointWickDiagramOfExternalOrder_eq_sum_slotData]
  simp_rw [hshuffle]
  rw [← Finset.sum_mul]
  apply congrArg (fun z : ℂ =>
    (∑ external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j,
      external.1.dysonAmplitude ε β g τ τ') * z)
  exact sum_explicitVacuumFixedOrderAmplitude_eq_normalizedDysonPartitionCoeff ε β g m

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
