import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointLinkedClusterTheorem
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalVacuumShuffleProduct
import Mathlib.Data.Finset.NatAntidiagonal

set_option linter.style.header false

/-!
# External/vacuum coefficient convolution

This module closes the last finite combinatorial bridge in the external-leg linked-cluster theorem.
The full order-`n` diagram sum is partitioned by the number of interaction vertices in the unique
external component. Each fiber is the binary external/vacuum slot decomposition proved earlier.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The external-component order of an explicit order-`n` diagram, as an element of `Fin (n+1)`. -/
noncomputable def fixedExternalInteractionOrderFin {n : ℕ} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagram Mode n i j) : Fin (n + 1) := by
  refine ⟨d.1.externalInteractionPart.card, ?_⟩
  have hcard : d.1.externalInteractionPart.card ≤ n := by
    have h := Finset.card_le_card d.1.externalInteractionPart_subset
    simpa using h
  exact Nat.lt_succ_of_le hcard

private theorem sum_fixedExternal_externalOrderFiber_of_add_eq
    {n k m : ℕ} (hkm : k + m = n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    (∑ d : {d : FixedExternalTwoPointWickDiagram Mode n i j //
        d.1.externalInteractionPart.card = k},
      d.1.dysonAmplitude ε β g τ τ') =
      twoPointConnectedDiagramCoeff ε β g i j τ τ' k *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) m := by
  subst n
  change (∑ d : FixedExternalTwoPointWickDiagramOfExternalOrder Mode k m i j,
      d.1.dysonAmplitude ε β g τ τ') = _
  rw [sum_fixedExternalTwoPointWickDiagramOfExternalOrder_eq_connected_mul_vacuum]
  rfl

private theorem sum_fixedExternal_externalOrderFinFiber
    {n : ℕ} (r : Fin (n + 1))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    (∑ d : {d : FixedExternalTwoPointWickDiagram Mode n i j //
        fixedExternalInteractionOrderFin d = r},
      d.1.dysonAmplitude ε β g τ τ') =
      twoPointConnectedDiagramCoeff ε β g i j τ τ' r *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) (n - r) := by
  have hr : (r : ℕ) ≤ n := Nat.le_of_lt_succ r.isLt
  have hsum : (r : ℕ) + (n - r) = n := Nat.add_sub_of_le hr
  simpa [fixedExternalInteractionOrderFin] using
    sum_fixedExternal_externalOrderFiber_of_add_eq
      (Mode := Mode) hsum ε β g i j τ τ'

/-- The unnormalized two-point coefficient is the Cauchy convolution of the connected external
coefficient with the normalized vacuum coefficient. -/
theorem twoPointUnnormalizedDiagramCoeff_eq_connected_mul_vacuum
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    twoPointUnnormalizedDiagramCoeff ε β g i j τ τ' n =
      ∑ p ∈ Finset.antidiagonal n,
        twoPointConnectedDiagramCoeff ε β g i j τ τ' p.1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) p.2 := by
  classical
  let order : FixedExternalTwoPointWickDiagram Mode n i j → Fin (n + 1) :=
    fixedExternalInteractionOrderFin
  let amp : FixedExternalTwoPointWickDiagram Mode n i j → ℂ := fun d =>
    d.dysonAmplitude ε β g τ τ'
  calc
    twoPointUnnormalizedDiagramCoeff ε β g i j τ τ' n =
        ∑ d : FixedExternalTwoPointWickDiagram Mode n i j, amp d := by
      rfl
    _ = ∑ r : Fin (n + 1),
        ∑ d : {d : FixedExternalTwoPointWickDiagram Mode n i j // order d = r},
          amp d.1 := by
      exact (Fintype.sum_fiberwise order amp).symm
    _ = ∑ r : Fin (n + 1),
        twoPointConnectedDiagramCoeff ε β g i j τ τ' r *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) (n - r) := by
      apply Fintype.sum_congr
      intro r
      simpa [order, amp] using
        sum_fixedExternal_externalOrderFinFiber
          (Mode := Mode) r ε β g i j τ τ'
    _ = ∑ p : ↥(Finset.antidiagonal n),
        twoPointConnectedDiagramCoeff ε β g i j τ τ' p.1.1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) p.1.2 := by
      rw [← Equiv.sum_comp (Finset.Nat.antidiagonalEquivFin n)
        (fun r : Fin (n + 1) =>
          twoPointConnectedDiagramCoeff ε β g i j τ τ' r *
            normalizedDysonPartitionCoeff ε β (quarticInteraction g) (n - r))]
      apply Fintype.sum_congr
      intro p
      rw [Finset.Nat.antidiagonalEquivFin_apply_val]
      have hp : p.1.1 + p.1.2 = n := by
        simpa using p.2
      have hsub : n - p.1.1 = p.1.2 := by omega
      rw [hsub]
    _ = ∑ p ∈ Finset.antidiagonal n,
        twoPointConnectedDiagramCoeff ε β g i j τ τ' p.1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) p.2 := by
      exact Finset.sum_coe_sort (Finset.antidiagonal n) (fun p =>
        twoPointConnectedDiagramCoeff ε β g i j τ τ' p.1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) p.2)

end Fermionic
end SecondQuantization
