import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.ComponentFactorization
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentOrder

set_option linter.style.header false

/-!
# Coefficientwise connected theorem for bosonic quartic thermal diagrams

The ordered thermal amplitude factors over connected components once a global vertex order is
written as component-local orders plus a shuffle. A raw sum over global vertex orders therefore
contains a shuffle multiplicity. Dividing by the number of vertex orders removes exactly that
multiplicity, so the resulting diagram-level amplitude is multiplicative under connected-component
decomposition.

This gives a direct input to the generic normalized cumulant/connected-decomposition theorem.
Everything in this file is finite and coefficientwise: no ordered-simplex integration, infinite
Dyson-series convergence, or completed-Fock-space assertion is made. The decomposition adapter
itself is statistics-independent and owned by `Common`.
-/

namespace SecondQuantization
namespace Bosonic

open Combinatorics

noncomputable section

variable {Mode : Type*} {N : ℕ}

/-- Diagram-level coefficientwise thermal amplitude, defined as the average over all vertex orders. -/
noncomputable def QuarticDiagram.thermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S) : ℂ :=
  (S.card.factorial : ℂ)⁻¹ *
    ∑ order : Common.QuarticVertexOrder S,
      QuarticDiagram.orderedThermalAmplitude ε β g d order

private theorem QuarticDiagram.card_componentVertexOrders
    {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S) :
    Fintype.card d.ComponentVertexOrders =
      ∏ B : d.vertexGraph.componentPartitionOn.parts, (B : Finset (Fin N)).card.factorial := by
  classical
  simp only [Common.QuarticDiagram.ComponentVertexOrders, Fintype.card_pi,
    Common.card_quarticVertexOrder]

private theorem QuarticDiagram.card_componentShuffle_mul_componentFactorials
    {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S) :
    Fintype.card d.ComponentShuffle *
        (∏ B : d.vertexGraph.componentPartitionOn.parts, (B : Finset (Fin N)).card.factorial) =
      S.card.factorial := by
  classical
  have hcard := Fintype.card_congr d.componentOrderDecompositionEquiv
  rw [Common.card_quarticVertexOrder, Fintype.card_prod,
    QuarticDiagram.card_componentVertexOrders d] at hcard
  simpa [Nat.mul_comm] using hcard.symm

private theorem QuarticDiagram.sum_orderedThermalAmplitude_eq_shuffle_mul_componentSums
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S) :
    (∑ order : Common.QuarticVertexOrder S,
      QuarticDiagram.orderedThermalAmplitude ε β g d order) =
      (Fintype.card d.ComponentShuffle : ℂ) *
        ∏ B : d.vertexGraph.componentPartitionOn.parts,
          ∑ order : Common.QuarticVertexOrder (B : Finset (Fin N)),
            QuarticDiagram.orderedThermalAmplitude ε β g (d.restrictComponent B.2) order := by
  classical
  exact Common.QuarticDiagram.sum_vertexOrder_eq_mul_prod_sum_componentOrders
    d
    (fun order : Common.QuarticVertexOrder S =>
      QuarticDiagram.orderedThermalAmplitude ε β g d order)
    (fun B order =>
      QuarticDiagram.orderedThermalAmplitude ε β g (d.restrictComponent B.2) order)
    (Fintype.card d.ComponentShuffle : ℂ) (fun orders => by
      simp_rw [QuarticDiagram.orderedThermalAmplitude_eq_prod_components ε β g d orders]
      simp)


/-- Averaging over global vertex orders removes the shuffle multiplicity, so the coefficientwise
thermal amplitude factors exactly over connected components. -/
theorem QuarticDiagram.thermalAmplitude_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S) :
    QuarticDiagram.thermalAmplitude ε β g d =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        QuarticDiagram.thermalAmplitude ε β g (d.restrictComponentConnected B.2).1 := by
  classical
  rw [QuarticDiagram.thermalAmplitude,
    QuarticDiagram.sum_orderedThermalAmplitude_eq_shuffle_mul_componentSums ε β g d]
  simp only [QuarticDiagram.thermalAmplitude,
    Common.QuarticDiagram.restrictComponentConnected]
  rw [Finset.prod_mul_distrib]
  have hcard := QuarticDiagram.card_componentShuffle_mul_componentFactorials d
  have hshuffle : (Fintype.card d.ComponentShuffle : ℂ) ≠ 0 := by
    let order := Common.someVertexOrder S
    letI : Nonempty d.ComponentShuffle :=
      ⟨(d.componentOrderDecompositionEquiv order).2⟩
    exact_mod_cast Fintype.card_ne_zero
  have hcardC :
      (S.card.factorial : ℂ) =
        (Fintype.card d.ComponentShuffle : ℂ) *
          (∏ B : d.vertexGraph.componentPartitionOn.parts,
            ((B : Finset (Fin N)).card.factorial : ℂ)) := by
    exact_mod_cast hcard.symm
  rw [hcardC]
  simp only [mul_inv_rev]
  rw [mul_assoc
    (∏ B : d.vertexGraph.componentPartitionOn.parts,
      ((B : Finset (Fin N)).card.factorial : ℂ))⁻¹
    (Fintype.card d.ComponentShuffle : ℂ)⁻¹
    ((Fintype.card d.ComponentShuffle : ℂ) *
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        ∑ order : Common.QuarticVertexOrder (B : Finset (Fin N)),
          QuarticDiagram.orderedThermalAmplitude ε β g (d.restrictComponent B.2) order)]
  rw [← mul_assoc (Fintype.card d.ComponentShuffle : ℂ)⁻¹
    (Fintype.card d.ComponentShuffle : ℂ), inv_mul_cancel₀ hshuffle, one_mul]
  rw [Finset.prod_inv_distrib]

variable [Fintype Mode]

/-- The order-averaged coefficientwise thermal amplitude as a multiplicative diagram weight. -/
noncomputable def quarticThermalDiagramMultiplicativeWeight
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.MultiplicativeWeight
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) N) ℂ :=
  Common.QuarticDiagram.multiplicativeWeight
    (N := N)
    (fun d => QuarticDiagram.thermalAmplitude ε β g d)
    (fun d => QuarticDiagram.thermalAmplitude_eq_prod_components ε β g d)

/-- Total coefficientwise bosonic thermal diagram weight on a finite vertex set, bundled with its
canonical empty-set normalization. -/
noncomputable def quarticThermalMoment
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.NormalizedSetFunction (Fin N) ℂ :=
  (quarticThermalDiagramMultiplicativeWeight (N := N) ε β g).normalizedObjectMoment

/-- Coefficientwise bosonic thermal cumulant in normalized finite-set coordinates. -/
noncomputable def quarticThermalCumulant
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.NormalizedSetFunction (Fin N) ℂ :=
  (quarticThermalMoment (N := N) ε β g).cumulant

/-- The coefficientwise bosonic thermal cumulant is exactly the sum of order-averaged amplitudes of
connected quartic diagrams. -/
theorem quarticThermalCumulant_eq_sum_connectedQuarticDiagramAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (hS : S ≠ ∅) :
    quarticThermalCumulant (N := N) ε β g S =
      ∑ d : Common.ConnectedQuarticDiagram (Common.QuarticVertexLabel Mode) N S,
        QuarticDiagram.thermalAmplitude ε β g d.1 := by
  let W := quarticThermalDiagramMultiplicativeWeight (N := N) ε β g
  change W.normalizedObjectMoment.cumulant S =
    ∑ d : Common.ConnectedQuarticDiagram (Common.QuarticVertexLabel Mode) N S,
      QuarticDiagram.thermalAmplitude ε β g d.1
  calc
    W.normalizedObjectMoment.cumulant S = W.connectedContribution S :=
      W.normalizedObjectMoment_cumulant_eq_connectedContribution hS
    _ = ∑ d : Common.ConnectedQuarticDiagram (Common.QuarticVertexLabel Mode) N S,
        QuarticDiagram.thermalAmplitude ε β g d.1 := rfl

end
end Bosonic
end SecondQuantization
