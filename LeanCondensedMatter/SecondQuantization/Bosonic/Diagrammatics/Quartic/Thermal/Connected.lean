import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticThermalComponentFactorization
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

This gives a direct input to the generic cumulant/connected-decomposition theorem. Everything in
this file is finite and coefficientwise: no ordered-simplex integration, infinite Dyson-series
convergence, or completed-Fock-space assertion is made. The decomposition adapter itself is
statistics-independent and owned by `Common`.
-/

namespace SecondQuantization
namespace Bosonic

open Combinatorics

noncomputable section

variable {Mode : Type*} [DecidableEq Mode] {N : ℕ}

/-- Diagram-level coefficientwise thermal amplitude, defined as the average over all vertex orders. -/
noncomputable def QuarticDiagram.thermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S) : ℂ :=
  (S.card.factorial : ℂ)⁻¹ *
    ∑ order : Common.QuarticVertexOrder S, d.orderedThermalAmplitude ε β g order

omit [DecidableEq Mode] in
private theorem QuarticDiagram.card_componentVertexOrders
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S) :
    Fintype.card d.ComponentVertexOrders =
      ∏ B : d.componentPartition.parts, (B : Finset (Fin N)).card.factorial := by
  classical
  simp only [Common.QuarticDiagram.ComponentVertexOrders, Fintype.card_pi,
    Common.card_quarticVertexOrder]

omit [DecidableEq Mode] in
private theorem QuarticDiagram.card_componentShuffle_mul_componentFactorials
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S) :
    Fintype.card d.ComponentShuffle *
        (∏ B : d.componentPartition.parts, (B : Finset (Fin N)).card.factorial) =
      S.card.factorial := by
  classical
  have hcard := Fintype.card_congr d.componentOrderDecompositionEquiv
  rw [Common.card_quarticVertexOrder, Fintype.card_prod,
    d.card_componentVertexOrders] at hcard
  simpa [Nat.mul_comm] using hcard.symm

private theorem QuarticDiagram.sum_orderedThermalAmplitude_eq_shuffle_mul_componentSums
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S) :
    (∑ order : Common.QuarticVertexOrder S, d.orderedThermalAmplitude ε β g order) =
      (Fintype.card d.ComponentShuffle : ℂ) *
        ∏ B : d.componentPartition.parts,
          ∑ order : Common.QuarticVertexOrder (B : Finset (Fin N)),
            QuarticDiagram.orderedThermalAmplitude ε β g (d.restrictComponent B.2) order := by
  classical
  let F : d.ComponentVertexOrders × d.ComponentShuffle → ℂ := fun x =>
    d.orderedThermalAmplitude ε β g (d.assembleVertexOrder x.1 x.2)
  have hreindex := Equiv.sum_comp d.componentOrderDecompositionEquiv F
  have hleft :
      (∑ order : Common.QuarticVertexOrder S, d.orderedThermalAmplitude ε β g order) =
        ∑ x : d.ComponentVertexOrders × d.ComponentShuffle, F x := by
    calc
      (∑ order : Common.QuarticVertexOrder S, d.orderedThermalAmplitude ε β g order) =
          ∑ order : Common.QuarticVertexOrder S,
            F (d.componentOrderDecompositionEquiv order) := by
        apply Finset.sum_congr rfl
        intro order _
        change d.orderedThermalAmplitude ε β g order =
          d.orderedThermalAmplitude ε β g
            ((d.componentOrderDecompositionEquiv).symm
              (d.componentOrderDecompositionEquiv order))
        exact congrArg (d.orderedThermalAmplitude ε β g)
          ((d.componentOrderDecompositionEquiv).symm_apply_apply order).symm
      _ = ∑ x : d.ComponentVertexOrders × d.ComponentShuffle, F x := hreindex
  rw [hleft, Fintype.sum_prod_type]
  simp only [F]
  have hfactor : ∀ orders : d.ComponentVertexOrders,
      (∑ shuffle : d.ComponentShuffle,
        d.orderedThermalAmplitude ε β g (d.assembleVertexOrder orders shuffle)) =
        (Fintype.card d.ComponentShuffle : ℂ) *
          ∏ B : d.componentPartition.parts,
            QuarticDiagram.orderedThermalAmplitude ε β g
              (d.restrictComponent B.2) (orders B) := by
    intro orders
    simp_rw [d.orderedThermalAmplitude_eq_prod_components ε β g orders]
    simp
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  congr 1
  have hdist := Finset.prod_univ_sum
    (fun B : d.componentPartition.parts =>
      (Finset.univ : Finset (Common.QuarticVertexOrder (B : Finset (Fin N)))))
    (fun B order =>
      QuarticDiagram.orderedThermalAmplitude ε β g (d.restrictComponent B.2) order)
  rw [Fintype.piFinset_univ] at hdist
  simpa using hdist.symm

/-- Averaging over global vertex orders removes the shuffle multiplicity, so the coefficientwise
thermal amplitude factors exactly over connected components. -/
theorem QuarticDiagram.thermalAmplitude_eq_prod_restrictComponentConnected
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S) :
    d.thermalAmplitude ε β g =
      ∏ B : d.componentPartition.parts,
        QuarticDiagram.thermalAmplitude ε β g (d.restrictComponentConnected B.2).1 := by
  classical
  rw [QuarticDiagram.thermalAmplitude,
    d.sum_orderedThermalAmplitude_eq_shuffle_mul_componentSums ε β g]
  simp only [QuarticDiagram.thermalAmplitude,
    Common.QuarticDiagram.restrictComponentConnected]
  rw [Finset.prod_mul_distrib]
  have hcard := d.card_componentShuffle_mul_componentFactorials
  have hshuffle : (Fintype.card d.ComponentShuffle : ℂ) ≠ 0 := by
    let order := Common.someVertexOrder S
    letI : Nonempty d.ComponentShuffle :=
      ⟨(d.componentOrderDecompositionEquiv order).2⟩
    exact_mod_cast Fintype.card_ne_zero
  have hcardC :
      (S.card.factorial : ℂ) =
        (Fintype.card d.ComponentShuffle : ℂ) *
          (∏ B : d.componentPartition.parts,
            ((B : Finset (Fin N)).card.factorial : ℂ)) := by
    exact_mod_cast hcard.symm
  rw [hcardC]
  simp only [mul_inv_rev]
  rw [mul_assoc
    (∏ B : d.componentPartition.parts,
      ((B : Finset (Fin N)).card.factorial : ℂ))⁻¹
    (Fintype.card d.ComponentShuffle : ℂ)⁻¹
    ((Fintype.card d.ComponentShuffle : ℂ) *
      ∏ B : d.componentPartition.parts,
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
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) N) ℂ where
  objectWeight d := QuarticDiagram.thermalAmplitude ε β g d
  connectedWeight d := QuarticDiagram.thermalAmplitude ε β g d.1
  weight_decompose d := by
    change QuarticDiagram.thermalAmplitude ε β g d =
      ∏ B : d.componentPartition.parts,
        QuarticDiagram.thermalAmplitude ε β g (d.restrictComponentConnected B.2).1
    exact QuarticDiagram.thermalAmplitude_eq_prod_restrictComponentConnected ε β g d

/-- Total coefficientwise bosonic thermal diagram weight on a finite vertex set. -/
noncomputable def quarticThermalMoment
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (S : Finset (Fin N)) : ℂ :=
  (quarticThermalDiagramMultiplicativeWeight (N := N) ε β g).objectMoment S

/-- Coefficientwise bosonic thermal cumulant obtained by Möbius inversion of the diagram moment. -/
noncomputable def quarticThermalCumulant
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (S : Finset (Fin N)) : ℂ :=
  Finpartition.cumulantFromMoment (quarticThermalMoment (N := N) ε β g) S

/-- The coefficientwise bosonic thermal cumulant is exactly the sum of order-averaged amplitudes of
connected quartic diagrams. -/
theorem quarticThermalCumulant_eq_sum_connectedQuarticDiagramAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (hS : S ≠ ∅) :
    quarticThermalCumulant (N := N) ε β g S =
      ∑ d : ConnectedQuarticDiagram Mode N S,
        QuarticDiagram.thermalAmplitude ε β g d.1 := by
  let W := quarticThermalDiagramMultiplicativeWeight (N := N) ε β g
  change Finpartition.cumulantFromMoment W.objectMoment S =
    ∑ d : ConnectedQuarticDiagram Mode N S,
      QuarticDiagram.thermalAmplitude ε β g d.1
  calc
    Finpartition.cumulantFromMoment W.objectMoment S = W.connectedContribution S :=
      W.cumulantFromMoment_objectMoment hS
    _ = ∑ d : ConnectedQuarticDiagram Mode N S,
        QuarticDiagram.thermalAmplitude ε β g d.1 := rfl

end
end Bosonic
end SecondQuantization
