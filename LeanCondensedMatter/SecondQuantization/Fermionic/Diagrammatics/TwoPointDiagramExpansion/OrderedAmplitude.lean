import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Ordered
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonCoefficient

set_option linter.style.header false

/-!
# Two-point amplitudes on arbitrary finite interaction sets

A finite interaction set is first supplied with a vertex order, then reindexed to the explicit
`Fin n` slot convention used by the existing two-point Dyson amplitude. Summing over all interaction
orders gives an order-independent labelled-diagram amplitude, parallel to
`quarticWickDiagramAmplitude` on the vacuum side.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- Two-point Wick diagrams on an arbitrary finite interaction set with the two external labels
fixed to `T c_i c_j†`. -/
abbrev FixedExternalTwoPointWickDiagramOn
    (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :=
  {d : TwoPointWickDiagram Mode N S // d.externalLabel = twoPointExternalLabels i j}

/-- Ordered standard data of a fixed-external two-point diagram. -/
abbrev OrderedFixedExternalTwoPointData (Mode : Type*) (n : ℕ) :=
  (Fin n → QuarticVertexLabel Mode) × Pairing (2 * n + 1)

/-- Fixed-external diagrams on `S` are equivalent to standard slot data once an interaction order is
chosen. -/
noncomputable def fixedExternalTwoPointWickDiagramOnEquivOrderedData
    {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S) :
    FixedExternalTwoPointWickDiagramOn Mode N S i j ≃
      OrderedFixedExternalTwoPointData Mode S.card where
  toFun d :=
    (fun k => d.1.vertexLabel (order k), d.1.pairingInInteractionOrder order)
  invFun x :=
    ⟨(Common.twoPointDiagramEquivOrderedData order).symm
      (twoPointExternalLabels i j, x.1, x.2), by
        change ((Common.twoPointDiagramEquivOrderedData order).symm
          (twoPointExternalLabels i j, x.1, x.2)).externalLabel = _
        simp [Common.twoPointDiagramEquivOrderedData]⟩
  left_inv d := by
    apply Subtype.ext
    change (Common.twoPointDiagramEquivOrderedData order).symm
      (d.1.externalLabel, fun k => d.1.vertexLabel (order k),
        d.1.pairingInInteractionOrder order) = d.1
    simpa using (Common.twoPointDiagramEquivOrderedData order).left_inv d.1
  right_inv x := by
    rcases x with ⟨labels, pairing⟩
    apply Prod.ext
    · funext k
      simp [Common.twoPointDiagramEquivOrderedData]
    · simp [Common.twoPointDiagramEquivOrderedData]

/-- Standard slot data are equivalent to the existing explicit-`Fin n` fixed-external diagram type. -/
noncomputable def orderedFixedExternalTwoPointDataEquivFixedDiagram
    (n : ℕ) (i j : Mode) :
    OrderedFixedExternalTwoPointData Mode n ≃ FixedExternalTwoPointWickDiagram Mode n i j where
  toFun x :=
    ⟨{
      externalLabel := twoPointExternalLabels i j
      vertexLabel := fun v => x.1 v.1
      pairing := (orderedTwoPointPairingCastEquiv n).symm x.2
    }, rfl⟩
  invFun d :=
    (d.vertexLabelSequence, orderedTwoPointPairingCastEquiv n d.1.pairing)
  left_inv x := by
    rcases x with ⟨labels, pairing⟩
    apply Prod.ext
    · rfl
    · exact (orderedTwoPointPairingCastEquiv n).apply_symm_apply pairing
  right_inv d := by
    apply Subtype.ext
    apply Common.TwoPointDiagram.ext
    · exact d.2.symm
    · funext v
      rfl
    · exact (orderedTwoPointPairingCastEquiv n).symm_apply_apply d.1.pairing

/-- Reindex an arbitrary finite-set fixed-external diagram to explicit interaction slots according
to `order`. -/
noncomputable def fixedExternalTwoPointWickDiagramOrderEquiv
    {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S) :
    FixedExternalTwoPointWickDiagramOn Mode N S i j ≃
      FixedExternalTwoPointWickDiagram Mode S.card i j :=
  (fixedExternalTwoPointWickDiagramOnEquivOrderedData i j order).trans
    (orderedFixedExternalTwoPointDataEquivFixedDiagram S.card i j)

/-- Dyson amplitude of an arbitrary finite-set diagram for one chosen interaction order. -/
noncomputable def FixedExternalTwoPointWickDiagramOn.orderedDysonAmplitude
    {S : Finset (Fin N)} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j)
    (order : Common.QuarticVertexOrder S)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) : ℂ :=
  (fixedExternalTwoPointWickDiagramOrderEquiv i j order d).dysonAmplitude
    ε β g τ τ'

/-- Order-independent amplitude of a fixed-external two-point Wick diagram on an arbitrary finite
interaction set, obtained by summing over all interaction-vertex orders. -/
noncomputable def fixedExternalTwoPointWickDiagramAmplitude
    {S : Finset (Fin N)} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) : ℂ :=
  ∑ order : Common.QuarticVertexOrder S,
    d.orderedDysonAmplitude order ε β g τ τ'

/-- For each fixed interaction order, summing arbitrary-set diagram contributions is the same as
summing the existing explicit-slot Dyson amplitudes. -/
theorem sum_orderedDysonAmplitude_eq_sum_fixedDiagram_dysonAmplitude
    {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    (∑ d : FixedExternalTwoPointWickDiagramOn Mode N S i j,
        d.orderedDysonAmplitude order ε β g τ τ') =
      ∑ d : FixedExternalTwoPointWickDiagram Mode S.card i j,
        d.dysonAmplitude ε β g τ τ' := by
  exact Equiv.sum_comp
    (fixedExternalTwoPointWickDiagramOrderEquiv i j order)
    (fun d => d.dysonAmplitude ε β g τ τ')

/-- Summing the order-independent arbitrary-set amplitudes gives `|S|!` copies of the existing
explicit-slot diagram-amplitude sum. -/
theorem sum_fixedExternalTwoPointWickDiagramAmplitude_eq_factorial_mul_sum_dysonAmplitude
    {S : Finset (Fin N)} (i j : Mode)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    (∑ d : FixedExternalTwoPointWickDiagramOn Mode N S i j,
        fixedExternalTwoPointWickDiagramAmplitude d ε β g τ τ') =
      (S.card.factorial : ℂ) *
        ∑ d : FixedExternalTwoPointWickDiagram Mode S.card i j,
          d.dysonAmplitude ε β g τ τ' := by
  simp only [fixedExternalTwoPointWickDiagramAmplitude]
  rw [Finset.sum_comm]
  simp_rw [sum_orderedDysonAmplitude_eq_sum_fixedDiagram_dysonAmplitude
    i j _ ε β g τ τ']
  rw [Finset.sum_const, Finset.card_univ, Common.card_quarticVertexOrder]
  simp

end Fermionic
end SecondQuantization
