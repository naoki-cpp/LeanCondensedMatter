import LeanCondensedMatter.Combinatorics.DiagramConnectedness
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.AmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion

set_option linter.style.header false

/-!
# Connected quartic Wick diagrams and Dyson vertex cumulants

Quartic Wick diagrams, their connected subtypes, the component-decomposition equivalence, and the
quartic Wick amplitude define a concrete `Combinatorics.WeightedDiagramFamily`. The M2 amplitude
factorization theorem supplies its component-weight axiom. The abstract diagram-connectedness theorem
then identifies the finite-set Dyson cumulant with the sum of connected quartic Wick-diagram
amplitudes on every nonempty vertex set.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- Quartic Wick diagrams equipped with their connected-component decomposition and amplitude form a
weighted diagram family on the ambient vertex-label type `Fin N`. -/
noncomputable def quarticWickDiagramWeightedFamily (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) : Combinatorics.WeightedDiagramFamily (Fin N) where
  Diagram S := QuarticWickDiagram Mode N S
  ConnectedDiagram S := ConnectedQuarticWickDiagram Mode N S
  fintypeDiagram S := inferInstance
  fintypeConnectedDiagram S := inferInstance
  decompose S := QuarticWickDiagram.componentDecompositionEquiv
  diagramWeight d := quarticWickDiagramAmplitude ε β g d
  connectedWeight d := quarticWickDiagramAmplitude ε β g d.1
  weight_decompose d := by
    change quarticWickDiagramAmplitude ε β g d =
      ∏ B : d.componentPartition.parts,
        quarticWickDiagramAmplitude ε β g (d.restrictComponentConnected B.2).1
    exact quarticWickDiagramAmplitude_eq_prod_restrictComponentConnected ε β g d

/-- The abstract moment of the quartic Wick-diagram family is the Dyson vertex moment of the quartic
interaction. -/
theorem quarticWickDiagramWeightedFamily_diagramMoment (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (S : Finset (Fin N)) :
    (quarticWickDiagramWeightedFamily (N := N) ε β g).diagramMoment S =
      dysonVertexMoment ε β (quarticInteraction g) S := by
  change (∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d) =
    dysonVertexMoment ε β (quarticInteraction g) S
  exact (dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude ε β g S).symm

/-- The connected contribution of the concrete family is the explicit sum of connected quartic
Wick-diagram amplitudes. -/
theorem quarticWickDiagramWeightedFamily_connectedDiagramContribution (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (S : Finset (Fin N)) :
    (quarticWickDiagramWeightedFamily (N := N) ε β g).connectedDiagramContribution S =
      ∑ d : ConnectedQuarticWickDiagram Mode N S,
        quarticWickDiagramAmplitude ε β g d.1 := by
  rfl

/-- The Dyson vertex cumulant of a quartic interaction is the sum of amplitudes of connected quartic
Wick diagrams on every nonempty vertex set. This is the exit theorem of milestone M3. -/
theorem dysonVertexCumulant_quarticInteraction_eq_sum_connectedQuarticWickDiagramAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (hS : S ≠ ∅) :
    dysonVertexCumulant ε β (quarticInteraction g) S =
      ∑ d : ConnectedQuarticWickDiagram Mode N S,
        quarticWickDiagramAmplitude ε β g d.1 := by
  let D := quarticWickDiagramWeightedFamily (N := N) ε β g
  calc
    dysonVertexCumulant ε β (quarticInteraction g) S =
        Finpartition.cumulantFromMoment D.diagramMoment S := by
      unfold dysonVertexCumulant
      congr 1
      funext T
      exact (quarticWickDiagramWeightedFamily_diagramMoment ε β g T).symm
    _ = D.connectedDiagramContribution S :=
      D.cumulantFromMoment_diagramMoment hS
    _ = ∑ d : ConnectedQuarticWickDiagram Mode N S,
        quarticWickDiagramAmplitude ε β g d.1 := by
      simpa only [D] using
        quarticWickDiagramWeightedFamily_connectedDiagramContribution ε β g S

end SecondQuantization
