import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Amplitude

set_option linter.style.header false

/-!
# Ordered-simplex amplitudes of external-insertion diagrams

Integrate one diagram's fixed-time amplitude, with or without the Dyson sign, using either its
consecutive interaction slots or an explicit interaction order. Component factorization and
shuffle sums are separate consumers of these amplitudes.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Ordered-simplex contribution of one arbitrary external-insertion diagram, before the Dyson
sign. -/
noncomputable def ExternalInsertionWickDiagram.orderedSimplexContribution
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) : ℂ :=
  intervalIntegral.orderedSimplexIntegral n β
    (fun σ => d.fixedTimeAmplitude ε β g externalTime σ)

/-- Integrated arbitrary-external-insertion amplitude including the order-`n` Dyson sign. -/
noncomputable def ExternalInsertionWickDiagram.dysonAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) : ℂ :=
  (-1 : ℂ) ^ n * d.orderedSimplexContribution ε β g externalTime


/-- Dyson amplitude with the interaction vertices assigned to the ordered-simplex slots by an
explicit global interaction order. -/
noncomputable def ExternalInsertionWickDiagram.orderedDysonAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin n))) : ℂ :=
  intervalIntegral.orderedSimplexIntegral
    (Finset.univ : Finset (Fin n)).card β
    (fun τ =>
      d.dysonFixedTimeAmplitude ε β g externalTime
        (fun v => τ (order.symm ⟨v, Finset.mem_univ v⟩)))

/-- Integrating the Dyson-signed fixed-time amplitude is the integrated Dyson amplitude. -/
theorem ExternalInsertionWickDiagram.orderedSimplexIntegral_dysonFixedTimeAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    intervalIntegral.orderedSimplexIntegral n β
        (fun σ => d.dysonFixedTimeAmplitude ε β g externalTime σ) =
      d.dysonAmplitude ε β g externalTime := by
  unfold ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
    ExternalInsertionWickDiagram.dysonAmplitude
    ExternalInsertionWickDiagram.orderedSimplexContribution
  exact intervalIntegral.orderedSimplexIntegral_smul n β
    ((-1 : ℂ) ^ n) (fun σ => d.fixedTimeAmplitude ε β g externalTime σ)

end Fermionic
end SecondQuantization
