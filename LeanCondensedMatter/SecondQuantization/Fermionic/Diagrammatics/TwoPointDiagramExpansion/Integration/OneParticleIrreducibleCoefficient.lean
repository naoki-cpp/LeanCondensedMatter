import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramIntegral
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.OneParticleIrreducible

set_option linter.style.header false

/-!
# One-particle-irreducible two-point Dyson coefficients

Select the proper 1PI diagrams from the same fixed-external finite Wick-diagram family used
by the connected two-point expansion, retaining their existing integrated Dyson amplitudes.

These are still *unamputated* imaginary-time two-point amplitudes. They are not asserted to
equal the proper self-energy: doing so requires an external-leg amputation/transform and a
factorization proof reconstructing the connected two-point series from 1PI insertions.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

open Classical in
/-- The order-`n` integrated two-point contribution from proper 1PI pairing diagrams. -/
noncomputable def oneParticleIrreducibleTwoPointDysonCoefficient (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)).filter
      fun d => d.1.IsOneParticleIrreducible,
    d.dysonAmplitude ε β g τ τ'

end Fermionic
end SecondQuantization
