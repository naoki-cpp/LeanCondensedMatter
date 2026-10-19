import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramIntegral
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.OneParticleIrreducible

set_option linter.style.header false

/-!
# Selected two-point Dyson coefficients

Coefficients of the integrated two-point Dyson expansion, restricted to externally connected
or proper one-particle-irreducible diagrams. The summands share the canonical integrated Dyson
amplitude; the selection conditions are independent combinatorial predicates.

The proper 1PI sum still contains *unamputated* imaginary-time two-point amplitudes. Identifying
it with a self-energy requires external-leg amputation and the corresponding factorization proof.
Formal power-series packaging belongs to `Series/DysonSeries.lean`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

open Classical in
/-- The order-`n` coefficient of the connected two-point series: the integrated Dyson amplitudes of
the externally connected diagrams only. -/
noncomputable def connectedTwoPointDysonCoefficient (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)).filter
      fun d => d.1.IsExternallyConnected,
    d.dysonAmplitude ε β g τ τ'

open Classical in
/-- The order-`n` integrated two-point contribution from proper 1PI pairing diagrams. -/
noncomputable def oneParticleIrreducibleTwoPointDysonCoefficient (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)).filter
      fun d => d.1.IsOneParticleIrreducible,
    d.dysonAmplitude ε β g τ τ'

end Fermionic
end SecondQuantization
