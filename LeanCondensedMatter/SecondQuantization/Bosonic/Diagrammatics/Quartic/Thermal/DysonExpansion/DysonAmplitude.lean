import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.Amplitude
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.QuarticDysonExpansion

set_option linter.style.header false

/-!
# Time-integrated bosonic quartic diagram amplitudes

A chosen vertex order supplies the scalar Dyson coefficient and the thermal pairing
value in the same coordinates. Summing these amplitudes over all vertex orders retains
the ordered-simplex regions used by connected-component factorization. Gibbs expectation
identities are supplied separately by the physical Dyson-to-pairing expansion.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*}

/-- Fixed-order physical quartic Dyson diagram amplitude. The scalar Dyson sequence coefficient
contains the ordered-simplex time integration and coupling product, while the diagram contributes
one concrete bosonic thermal pairing value in the same vertex order. -/
noncomputable def QuarticDiagram.orderedDysonThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) (t : ℝ) : ℂ :=
  Common.quarticDysonSequenceCoeff ε g (fun i => d.vertexLabel (order i)) t *
    QuarticDiagram.orderedThermalPairingValue ε β d order

/-- Physical bosonic quartic Dyson diagram amplitude, summed over all global vertex orders.
The ordered-simplex regions associated with these orders are the pieces that shuffle-factorize over
connected components, so this physical amplitude is a sum over orders, with no factorial
averaging. -/
noncomputable def QuarticDiagram.dysonThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S) (t : ℝ) : ℂ :=
  ∑ order : Common.QuarticVertexOrder S,
    QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t

end
end Bosonic
end SecondQuantization
