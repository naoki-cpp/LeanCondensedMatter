import LeanCondensedMatter.Transport.FiniteConductivityTable
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.Table
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Channel

set_option linter.style.header false

/-!
# Conductivity evaluation data from an eigenbasis response channel

This adapter constructs scalar Lehmann data and the observable-variation expectation from
a supplied energy eigenbasis and response channel. It is independent of particle statistics,
Fock space, lattice geometry, and the physical realization of measured and source operators.
The scalar evaluator remains in `Transport.FiniteConductivityTable` without operator dependencies.
Physical use as electrical conductivity requires appropriate current/source conventions.
-/

namespace QuantumTheory.Transport

open LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar evaluation data for the measured/source operators and observable variation of a
supplied channel in an eigenbasis state. -/
noncomputable def finiteConductivityTableOfEigenbasis
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (channel : ResponseChannel H) : FiniteConductivityTable ι where
  lehmann := finiteLehmannTableOfEigenbasis system data channel.measured channel.source
  contact := eigenbasisNormalizedExpectation system data channel.observableVariation

/-- Generic table evaluation preserves the aggregate eigenbasis response, contact, and the
explicit volume/electric-field normalization. -/
theorem finiteConductivityTableValue_ofEigenbasis
    [Fintype ι]
    (volume : PositiveVolume)
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (channel : ResponseChannel H) (omega eta : ℝ) :
    finiteConductivityTableValue volume system.hbar omega eta
        (finiteConductivityTableOfEigenbasis system data channel) =
      (eigenbasisLehmannSeries system data channel.measured channel.source omega eta +
        eigenbasisNormalizedExpectation system data channel.observableVariation) *
        finiteVolumeConductivityNormalization volume omega eta := by
  unfold finiteConductivityTableValue finiteConductivityTableOfEigenbasis
  rw [finiteLehmannTableResponse_ofEigenbasis]

end
end QuantumTheory.Transport
