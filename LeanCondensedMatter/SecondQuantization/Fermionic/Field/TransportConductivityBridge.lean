import LeanCondensedMatter.Transport.System
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ConductivityNormalization

set_option linter.style.header false

/-!
# Bridge from transport volume data to field conductivity

The transport convention layer stores finite physical volume independently of the model-specific
fermionic current construction. This module reuses that volume in the explicit conductivity
normalization introduced by the finite-lattice Peierls response.

The bridge copies only the volume and its positivity proof. Hamiltonian and current compatibility
remain separate theorem obligations for later transport-model adapters.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Use the finite volume stored by a general transport system in the field conductivity
normalization. -/
def FiniteVolumeConductivityConvention.ofTransportSystem
    (system : QuantumTheory.Transport.FiniteVolumeSystem H) :
    FiniteVolumeConductivityConvention where
  volume := system.volume
  volume_pos := system.volume_pos

@[simp]
theorem FiniteVolumeConductivityConvention.ofTransportSystem_volume
    (system : QuantumTheory.Transport.FiniteVolumeSystem H) :
    (FiniteVolumeConductivityConvention.ofTransportSystem system).volume = system.volume :=
  rfl

end
end Field
end Fermionic
end SecondQuantization
