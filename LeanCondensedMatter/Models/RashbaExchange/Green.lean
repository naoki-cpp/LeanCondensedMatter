import LeanCondensedMatter.Models.RashbaExchange.Operator
import LeanCondensedMatter.Models.RashbaExchange.ResponseParameters
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced

set_option linter.style.header false

/-!
# Finite-broadening Green operators for the Rashba-exchange model

The clean bounded Hamiltonian is defined in `Operator` and the chemical potential and
broadening are supplied by `ResponseParameters`. This module realizes retarded/advanced
resolvents through the generic Středa resolvent API without importing charge-current vertices.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

open QuantumTheory.Transport

/-- Canonical retarded or advanced Green resolvent at the chemical potential. -/
noncomputable def greenOperator
    (side : SpectralSide) (params : Parameters) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  match side with
  | .retarded =>
      retardedResolvent (hamiltonianOperator params px py)
        params.chemicalPotential params.broadening
  | .advanced =>
      advancedResolvent (hamiltonianOperator params px py)
        params.chemicalPotential params.broadening

end
end QuantumTheory.Models.RashbaExchange
