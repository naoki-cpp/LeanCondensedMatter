import LeanCondensedMatter.Transport.Core.FiniteConductivityTable
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboGreenwood

set_option linter.style.header false

/-!
# Fermionic directional finite-conductivity table realization

The representation-independent scalar conductivity table and evaluator now live in
`QuantumTheory.Transport.Core.FiniteConductivityTable`. This module retains only the finite-lattice
fermionic realization: it constructs that canonical scalar table from a pure-point Peierls
conductivity problem and proves that evaluating it reproduces the existing finite
Kubo–Greenwood directional conductivity.

The directional realization supplies the continuity-derived Peierls current and explicit contact
expectation. The table storage, scalar Lehmann evaluation, positive-volume normalization, and
electric-field conversion are owned upstream and are not redefined here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Forget a finite pure-point Peierls conductivity problem to the generic scalar data needed for
exact finite evaluation. -/
noncomputable def finiteDirectionalConductivityTableOfPurePoint
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) : FiniteConductivityTable ι :=
  let J := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  { lehmann := finiteLehmannTableOfPurePoint system data J J
    contact := purePointNormalizedExpectation system data
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K) }

/-- Evaluating the generic scalar table obtained from a finite pure-point hopping model gives
exactly the existing finite Kubo–Greenwood conductivity, including contact and finite-volume
normalization. -/
theorem finiteConductivityTableValue_directional_ofPurePoint_eq_kuboGreenwood
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteConductivityTableValue volume system.hbar omega eta
        (finiteDirectionalConductivityTableOfPurePoint
          system data geometry direction K q) =
      finiteKuboGreenwoodDirectionalConductivity
        volume system data geometry direction K q omega eta := by
  unfold finiteConductivityTableValue finiteKuboGreenwoodDirectionalConductivity
  unfold finiteDirectionalConductivityTableOfPurePoint
  rw [finiteLehmannTableResponse_ofPurePoint]
  rw [purePointLehmannSeries_eq_finite_sum]
  rfl

end
end Transport
end Fermionic
end SecondQuantization
