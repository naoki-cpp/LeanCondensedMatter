import LeanCondensedMatter.Transport.Core.FiniteConductivityTable
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboGreenwood

set_option linter.style.header false

/-!
# Fermionic finite-conductivity table realization

The representation-independent scalar conductivity table and evaluator live in
`QuantumTheory.Transport.Core.FiniteConductivityTable`. This module retains the finite-lattice
fermionic realization: it constructs that canonical scalar table from a pure-point Peierls
conductivity problem with independent measured-current and source-field directions.

The historical one-direction realization is the diagonal specialization. Table storage, scalar
Lehmann evaluation, positive-volume normalization, and electric-field conversion remain owned
upstream and are not redefined here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Forget a finite pure-point Peierls conductivity component to the generic scalar data needed for
exact finite evaluation. The first direction selects the measured current and the second selects the
uniform source field. -/
noncomputable def finiteConductivityComponentTableOfPurePoint
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) : FiniteConductivityTable ι :=
  let measured := boundedDirectionalCurrent geometry measuredDirection
    (system.hbar : ℂ) (q : ℂ) K
  let source := boundedDirectionalCurrent geometry sourceDirection
    (system.hbar : ℂ) (q : ℂ) K
  { lehmann := finiteLehmannTableOfPurePoint system data measured source
    contact := purePointNormalizedExpectation system data
      (boundedMixedDirectionalContact geometry measuredDirection sourceDirection
        (system.hbar : ℂ) (q : ℂ) K) }

/-- Forget a diagonal finite pure-point Peierls conductivity problem to the generic scalar data
needed for exact finite evaluation. -/
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

/-- The component table reduces to the historical directional table on the diagonal. -/
@[simp]
theorem finiteConductivityComponentTableOfPurePoint_self
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) :
    finiteConductivityComponentTableOfPurePoint
        system data geometry direction direction K q =
      finiteDirectionalConductivityTableOfPurePoint
        system data geometry direction K q := by
  simp [finiteConductivityComponentTableOfPurePoint,
    finiteDirectionalConductivityTableOfPurePoint]

/-- Evaluating the generic scalar table for one conductivity component gives exactly the finite
Kubo–Greenwood component, including the mixed contact term and finite-volume normalization. -/
theorem finiteConductivityTableValue_component_ofPurePoint_eq_kuboGreenwood
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteConductivityTableValue volume system.hbar omega eta
        (finiteConductivityComponentTableOfPurePoint
          system data geometry measuredDirection sourceDirection K q) =
      finiteKuboGreenwoodConductivityComponent
        volume system data geometry measuredDirection sourceDirection K q omega eta := by
  unfold finiteConductivityTableValue finiteKuboGreenwoodConductivityComponent
  unfold finiteConductivityComponentTableOfPurePoint
  rw [finiteLehmannTableResponse_ofPurePoint]
  rw [purePointLehmannSeries_eq_finite_sum]
  rfl

/-- Evaluating the generic scalar table obtained from a diagonal finite pure-point hopping model
gives exactly the existing finite Kubo–Greenwood directional conductivity. -/
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
