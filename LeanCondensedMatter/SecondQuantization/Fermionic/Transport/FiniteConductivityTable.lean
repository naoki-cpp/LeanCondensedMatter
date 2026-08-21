import LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteLehmannTable
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboGreenwood

set_option linter.style.header false

/-!
# Finite scalar conductivity evaluation tables

This module is the electrical-conductivity specialization of the finite scalar Lehmann table.
The theorem-level Kubo chain already derives the finite Kubo–Greenwood expression from causal
response, the continuity-derived Peierls current, the explicit contact variation, and the
finite-volume electric-field normalization.

For small benchmark models, only the scalar spectral current table and the scalar contact
expectation are needed after that derivation.  `FiniteConductivityTable` therefore stores

```text
Eₙ, pₙ, Jₘₙ, Jₙₘ, ⟨C⟩,
```

through a `FiniteLehmannTable` plus one contact value.  Its evaluator keeps `ℏ`, driving frequency
`ω`, switching rate `η`, and positive physical volume explicit and reuses the existing
`finiteVolumeConductivityNormalization` convention.

The main theorem constructs this scalar table from a finite pure-point hopping model and proves
that its value is exactly `finiteKuboGreenwoodDirectionalConductivity`.  Thus this is a calculation
boundary for concrete finite models, not a second definition of electrical conductivity.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

/-- Scalar data sufficient to evaluate a finite electrical conductivity once the operator-level
Kubo theorem has supplied the current and contact observables. -/
structure FiniteConductivityTable (ι : Type*) where
  /-- Finite spectral current-current Lehmann data. -/
  lehmann : FiniteLehmannTable ι
  /-- Scalar expectation of the explicit Peierls/contact operator. -/
  contact : ℂ

/-- Evaluate the finite electrical conductivity from a scalar Lehmann table and contact value.

The conversion from vector-potential response to current-density/electric-field response uses the
same positive-volume normalization as the proved finite Kubo–Greenwood theorem. -/
noncomputable def finiteConductivityTableValue
    {ι : Type*} [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (hbar omega eta : ℝ) (table : FiniteConductivityTable ι) : ℂ :=
  (finiteLehmannTableResponse hbar omega eta table.lehmann + table.contact) *
    finiteVolumeConductivityNormalization volume omega eta

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Forget a finite pure-point Peierls conductivity problem to the scalar data needed for exact
finite evaluation. -/
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

/-- Evaluating the scalar table obtained from a finite pure-point hopping model gives exactly the
existing finite Kubo–Greenwood conductivity, including contact and finite-volume normalization. -/
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
