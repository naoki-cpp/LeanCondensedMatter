import LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteEvaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.FiniteConductivityTable

set_option linter.style.header false

/-!
# Public finite conductivity evaluation boundary

This module is the electrical-conductivity specialization of the public finite-response workflow.
After a finite fermionic model has supplied a scalar current-current Lehmann table and contact
expectation, `FiniteConductivityProblem` bundles only

```text
finite table, physical volume, ℏ, ω, η
```

and evaluates the already-proved finite conductivity formula.  No new Kubo or conductivity
convention is introduced here: `FiniteConductivityProblem.value` is exactly
`finiteConductivityTableValue`.

The pure-point constructor connects this calculation-facing input to the existing Peierls current,
contact, and finite Kubo–Greenwood theorem.  Generic mixed responses such as later spin-current /
charge-current calculations can continue to use `QuantumTheory.LinearResponse.FiniteResponseProblem`
directly, while ordinary electrical conductivity uses this contact-aware wrapper.

Like the generic boundary, this is theorem-level exact data in `ℝ`/`ℂ`.  It intentionally has no
floating-point or numerical approximation semantics; a future computational backend should be a
separate downstream layer with explicit approximation/error guarantees.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice
open QuantumTheory.LinearResponse

noncomputable section

/-- Complete scalar input for one exact finite electrical-conductivity evaluation. -/
structure FiniteConductivityProblem (ι : Type*) where
  /-- Finite current-current Lehmann data together with the explicit contact expectation. -/
  table : FiniteConductivityTable ι
  /-- Positive physical volume used in the current-density/electric-field normalization. -/
  volume : QuantumTheory.Transport.PositiveVolume
  /-- Reduced Planck constant used by the Lehmann kernel. -/
  hbar : ℝ
  /-- Observation/driving angular frequency. -/
  omega : ℝ
  /-- Positive-rate/broadening parameter retained explicitly by the evaluator. -/
  eta : ℝ

/-- Evaluate a bundled finite conductivity problem with the existing scalar conductivity table. -/
noncomputable def FiniteConductivityProblem.value
    {ι : Type*} [Fintype ι] (problem : FiniteConductivityProblem ι) : ℂ :=
  finiteConductivityTableValue
    problem.volume problem.hbar problem.omega problem.eta problem.table

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Package a proved finite pure-point Peierls conductivity problem into the public scalar input. -/
noncomputable def finiteDirectionalConductivityProblemOfPurePoint
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    FiniteConductivityProblem ι where
  table := finiteDirectionalConductivityTableOfPurePoint
    system data geometry direction K q
  volume := volume
  hbar := system.hbar
  omega := omega
  eta := eta

/-- Evaluating the packaged scalar conductivity problem obtained from pure-point Peierls data is
exactly the existing finite Kubo–Greenwood directional conductivity. -/
theorem finiteDirectionalConductivityProblemOfPurePoint_value
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    (finiteDirectionalConductivityProblemOfPurePoint
      volume system data geometry direction K q omega eta).value =
      finiteKuboGreenwoodDirectionalConductivity
        volume system data geometry direction K q omega eta := by
  simpa [FiniteConductivityProblem.value,
    finiteDirectionalConductivityProblemOfPurePoint] using
    finiteConductivityTableValue_directional_ofPurePoint_eq_kuboGreenwood
      volume system data geometry direction K q omega eta

end
end Transport
end Fermionic
end SecondQuantization
