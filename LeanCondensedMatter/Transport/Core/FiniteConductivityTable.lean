import LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteLehmannTable
import LeanCondensedMatter.Transport.Core.ConductivityNormalization

set_option linter.style.header false

/-!
# Finite scalar conductivity evaluation tables

This module owns the representation-independent scalar calculation boundary for finite electrical
conductivity. Once an operator-level response theorem has supplied finite Lehmann data and the
scalar expectation of any explicit observable/contact variation, evaluation requires only

```text
Eₙ, pₙ, Aₘₙ, Bₘₙ, ⟨C⟩,
```

plus the positive physical volume, driving frequency, switching rate, and `ℏ`.

`FiniteConductivityTable` therefore extends the generic finite Lehmann calculation boundary with one
scalar contact value. `finiteConductivityTableValue` evaluates that data using the canonical
finite-volume electric-field normalization from `Transport.Core.ConductivityNormalization`.

This layer is independent of particle statistics, Fock-space realization, lattice geometry, Peierls
currents, and any concrete model. Fermionic directional constructors remain downstream in
`SecondQuantization.Fermionic.Transport.FiniteConductivityTable`.
-/

namespace QuantumTheory
namespace Transport

open LinearResponse

noncomputable section

/-- Scalar data sufficient to evaluate a finite electrical conductivity once an operator-level
response theorem has supplied the measured/source Lehmann data and explicit contact variation. -/
structure FiniteConductivityTable (ι : Type*) where
  /-- Finite spectral measured/source Lehmann data. -/
  lehmann : FiniteLehmannTable ι
  /-- Scalar expectation of the explicit observable/contact variation. -/
  contact : ℂ

/-- Evaluate finite electrical conductivity from a scalar Lehmann table and contact value.

The conversion from vector-potential response to current-density/electric-field response uses the
canonical positive-volume normalization. -/
noncomputable def finiteConductivityTableValue
    {ι : Type*} [Fintype ι]
    (volume : PositiveVolume)
    (hbar omega eta : ℝ) (table : FiniteConductivityTable ι) : ℂ :=
  (finiteLehmannTableResponse hbar omega eta table.lehmann + table.contact) *
    finiteVolumeConductivityNormalization volume omega eta

end
end Transport
end QuantumTheory
