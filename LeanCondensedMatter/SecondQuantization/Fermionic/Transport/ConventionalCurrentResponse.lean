import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity.ConventionalCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedCurrentResponse

set_option linter.style.header false

/-!
# Bounded conventional-current response adapters

This module specializes the generic bounded one-body-current response boundary to the conventional
current

```text
jᵐ = 1/2 {v,m}.
```

The generic `BoundedCurrentResponse` module intentionally does not depend on this representation.
Use this module only after the generalized balance-law layer has justified the conventional current
for the internal/local quantity under study.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- Bounded realization of the conventional generalized current `jᵐ = 1/2 {v,m}`. -/
noncomputable def boundedConventionalCurrent
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyCurrent
    (Field.conventionalCurrent (LatticeState Site) velocity m)

@[simp]
theorem boundedConventionalCurrent_smul_id
    (velocity : LatticeState Site →ₗ[ℂ] LatticeState Site) (q : ℂ) :
    boundedConventionalCurrent velocity (q • LinearMap.id) =
      q • boundedOneBodyCurrent velocity := by
  rw [boundedConventionalCurrent,
    Field.conventionalCurrent_smul_id,
    boundedOneBodyCurrent_smul]

/-- Kubo response of the conventional current `1/2 {v,m}` when that current representation has
been justified by the upstream generalized-balance-law hypotheses. -/
noncomputable def boundedConventionalCurrentRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (t s : ℝ) : ℂ :=
  boundedMeasuredCurrentRetardedSusceptibility system expectation
    (boundedConventionalCurrent velocity m) source t s

/-- The charge-like internal quantity `m = q I` reduces the bounded conventional current to `qv`. -/
theorem boundedConventionalCurrentRetardedSusceptibility_smul_id
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (velocity : LatticeState Site →ₗ[ℂ] LatticeState Site) (q : ℂ)
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (t s : ℝ) :
    boundedConventionalCurrentRetardedSusceptibility system expectation
        velocity (q • LinearMap.id) source t s =
      boundedMeasuredCurrentRetardedSusceptibility system expectation
        (q • boundedOneBodyCurrent velocity) source t s := by
  rw [boundedConventionalCurrentRetardedSusceptibility,
    boundedConventionalCurrent_smul_id]

end
end Transport
end Fermionic
end SecondQuantization
