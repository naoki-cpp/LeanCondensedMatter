import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

set_option linter.style.header false

/-!
# Basis-independent finite-particle fermionic Fock space

This module starts the field-theoretic line tracked by issue #524. For a complex one-particle
space `𝓗₁`, the algebraic finite-particle fermionic Fock space is represented by the exterior
algebra

```text
Λ(𝓗₁) = ⨁ₙ^alg Λⁿ(𝓗₁).
```

The construction is basis-independent and does not require `𝓗₁` to be finite-dimensional. At this
layer only the complex vector-space structure is needed. An inner product and completeness belong
to later modules that define smeared annihilation fields and analytic Hilbert-space realizations.

This is deliberately separate from `Fermionic.FockSpace Mode`, which is the free vector space on
finite occupation subsets of a chosen ordered mode type. A comparison between the two
representations requires a chosen basis and is deferred until the field operators are in place.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The basis-independent algebraic fermionic Fock space over the one-particle space `𝓗₁`.

Every element is a finite algebraic combination of finite wedge products. This is not the completed
Hilbert direct sum and carries no claim that general second-quantized Hamiltonians are bounded. -/
abbrev FiniteParticleFock := ExteriorAlgebra ℂ 𝓗₁

/-- The homogeneous `n`-particle sector inside `FiniteParticleFock 𝓗₁`. -/
abbrev ParticleSector (n : ℕ) := ⋀[ℂ]^n 𝓗₁

/-- The Fock vacuum, represented by the multiplicative unit of the exterior algebra. -/
def vacuum : FiniteParticleFock 𝓗₁ := 1

/-- The canonical basis-independent embedding of one-particle states into Fock space. -/
abbrev oneParticle : 𝓗₁ →ₗ[ℂ] FiniteParticleFock 𝓗₁ :=
  ExteriorAlgebra.ι ℂ

/-- The one-particle embedding is injective, without any finite-dimensionality assumption. -/
theorem oneParticle_injective : Function.Injective (oneParticle 𝓗₁) := by
  intro f g h
  exact (ExteriorAlgebra.ι_inj ℂ f g).mp h

/-- The vacuum is nonzero. -/
@[simp]
theorem vacuum_ne_zero : vacuum 𝓗₁ ≠ 0 := by
  exact one_ne_zero

end Field
end Fermionic
end SecondQuantization
