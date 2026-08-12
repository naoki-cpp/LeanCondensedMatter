import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

set_option linter.style.header false

/-!
# Basis-independent algebraic fermionic Fock space

For a complex one-particle space `𝓗₁`, the algebraic fermionic Fock space is the exterior algebra

```text
Λ(𝓗₁) = ⨁ₙ^alg Λⁿ(𝓗₁).
```

The construction is basis-independent and does not require finite-dimensionality. It is deliberately
algebraic: it is not the completed Hilbert direct sum, and general second-quantized operators are not
assumed bounded. The occupation-subset representation is related to this space only after choosing a
linearly ordered one-particle basis.
-/

namespace SecondQuantization
namespace Fermionic

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The basis-independent algebraic fermionic Fock space over the one-particle space `𝓗₁`.

Every element is a finite algebraic combination of finite wedge products. This is not the completed
Hilbert direct sum and carries no claim that general second-quantized Hamiltonians are bounded. -/
abbrev AlgebraicFock := ExteriorAlgebra ℂ 𝓗₁

namespace AlgebraicFock

/-- The homogeneous `n`-particle sector inside `AlgebraicFock 𝓗₁`. -/
abbrev ParticleSector (n : ℕ) := ⋀[ℂ]^n 𝓗₁

/-- The Fock vacuum, represented by the multiplicative unit of the exterior algebra. -/
def vacuum : AlgebraicFock 𝓗₁ := 1

/-- The canonical basis-independent embedding of one-particle states into Fock space. -/
abbrev oneParticle : 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  ExteriorAlgebra.ι ℂ

/-- The one-particle embedding is injective, without any finite-dimensionality assumption. -/
theorem oneParticle_injective : Function.Injective (oneParticle 𝓗₁) := by
  intro f g h
  exact (ExteriorAlgebra.ι_inj ℂ f g).mp h

/-- The vacuum is nonzero. -/
@[simp]
theorem vacuum_ne_zero : vacuum 𝓗₁ ≠ 0 := by
  exact one_ne_zero

end AlgebraicFock
end Fermionic
end SecondQuantization
