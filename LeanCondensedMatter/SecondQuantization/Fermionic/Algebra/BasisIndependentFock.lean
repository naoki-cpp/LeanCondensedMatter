import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

set_option linter.style.header false

/-!
# Basis-independent fermionic finite-particle Fock space

This module begins issue #524's basis-independent fermionic field line.

For an arbitrary complex one-particle space `𝓗₁`, the algebraic finite-particle fermionic Fock
space is represented by the exterior algebra

```text
Λ(𝓗₁) = ⨁ₙ^alg Λⁿ(𝓗₁).
```

The construction does not assume that `𝓗₁` is finite-dimensional or that a basis has been chosen.
At this algebraic layer only the complex vector-space structure is required. An inner product enters
later when annihilation fields are defined by contraction; Hilbert completion and domains of
unbounded second-quantized operators remain separate analytic layers.

This representation complements rather than replaces `Fermionic.FockSpace Mode`, the existing
occupation-basis realization. A future comparison theorem will relate the two after choosing a basis
of the one-particle space.
-/

namespace SecondQuantization
namespace Fermionic
namespace BasisIndependent

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The algebraic finite-particle fermionic Fock space over `𝓗₁`.

Every element is a finite algebraic combination of finite wedge products. This is not the completed
Hilbert direct sum and carries no claim that general second-quantized Hamiltonians are bounded. -/
abbrev FiniteParticleFock := ExteriorAlgebra ℂ 𝓗₁

/-- The homogeneous `n`-particle sector inside the algebraic finite-particle Fock space. -/
abbrev ParticleSector (n : ℕ) := ⋀[ℂ]^n 𝓗₁

/-- The Fock vacuum, represented by the multiplicative unit in exterior degree zero. -/
def vacuum : FiniteParticleFock 𝓗₁ := 1

/-- The canonical basis-independent embedding of one-particle states into Fock space. -/
abbrev oneParticle : 𝓗₁ →ₗ[ℂ] FiniteParticleFock 𝓗₁ :=
  ExteriorAlgebra.ι ℂ

@[simp]
theorem oneParticle_apply (f : 𝓗₁) :
    oneParticle 𝓗₁ f = ExteriorAlgebra.ι ℂ f :=
  rfl

/-- The one-particle embedding is injective, without any finite-dimensionality assumption. -/
theorem oneParticle_injective : Function.Injective (oneParticle 𝓗₁) := by
  intro f g h
  exact (ExteriorAlgebra.ι_inj ℂ f g).mp h

/-- The vacuum is nonzero. -/
@[simp]
theorem vacuum_ne_zero : vacuum 𝓗₁ ≠ 0 := by
  exact one_ne_zero

end BasisIndependent
end Fermionic
end SecondQuantization
