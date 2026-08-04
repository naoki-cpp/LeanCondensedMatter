import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basic

set_option linter.style.header false

/-!
# Basis-independent fermionic finite-particle Fock space

This module begins issue #524's basis-independent fermionic field line.

For an arbitrary complex one-particle Hilbert space `𝓗₁`, the algebraic finite-particle
fermionic Fock space is represented by the exterior algebra

```text
Λ(𝓗₁) = ⨁ₙ Λⁿ(𝓗₁).
```

The construction does not assume that `𝓗₁` is finite-dimensional or that an orthonormal basis has
been chosen. It is deliberately algebraic: Hilbert completion of the full Fock space and the domain
theory of generally unbounded second-quantized operators are separate later layers.

This representation complements rather than replaces `Fermionic.FockSpace Mode`, the existing
occupation-basis realization. A future comparison theorem will relate the two after choosing an
orthonormal basis of the one-particle space.
-/

namespace SecondQuantization
namespace Fermionic
namespace BasisIndependent

noncomputable section

variable (𝓗₁ : Type*) [NormedAddCommGroup 𝓗₁] [InnerProductSpace ℂ 𝓗₁]

/-- The algebraic finite-particle fermionic Fock space over `𝓗₁`.

Every element is a finite algebraic sum of homogeneous exterior-degree components. No
finite-dimensionality or chosen basis is required. -/
abbrev FiniteParticleFock := ExteriorAlgebra ℂ 𝓗₁

/-- The `n`-particle sector inside the algebraic finite-particle Fock space. -/
abbrev ParticleSector (n : ℕ) := ⋀[ℂ]^n 𝓗₁

/-- The Fock vacuum, represented by the multiplicative unit in exterior degree zero. -/
def vacuum : FiniteParticleFock 𝓗₁ := 1

/-- The canonical embedding of a one-particle vector into exterior degree one. -/
def oneParticle : 𝓗₁ →ₗ[ℂ] FiniteParticleFock 𝓗₁ :=
  ExteriorAlgebra.ι ℂ

@[simp]
theorem oneParticle_apply (f : 𝓗₁) :
    oneParticle 𝓗₁ f = ExteriorAlgebra.ι ℂ f :=
  rfl

end
end BasisIndependent
end Fermionic
end SecondQuantization
