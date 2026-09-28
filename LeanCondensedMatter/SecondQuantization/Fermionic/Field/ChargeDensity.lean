import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantization

set_option linter.style.header false

/-!
# Basis-independent smeared fermionic charge density

Let `Test` be a complex vector space of smearing functions or discrete observables, and let

```text
M : Test →ₗ[ℂ] End(𝓗₁)
```

assign the corresponding one-particle density observable. For charge `q`, define

```text
ρ(f) = q dΓ(M f).
```

No concrete position-space multiplication operator is assumed. This interface covers continuum
multiplication operators once their analytic domain is supplied, and finite lattice site observables
without introducing unnecessary analytic hypotheses.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]
variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The smeared many-particle charge density induced by a linear family `M` of one-particle density
observables.

The result is linear in the smearing observable. -/
noncomputable def chargeDensity (q : ℂ)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) :
    Test →ₗ[ℂ]
      (AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) :=
  q • (AlgebraicFock.dGammaLinear 𝓗₁).comp M

@[simp]
theorem chargeDensity_apply (q : ℂ)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (f : Test) :
    chargeDensity 𝓗₁ q M f = q • AlgebraicFock.dGamma 𝓗₁ (M f) :=
  rfl

end Field
end Fermionic
end SecondQuantization
