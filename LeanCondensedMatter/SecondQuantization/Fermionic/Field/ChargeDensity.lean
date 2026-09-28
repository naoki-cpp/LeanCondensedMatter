import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationCommutator

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

attribute [local instance 100] LieRing.ofAssociativeRing

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

/-- Every smeared charge density kills the vacuum. -/
theorem chargeDensity_vacuum (q : ℂ)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (f : Test) :
    chargeDensity 𝓗₁ q M f (AlgebraicFock.vacuum 𝓗₁) = 0 := by
  simp [chargeDensity]

/-- The commutator of a second-quantized Hamiltonian with smeared charge density is the second
quantization of the one-particle commutator. -/
theorem dGamma_commutator_chargeDensity (q : ℂ)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    ⁅AlgebraicFock.dGamma 𝓗₁ h, chargeDensity 𝓗₁ q M f⁆ =
      q • AlgebraicFock.dGamma 𝓗₁ ⁅h, M f⁆ := by
  rw [chargeDensity_apply, lie_smul, AlgebraicFock.dGamma_lie]

/-- Algebraic Heisenberg-form identity for smeared charge density:

```text
(i / ℏ) [dΓ(h), ρ(f)] = (i q / ℏ) dΓ([h, M(f)]).
```

This identity is purely algebraic. Analytic domain assumptions for an unbounded Schrödinger
Hamiltonian or continuum multiplication operator belong to the weak-continuity layer. -/
theorem heisenberg_commutator_chargeDensity (ℏ q : ℂ)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    (Complex.I / ℏ) •
        ⁅AlgebraicFock.dGamma 𝓗₁ h, chargeDensity 𝓗₁ q M f⁆ =
      ((Complex.I * q) / ℏ) •
        AlgebraicFock.dGamma 𝓗₁ ⁅h, M f⁆ := by
  rw [dGamma_commutator_chargeDensity]
  rw [smul_smul]
  congr 1
  ring

end Field
end Fermionic
end SecondQuantization
