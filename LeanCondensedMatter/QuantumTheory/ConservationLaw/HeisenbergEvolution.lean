import LeanCondensedMatter.Analysis.ConservationLaw.BalanceLaw
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Heisenberg evolution for abstract balance laws

This module supplies only the quantum-mechanical normalization of algebraic commutator evolution:

```text
δₕ(A) = (i / ℏ) [h,A].
```

It does not choose a localization map, transported quantity, position observable, velocity, or
current representation. An existing represented balance law is normalized directly, scaling its
chosen current and source together with the evolution. No temporary intrinsic representation is
required for this operation.
-/

namespace QuantumTheory
namespace ConservationLaw

attribute [local instance 100] LieRing.ofAssociativeRing

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Scalar converting a commutator with the Hamiltonian into the Heisenberg derivative. -/
noncomputable def heisenbergScale (ℏ : ℝ) : ℂ :=
  Complex.I / (ℏ : ℂ)

/-- Heisenberg evolution as a linear endomorphism of the one-body operator space. -/
noncomputable def heisenbergEvolution
    (ℏ : ℝ) (h : V →ₗ[ℂ] V) :
    (V →ₗ[ℂ] V) →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  heisenbergScale ℏ • LieAlgebra.ad ℂ (Module.End ℂ V) h

@[simp]
theorem heisenbergEvolution_apply
    (ℏ : ℝ) (h A : V →ₗ[ℂ] V) :
    heisenbergEvolution V ℏ h A =
      heisenbergScale ℏ • ⁅h, A⁆ :=
  rfl

/-- Normalize a represented algebraic balance law to physical Heisenberg evolution by scaling
its chosen current and source directly. -/
noncomputable def heisenbergBalanceLaw
    {Test OneForm : Type*}
    [AddCommGroup Test] [Module ℂ Test]
    [AddCommGroup OneForm] [Module ℂ OneForm]
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (Q : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (d : Test →ₗ[ℂ] OneForm)
    (B : _root_.ConservationLaw.BalanceLaw
      (LieAlgebra.ad ℂ (Module.End ℂ V) h) Q d) :
    _root_.ConservationLaw.BalanceLaw (heisenbergEvolution V ℏ h) Q d where
  current := heisenbergScale ℏ • B.current
  source := heisenbergScale ℏ • B.source
  balance := by
    intro f
    change
      (heisenbergScale ℏ • LieAlgebra.ad ℂ (Module.End ℂ V) h) (Q f) =
        (heisenbergScale ℏ • B.current) (d f) +
          (heisenbergScale ℏ • B.source) f
    simp only [LinearMap.smul_apply]
    rw [B.balance f]
    exact smul_add (heisenbergScale ℏ) (B.current (d f)) (B.source f)

end ConservationLaw
end QuantumTheory
