import LeanCondensedMatter.Analysis.Calculus.BalanceLaw
import LeanCondensedMatter.Analysis.Operator.LinearCommutator

set_option linter.style.header false

/-!
# Heisenberg evolution for abstract balance laws

This module supplies only the quantum-mechanical normalization of algebraic commutator evolution:

```text
δₕ(A) = (i / ℏ) [h,A].
```

It does not choose a localization map, transported quantity, position observable, velocity, or
current representation. Any algebraic `BalanceLaw` for commutator evolution can be scaled into its
Heisenberg form.
-/

namespace QuantumTheory
namespace ConservationLaw

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Scalar converting a commutator with the Hamiltonian into the Heisenberg derivative. -/
noncomputable def heisenbergScale (ℏ : ℝ) : ℂ :=
  Complex.I / (ℏ : ℂ)

/-- Heisenberg evolution as a linear endomorphism of the one-body operator space. -/
noncomputable def heisenbergEvolution
    (ℏ : ℝ) (h : V →ₗ[ℂ] V) :
    (V →ₗ[ℂ] V) →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  heisenbergScale ℏ • _root_.ConservationLaw.commutatorEvolution h

@[simp]
theorem heisenbergEvolution_apply
    (ℏ : ℝ) (h A : V →ₗ[ℂ] V) :
    heisenbergEvolution V ℏ h A =
      heisenbergScale ℏ • _root_.ConservationLaw.linearCommutator h A :=
  rfl

/-- Any balance law for algebraic commutator evolution acquires the physical Heisenberg
normalization by scaling both its current and source. -/
noncomputable def heisenbergBalanceLaw
    {Test OneForm : Type*}
    [AddCommGroup Test] [Module ℂ Test]
    [AddCommGroup OneForm] [Module ℂ OneForm]
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (Q : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (d : Test →ₗ[ℂ] OneForm)
    (B : _root_.ConservationLaw.BalanceLaw
      (_root_.ConservationLaw.commutatorEvolution h) Q d) :
    _root_.ConservationLaw.BalanceLaw (heisenbergEvolution V ℏ h) Q d := by
  change _root_.ConservationLaw.BalanceLaw
    (heisenbergScale ℏ • _root_.ConservationLaw.commutatorEvolution h) Q d
  exact B.scaleEvolution (heisenbergScale ℏ)

end ConservationLaw
end QuantumTheory
