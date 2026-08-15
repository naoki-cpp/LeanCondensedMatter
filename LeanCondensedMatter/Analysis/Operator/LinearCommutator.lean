import Mathlib.Tactic

set_option linter.style.header false

/-!
# Linear-map commutators

This module owns the ordinary commutator of complex-linear endomorphisms independently of any
particular quantum representation or second-quantization construction.

```text
[S,T] = S ∘ T - T ∘ S.
```

Second-quantization layers may prove functoriality of this operation, but should not own the
operation itself.
-/

namespace ConservationLaw

/-- Ordinary commutator of two complex-linear endomorphisms. -/
noncomputable def linearCommutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S T : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  S.comp T - T.comp S

@[simp]
theorem linearCommutator_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S T : V →ₗ[ℂ] V) (v : V) :
    linearCommutator S T v = S (T v) - T (S v) :=
  rfl

/-- A scalar multiple of the identity commutes with every complex-linear endomorphism. -/
@[simp]
theorem linearCommutator_smul_id_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : V →ₗ[ℂ] V) (q : ℂ) :
    linearCommutator S (q • LinearMap.id) = 0 := by
  apply LinearMap.ext
  intro v
  simp [linearCommutator]

end ConservationLaw
