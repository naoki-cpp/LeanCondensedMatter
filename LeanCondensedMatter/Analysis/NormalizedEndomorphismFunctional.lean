import Mathlib.Algebra.Module.LinearMap.End

set_option linter.style.header false

/-!
# Normalized linear functionals on endomorphisms

A normalized endomorphism functional is a linear functional on `Module.End` that sends the identity
to `1`.  This is pure linear algebra: it does not depend on an occupation basis, a trace formula,
statistics, or a Gibbs interpretation.

Second-quantization code specializes this structure to endomorphisms of an algebraic Fock space.
-/

/-- A linear functional on endomorphisms, normalized by its value on the identity. -/
structure NormalizedEndomorphismFunctional (𝕜 : Type*) (V : Type*) [CommRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] where
  /-- The underlying linear functional. -/
  toLinearMap : Module.End 𝕜 V →ₗ[𝕜] 𝕜
  /-- The identity endomorphism has value `1`. -/
  map_id : toLinearMap LinearMap.id = 1

namespace NormalizedEndomorphismFunctional

variable {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

instance : CoeFun (NormalizedEndomorphismFunctional 𝕜 V)
    (fun _ => Module.End 𝕜 V → 𝕜) :=
  ⟨fun F => F.toLinearMap⟩

@[simp]
theorem toLinearMap_apply (F : NormalizedEndomorphismFunctional 𝕜 V)
    (A : Module.End 𝕜 V) : F.toLinearMap A = F A := rfl

theorem map_add (F : NormalizedEndomorphismFunctional 𝕜 V) (A B : Module.End 𝕜 V) :
    F (A + B) = F A + F B :=
  F.toLinearMap.map_add A B

theorem map_smul (F : NormalizedEndomorphismFunctional 𝕜 V) (c : 𝕜)
    (A : Module.End 𝕜 V) : F (c • A) = c * F A := by
  simpa only [smul_eq_mul] using F.toLinearMap.map_smul c A

@[simp]
theorem map_zero (F : NormalizedEndomorphismFunctional 𝕜 V) : F 0 = 0 :=
  F.toLinearMap.map_zero

theorem map_neg (F : NormalizedEndomorphismFunctional 𝕜 V) (A : Module.End 𝕜 V) :
    F (-A) = -F A :=
  F.toLinearMap.map_neg A

theorem map_sub (F : NormalizedEndomorphismFunctional 𝕜 V) (A B : Module.End 𝕜 V) :
    F (A - B) = F A - F B :=
  F.toLinearMap.map_sub A B

end NormalizedEndomorphismFunctional
