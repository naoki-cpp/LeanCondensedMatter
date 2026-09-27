import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Intrinsic dependence on differential data

This module contains the representation-independent predicate that a transport functional depends
only on the differential data `d f`.  It deliberately does not choose a current extension or a
current density.  Those representation-specific constructions live in `CurrentRepresentation`.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

/-- A transport functional depends only on differential data when equal differentials give equal
transport. This statement is representation-independent: it does not choose a current extension
`J : OneForm →ₗ[𝕜] Obs`. -/
def DependsOnlyOnDifferential
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) : Prop :=
  ∀ ⦃f g : Test⦄, d f = d g → Φ f = Φ g

namespace DependsOnlyOnDifferential

/-- Intrinsic differential dependence is preserved by addition. -/
theorem add
    {d : Test →ₗ[𝕜] OneForm} {Φ Ψ : Test →ₗ[𝕜] Obs}
    (hΦ : DependsOnlyOnDifferential d Φ)
    (hΨ : DependsOnlyOnDifferential d Ψ) :
    DependsOnlyOnDifferential d (Φ + Ψ) := by
  intro f g hfg
  simp only [LinearMap.add_apply]
  rw [hΦ hfg, hΨ hfg]

/-- Intrinsic differential dependence is preserved by scalar multiplication. -/
theorem smul
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs}
    (hΦ : DependsOnlyOnDifferential d Φ) (c : 𝕜) :
    DependsOnlyOnDifferential d (c • Φ) := by
  intro f g hfg
  simp only [LinearMap.smul_apply]
  rw [hΦ hfg]

/-- A transport functional depending only on `d f` vanishes whenever `d f = 0`. -/
theorem eq_zero_of_map_eq_zero
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs}
    (hΦ : DependsOnlyOnDifferential d Φ) {f : Test} (hf : d f = 0) :
    Φ f = 0 := by
  calc
    Φ f = Φ 0 := hΦ (by simpa using hf)
    _ = 0 := map_zero Φ

section Ring

variable {R Test' OneForm' Obs' : Type*}
variable [CommRing R]
variable [AddCommGroup Test'] [Module R Test']
variable [AddCommGroup OneForm'] [Module R OneForm']
variable [AddCommGroup Obs'] [Module R Obs']

/-- Over modules over a commutative ring, intrinsic differential dependence is exactly kernel
inclusion: the transport vanishes on every test direction invisible to `d`. -/
theorem iff_ker_le_ker
    {d : Test' →ₗ[R] OneForm'} {Φ : Test' →ₗ[R] Obs'} :
    DependsOnlyOnDifferential d Φ ↔ LinearMap.ker d ≤ LinearMap.ker Φ := by
  constructor
  · intro h f hf
    rw [LinearMap.mem_ker] at hf ⊢
    exact h.eq_zero_of_map_eq_zero hf
  · intro h f g hfg
    have hsub : f - g ∈ LinearMap.ker d :=
      LinearMap.sub_mem_ker_iff.mpr hfg
    exact LinearMap.sub_mem_ker_iff.mp (h hsub)

end Ring

end DependsOnlyOnDifferential

end ConservationLaw
