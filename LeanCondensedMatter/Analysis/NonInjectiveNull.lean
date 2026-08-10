import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option linter.style.header false

/-!
# Non-injective coordinate families are negligible

A finite family of real coordinates fails to be injective exactly on the union of the pairwise
equality hyperplanes, of which there are finitely many, so the failure set is null.

This is the packaging the two-point linked-cluster development needs: exact covariance of a
fixed-time amplitude under relabeling is only available when the interaction-time assignment is
injective, and the bad assignments are irrelevant under an integral. Stating it once for an
arbitrary finite family avoids a null-set theorem per diagram, component, or shuffle.
-/

namespace Analysis

open MeasureTheory

variable {ι : Type*}

/-- The set where two fixed coordinates agree: the kernel of the difference of two projections. -/
def eqCoordSubmodule (i j : ι) : Submodule ℝ (ι → ℝ) :=
  LinearMap.ker
    ((LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj j : (ι → ℝ) →ₗ[ℝ] ℝ))

theorem mem_eqCoordSubmodule_iff (i j : ι) (x : ι → ℝ) :
    x ∈ eqCoordSubmodule i j ↔ x i = x j := by
  simp [eqCoordSubmodule, LinearMap.mem_ker, sub_eq_zero]

/-- Two distinct coordinates do not agree everywhere, so their agreement set is a proper
subspace. -/
theorem eqCoordSubmodule_ne_top {i j : ι} (hij : i ≠ j) :
    eqCoordSubmodule i j ≠ (⊤ : Submodule ℝ (ι → ℝ)) := by
  classical
  intro htop
  have hmem : (Pi.single i (1 : ℝ)) ∈ eqCoordSubmodule i j := by rw [htop]; trivial
  rw [mem_eqCoordSubmodule_iff] at hmem
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at hmem
  exact one_ne_zero hmem

/-- **Coordinate coincidence is negligible.** The set where two distinct coordinates agree is
null. -/
theorem volume_eqCoord_eq_zero [Fintype ι] {i j : ι} (hij : i ≠ j) :
    volume {x : ι → ℝ | x i = x j} = 0 := by
  classical
  have hset : {x : ι → ℝ | x i = x j} = (eqCoordSubmodule i j : Set (ι → ℝ)) := by
    ext x
    exact (mem_eqCoordSubmodule_iff i j x).symm
  rw [hset]
  exact Measure.addHaar_submodule volume _ (eqCoordSubmodule_ne_top hij)

/-- **Non-injective families are negligible.** A finite family of real coordinates is injective
outside a null set, so an almost-everywhere statement may always assume injectivity. -/
theorem volume_setOf_not_injective_eq_zero [Fintype ι] :
    volume {x : ι → ℝ | ¬ Function.Injective x} = 0 := by
  classical
  have hsub : {x : ι → ℝ | ¬ Function.Injective x} ⊆
      ⋃ p : {p : ι × ι // p.1 ≠ p.2}, {x : ι → ℝ | x p.1.1 = x p.1.2} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Function.Injective, not_forall] at hx
    obtain ⟨i, j, hij, hne⟩ := hx
    exact Set.mem_iUnion.2 ⟨⟨(i, j), hne⟩, hij⟩
  refine measure_mono_null hsub ?_
  exact measure_iUnion_null fun p => volume_eqCoord_eq_zero p.2

/-- Almost every finite family of real coordinates is injective. -/
theorem ae_injective [Fintype ι] : ∀ᵐ x : ι → ℝ ∂volume, Function.Injective x := by
  rw [Filter.eventually_iff, mem_ae_iff, Set.compl_setOf]
  exact volume_setOf_not_injective_eq_zero

end Analysis
