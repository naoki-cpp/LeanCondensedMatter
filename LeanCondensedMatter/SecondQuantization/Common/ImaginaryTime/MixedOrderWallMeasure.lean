import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderChamber
import Mathlib.LinearAlgebra.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option linter.style.header false

/-!
# Measure-zero walls for mixed two-point order chambers

The mixed two-point event order can change only when an interaction time crosses one of the two fixed
external times or when two distinct interaction times coincide. In the finite-dimensional ambient
time space every such locus is a codimension-one affine or linear hyperplane and hence has Lebesgue
measure zero. This layer is statistics-independent.
-/

namespace SecondQuantization
namespace Common

open MeasureTheory

def twoPointExternalTimeWall {n : ℕ} (v : Fin n) (t : ℝ) : Set (Fin n → ℝ) :=
  {σ | σ v = t}

theorem volume_twoPointExternalTimeWall_eq_zero {n : ℕ} (v : Fin n) (t : ℝ) :
    volume (twoPointExternalTimeWall v t) = 0 := by
  rw [volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane
    (fun _ : Fin n => (volume : Measure ℝ)) v t

def twoPointInteractionCoincidenceSubmodule {n : ℕ} (v w : Fin n) :
    Submodule ℝ (Fin n → ℝ) :=
  ((LinearMap.proj v : (Fin n → ℝ) →ₗ[ℝ] ℝ) -
    (LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ)).ker

@[simp]
theorem mem_twoPointInteractionCoincidenceSubmodule_iff {n : ℕ}
    (v w : Fin n) (σ : Fin n → ℝ) :
    σ ∈ twoPointInteractionCoincidenceSubmodule v w ↔ σ v = σ w := by
  change σ v - σ w = 0 ↔ σ v = σ w
  exact sub_eq_zero

def twoPointInteractionCoincidenceWall {n : ℕ} (v w : Fin n) : Set (Fin n → ℝ) :=
  {σ | σ v = σ w}

private theorem twoPointInteractionCoincidenceSubmodule_ne_top {n : ℕ}
    {v w : Fin n} (hvw : v ≠ w) :
    twoPointInteractionCoincidenceSubmodule v w ≠ ⊤ := by
  intro htop
  let σ : Fin n → ℝ := fun k => if k = v then 1 else 0
  have hσ : σ ∈ twoPointInteractionCoincidenceSubmodule v w := by
    rw [htop]
    trivial
  rw [mem_twoPointInteractionCoincidenceSubmodule_iff] at hσ
  have hwv : w ≠ v := hvw.symm
  simpa [σ, hwv] using hσ

theorem volume_twoPointInteractionCoincidenceWall_eq_zero {n : ℕ}
    {v w : Fin n} (hvw : v ≠ w) :
    volume (twoPointInteractionCoincidenceWall v w) = 0 := by
  have hset : twoPointInteractionCoincidenceWall v w =
      (twoPointInteractionCoincidenceSubmodule v w : Set (Fin n → ℝ)) := by
    ext σ
    simp [twoPointInteractionCoincidenceWall]
  rw [hset]
  exact MeasureTheory.Measure.addHaar_submodule
    (volume : Measure (Fin n → ℝ))
    (twoPointInteractionCoincidenceSubmodule v w)
    (twoPointInteractionCoincidenceSubmodule_ne_top hvw)

def twoPointExternalTimeWalls {n : ℕ} (t : ℝ) : Set (Fin n → ℝ) :=
  ⋃ v : Fin n, twoPointExternalTimeWall v t

theorem volume_twoPointExternalTimeWalls_eq_zero {n : ℕ} (t : ℝ) :
    volume (twoPointExternalTimeWalls (n := n) t) = 0 := by
  unfold twoPointExternalTimeWalls
  exact measure_iUnion_null fun v => volume_twoPointExternalTimeWall_eq_zero v t

def twoPointInteractionCoincidenceWalls {n : ℕ} : Set (Fin n → ℝ) :=
  ⋃ v : Fin n, ⋃ w : Fin n,
    if v = w then ∅ else twoPointInteractionCoincidenceWall v w

theorem volume_twoPointInteractionCoincidenceWalls_eq_zero {n : ℕ} :
    volume (twoPointInteractionCoincidenceWalls (n := n)) = 0 := by
  unfold twoPointInteractionCoincidenceWalls
  apply measure_iUnion_null
  intro v
  apply measure_iUnion_null
  intro w
  by_cases hvw : v = w
  · simp [hvw]
  · simp [hvw, volume_twoPointInteractionCoincidenceWall_eq_zero hvw]

def twoPointMixedOrderWallSet {n : ℕ} (τ τ' : ℝ) : Set (Fin n → ℝ) :=
  twoPointExternalTimeWalls (n := n) τ ∪
    twoPointExternalTimeWalls (n := n) τ' ∪
      twoPointInteractionCoincidenceWalls (n := n)

theorem volume_twoPointMixedOrderWallSet_eq_zero {n : ℕ} (τ τ' : ℝ) :
    volume (twoPointMixedOrderWallSet (n := n) τ τ') = 0 := by
  unfold twoPointMixedOrderWallSet
  exact measure_union_null
    (measure_union_null
      (volume_twoPointExternalTimeWalls_eq_zero (n := n) τ)
      (volume_twoPointExternalTimeWalls_eq_zero (n := n) τ'))
    (volume_twoPointInteractionCoincidenceWalls_eq_zero (n := n))

theorem ae_not_mem_twoPointMixedOrderWallSet {n : ℕ} (τ τ' : ℝ) :
    ∀ᵐ σ : Fin n → ℝ, σ ∉ twoPointMixedOrderWallSet (n := n) τ τ' := by
  rw [ae_iff]
  simpa only [not_not, Set.setOf_mem_eq] using
    (volume_twoPointMixedOrderWallSet_eq_zero (n := n) τ τ')

end Common
end SecondQuantization
