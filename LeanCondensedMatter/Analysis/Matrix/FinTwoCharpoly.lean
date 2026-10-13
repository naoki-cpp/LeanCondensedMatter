/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Two-dimensional Cayley–Hamilton identities

The characteristic polynomial of a two-by-two matrix gives a quadratic identity.
This specializes to useful finite-order relations for determinant-one matrices.
-/

namespace Matrix

/-- The quadratic Cayley–Hamilton identity for a real `2 × 2` matrix. -/
theorem sq_sub_trace_smul_add_det_eq_zero (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M ^ 2 - (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ)) M.trace * M +
      (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ)) M.det = 0 := by
  simpa [Matrix.charpoly_fin_two] using M.aeval_self_charpoly

/-- A real `2 × 2` matrix with determinant one and trace zero has fourth power one. -/
theorem pow_four_eq_one_of_trace_zero_det_one (M : Matrix (Fin 2) (Fin 2) ℝ)
    (htrace : M.trace = 0) (hdet : M.det = 1) : M ^ 4 = 1 := by
  have h := M.sq_sub_trace_smul_add_det_eq_zero
  rw [htrace, hdet] at h
  simp only [map_zero, map_one, zero_mul, sub_zero] at h
  have hsq : M ^ 2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    calc
      M ^ 2 = (M ^ 2 + 1) - 1 := by simp
      _ = -1 := by rw [h, zero_sub]
  calc
    M ^ 4 = (M ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
    _ = (-1 : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 := by rw [hsq]
    _ = 1 := by simp


/-- A determinant-one real `2 × 2` matrix with trace `-1` has cube one. -/
theorem pow_three_eq_one_of_trace_neg_one_det_one (M : Matrix (Fin 2) (Fin 2) ℝ)
    (htrace : M.trace = -1) (hdet : M.det = 1) : M ^ 3 = 1 := by
  have hquad : M ^ 2 + M + 1 = 0 := by
    simpa [htrace, hdet] using M.sq_sub_trace_smul_add_det_eq_zero
  have hsq : M ^ 2 = -M - 1 := by
    calc
      M ^ 2 = (M ^ 2 + M + 1) - M - 1 := by noncomm_ring
      _ = -M - 1 := by rw [hquad]; noncomm_ring
  calc
    M ^ 3 = M ^ 2 * M := by noncomm_ring
    _ = (-M - 1) * M := by rw [hsq]
    _ = -(M ^ 2) - M := by noncomm_ring
    _ = 1 := by rw [hsq]; noncomm_ring

/-- A determinant-one real `2 × 2` matrix with trace `1` has sixth power one. -/
theorem pow_six_eq_one_of_trace_one_det_one (M : Matrix (Fin 2) (Fin 2) ℝ)
    (htrace : M.trace = 1) (hdet : M.det = 1) : M ^ 6 = 1 := by
  have hquad : M ^ 2 - M + 1 = 0 := by
    simpa [htrace, hdet] using M.sq_sub_trace_smul_add_det_eq_zero
  have hsq : M ^ 2 = M - 1 := by
    calc
      M ^ 2 = (M ^ 2 - M + 1) + M - 1 := by noncomm_ring
      _ = M - 1 := by rw [hquad]; noncomm_ring
  have hcube : M ^ 3 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    calc
      M ^ 3 = M ^ 2 * M := by noncomm_ring
      _ = (M - 1) * M := by rw [hsq]
      _ = M ^ 2 - M := by noncomm_ring
      _ = -1 := by rw [hsq]; noncomm_ring
  calc
    M ^ 6 = (M ^ 3) ^ 2 := by rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul]
    _ = (-1 : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 := by rw [hcube]
    _ = 1 := by simp

end Matrix
