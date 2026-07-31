import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

open Polynomial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

example {T : H →L[ℂ] H} {v : H} {c : ℝ}
    (hv : (T : H →ₗ[ℂ] H) v = (c : ℂ) • v) (q : ℝ[X]) :
    (Polynomial.aeval T q : H →L[ℂ] H) v = ((q.eval c : ℝ) : ℂ) • v := by
  rw [Polynomial.aeval_eq_aeval_map
    (φ := algebraMap ℝ ℂ) (by ext r; simp [RingHom.comp_apply]) q T]
  change
    (Polynomial.aeval (T : H →ₗ[ℂ] H) (q.map (algebraMap ℝ ℂ))) v =
      ((q.eval c : ℝ) : ℂ) • v
  have h := Module.End.aeval_apply_of_mem_apply_eq_smul
    (f := (T : H →ₗ[ℂ] H)) (μ := (c : ℂ)) (x := v)
    (p := q.map (algebraMap ℝ ℂ)) hv
  simpa using h
