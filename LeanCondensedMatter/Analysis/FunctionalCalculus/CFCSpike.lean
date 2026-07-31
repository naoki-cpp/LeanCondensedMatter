import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

open Polynomial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

example {T : H →L[ℂ] H} {v : H} {c : ℝ}
    (hv : (T : H →ₗ[ℂ] H) v = (c : ℂ) • v) (q : ℝ[X]) :
    (Polynomial.aeval T q : H →L[ℂ] H) v = ((q.eval c : ℝ) : ℂ) • v := by
  change
    (Polynomial.aeval ((T.restrictScalars ℝ : H →L[ℝ] H) : H →ₗ[ℝ] H) q) v =
      (q.eval c : ℝ) • v
  exact Module.End.aeval_apply_of_mem_apply_eq_smul (by
    simpa [RCLike.real_smul_eq_coe_smul] using hv)
