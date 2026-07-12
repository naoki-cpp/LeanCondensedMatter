import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.InnerProductSpace.Spectrum

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# The continuous functional calculus acts on eigenvectors by evaluation

Mathlib's continuous functional calculus `cfc f T` (for `T` self-adjoint on a Hilbert space)
has no lemma connecting it to eigenvectors of `T` in the literature sense: if `T v = c • v`,
then `cfc f T v = f c • v`. This file proves that fact for finite-dimensional `H`, via
polynomial approximation (Stone–Weierstrass) — the route recommended after surveying Mathlib
for a shortcut (none exists; see `notes/caveats.md`).

This is foundational infrastructure for Track C (`notes/roadmaps/operator-algebra.md`): the
continuous functional calculus is the natural infinite-dimensional replacement for the
explicit-eigenbasis constructions used in `LeanCondensedMatter/QuantumTheory/Entropy.lean`,
since in infinite dimensions there is no finite list of eigenvalues to sum over.
-/

open Polynomial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

/-- An operator's polynomial functional calculus acts on an eigenvector by evaluating the
polynomial at the eigenvalue. No self-adjointness hypothesis is needed here — this is a
purely algebraic fact about `Polynomial.aeval`. Self-adjointness only becomes necessary for
the continuous functional calculus `cfc` itself (in the next step of this file, not yet
proved — see `notes/caveats.md`), since Mathlib's `cfc` on `H →L[ℂ] H` is only meaningful
(non-junk) for operators satisfying the `IsSelfAdjoint` predicate. -/
theorem Polynomial.aeval_apply_eigenvector {T : H →L[ℂ] H} {v : H} {c : ℝ}
    (hv : (T : H →ₗ[ℂ] H) v = (c : ℂ) • v) (q : ℝ[X]) :
    (Polynomial.aeval T q : H →L[ℂ] H) v = ((q.eval c : ℝ) : ℂ) • v := by
  induction q using Polynomial.induction_on with
  | C r =>
    simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq =>
    simp only [map_add, add_apply, hp, hq]
    rw [eval_add, Complex.ofReal_add, add_smul]
  | monomial n r _ =>
    have hv' : T v = (c : ℂ) • v := hv
    have hTpow : ∀ m : ℕ, (T ^ m : H →L[ℂ] H) v = (c ^ m : ℂ) • v := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply, hv', map_smul, ih, smul_smul, pow_succ,
          mul_comm]
    simp only [eval_mul, eval_C, eval_X_pow, map_mul, aeval_C, map_pow, aeval_X,
      Algebra.algebraMap_eq_smul_one]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply, hTpow (n + 1)]
    rw [← smul_assoc, RCLike.real_smul_eq_coe_mul]
    congr 1
    push_cast
    ac_rfl

open Filter Topology in
/-- **The continuous functional calculus acts on eigenvectors by evaluation.** For a
self-adjoint `T` and an eigenvector `v` of `T` with (real) eigenvalue `c`, `cfc f T` acts on
`v` by scaling it by `f c`, for any continuous `f : ℝ → ℝ`. Proved by approximating `f`
uniformly by polynomials on `[-‖T‖, ‖T‖]` (a compact interval containing `spectrum ℝ T`,
via the classical Weierstrass approximation theorem) and passing to the limit using the
isometry of `cfcHom` together with `Polynomial.aeval_apply_eigenvector`. -/
theorem cfc_apply_eigenvector {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {v : H} {c : ℝ}
    (hv : (T : H →ₗ[ℂ] H) v = (c : ℂ) • v) {f : ℝ → ℝ} (hf : Continuous f) :
    cfc f T v = ((f c : ℝ) : ℂ) • v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  haveI : Nontrivial H := ⟨0, v, fun h => hv0 h.symm⟩
  set R := ‖T‖ with hR_def
  have hc_bound : |c| ≤ R := by
    have h1 : ‖(T : H →ₗ[ℂ] H) v‖ = |c| * ‖v‖ := by
      rw [hv, norm_smul]; simp
    have h2 : ‖(T : H →ₗ[ℂ] H) v‖ ≤ R * ‖v‖ := T.le_opNorm v
    rw [h1] at h2
    exact le_of_mul_le_mul_right h2 (norm_pos_iff.mpr hv0)
  have hc_mem : c ∈ Set.Icc (-R) R := abs_le.mp hc_bound
  have hspec_sub : spectrum ℝ T ⊆ Set.Icc (-R) R := by
    intro x hx
    have hnorm := spectrum.norm_le_norm_of_mem hx
    rw [Real.norm_eq_abs] at hnorm
    exact abs_le.mp hnorm
  choose p hp using fun n : ℕ =>
    exists_polynomial_near_of_continuousOn (-R) R f hf.continuousOn (1 / (n + 1))
      (by positivity)
  have hconv : Tendsto (fun n => cfc (p n).eval T) atTop (𝓝 (cfc f T)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, ← cfc_sub (p n).eval f T]
    obtain ⟨⟨x₀, hx₀_mem, hx₀_eq⟩, -⟩ :=
      IsGreatest.norm_cfc (fun x => (p n).eval x - f x) T
    rw [← hx₀_eq]
    change ‖(p n).eval x₀ - f x₀‖ < ε
    rw [Real.norm_eq_abs]
    calc |(p n).eval x₀ - f x₀| < 1 / (n + 1) := hp n x₀ (hspec_sub hx₀_mem)
      _ ≤ 1 / (N + 1) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact_mod_cast Nat.succ_le_succ hn
      _ < ε := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε] at hN
          nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hconv2 : Tendsto (fun n => cfc (p n).eval T v) atTop (𝓝 (((f c : ℝ) : ℂ) • v)) := by
    have heq : ∀ n, cfc (p n).eval T v = (((p n).eval c : ℝ) : ℂ) • v := by
      intro n
      rw [cfc_polynomial (p n) T]
      exact Polynomial.aeval_apply_eigenvector hv (p n)
    simp_rw [heq]
    have hp_c : Tendsto (fun n => (p n).eval c) atTop (𝓝 (f c)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq]
      calc |(p n).eval c - f c| < 1 / (n + 1) := hp n c hc_mem
        _ ≤ 1 / (N + 1) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            exact_mod_cast Nat.succ_le_succ hn
        _ < ε := by
            rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hε] at hN
            nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact ((Complex.continuous_ofReal.tendsto (f c)).comp hp_c).smul_const v
  have hconv3 : Tendsto (fun n => cfc (p n).eval T v) atTop (𝓝 (cfc f T v)) :=
    ((ContinuousLinearMap.apply ℂ H v).continuous.tendsto (cfc f T)).comp hconv
  exact tendsto_nhds_unique hconv3 hconv2
