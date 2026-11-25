import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.InnerProductSpace.Spectrum

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Continuous functional calculus on eigenvectors and compact operators

For a self-adjoint bounded operator `T` on a Hilbert space, this module proves the eigenvector
functional-calculus law

`T v = c • v  ⟹  cfc f T v = f c • v`

for continuous `f`, using polynomial approximation.

It also proves that `cfc f T` is compact when `T` is compact and self-adjoint and `f 0 = 0`.
The condition at zero is essential in infinite dimensions because a nonzero constant term
contributes a multiple of the identity, which need not be compact.

These results provide the operator-level functional-calculus facts used by the spectral trace and
quantum thermodynamic layers.
-/

open Polynomial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open Filter Topology

/-- **The continuous functional calculus acts on eigenvectors by evaluation.** For a
self-adjoint `T` and an eigenvector `v` of `T` with (real) eigenvalue `c`, `cfc f T` acts on
`v` by scaling it by `f c`, for any continuous `f : ℝ → ℝ`. Proved by approximating `f`
uniformly by polynomials on `[-‖T‖, ‖T‖]` (a compact interval containing `spectrum ℝ T`,
via the classical Weierstrass approximation theorem) and passing to the limit using the
isometry of `cfcHom` together with Mathlib's eigenvector evaluation law for `Polynomial.aeval`. -/
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
      rw [Polynomial.aeval_eq_aeval_map
        (φ := algebraMap ℝ ℂ) (by ext r; simp [RingHom.comp_apply]) (p n) T]
      let q := (p n).map (algebraMap ℝ ℂ)
      change (ContinuousLinearMap.toLinearMapRingHom (Polynomial.aeval T q)) v = _
      rw [Polynomial.map_aeval_eq_aeval_map
        (R := ℂ) (S := H →L[ℂ] H) (T := ℂ) (U := H →ₗ[ℂ] H)
        (φ := RingHom.id ℂ)
        (ψ := ContinuousLinearMap.toLinearMapRingHom)
        (by ext z x; simp [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one]) q T]
      have heval : q.eval (c : ℂ) = (((p n).eval c : ℝ) : ℂ) := by
        change ((p n).map (algebraMap ℝ ℂ)).eval (c : ℂ) = (((p n).eval c : ℝ) : ℂ)
        rw [Polynomial.eval_map]
        exact Polynomial.eval₂_at_apply (p := p n) (algebraMap ℝ ℂ) c
      simp only [Polynomial.map_id]
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul
        (f := ContinuousLinearMap.toLinearMapRingHom T) (μ := (c : ℂ))
        (x := v) (p := q) (by simpa using hv), heval]
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

/-- If `T` is a compact self-adjoint operator and a continuous real function vanishes at zero,
then its continuous functional calculus is compact. The non-unital CFC induction principle
reduces the proof to algebraic closure and norm-closedness of the compact operators. -/
theorem isCompactOperator_cfc_of_zero {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (hcompact : IsCompactOperator T) {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) :
    IsCompactOperator (cfc f T : H →L[ℂ] H) := by
  open scoped NonUnitalContinuousFunctionalCalculus in
  have h (g : C(quasispectrum ℝ T, ℝ)₀) : IsCompactOperator (cfcₙHom hT g : H →L[ℂ] H) := by
    induction g using ContinuousMapZero.induction_on_of_compact with
    | zero => rw [map_zero]; exact isCompactOperator_zero
    | id => rwa [cfcₙHom_id hT]
    | star_id => rwa [map_star, cfcₙHom_id hT, hT.star_eq]
    | add g k hg hk => rw [map_add]; exact hg.add hk
    | mul g k hg hk =>
      rw [map_mul]
      exact hg.comp_clm (cfcₙHom hT k)
    | smul r g hg => rw [map_smul]; exact hg.smul r
    | frequently g hg =>
      change cfcₙHom hT g ∈ {x : H →L[ℂ] H | IsCompactOperator x}
      rw [← isClosed_setOfPred_isCompactOperator.closure_eq]
      exact mem_closure_of_frequently_of_tendsto hg ((cfcₙHom_continuous hT).tendsto g)
  rw [← cfcₙ_eq_cfc hf.continuousOn hf0, cfcₙ_apply f T hf.continuousOn hf0 hT]
  exact h _
