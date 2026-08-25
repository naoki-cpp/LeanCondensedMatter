import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.InnerProductSpace.Spectrum

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Continuous functional calculus on eigenvectors and compact operators

Mathlib's continuous functional calculus `cfc f T` (for `T` self-adjoint on a Hilbert space)
has no lemma connecting it to eigenvectors of `T` in the literature sense: if `T v = c • v`,
then `cfc f T v = f c • v`. This file proves that fact for Hilbert spaces via polynomial
approximation (Stone–Weierstrass).

It also proves that if `T` is compact and self-adjoint and `f 0 = 0`, then `cfc f T` is compact.
The condition at zero is essential in infinite dimensions: a nonzero constant term contributes a
multiple of the identity, which is not compact in general.

This is foundational infrastructure for the operator-algebra development documented in
`notes/roadmaps/operator-algebra.md`: the continuous functional calculus is the natural
infinite-dimensional replacement for the explicit-eigenbasis constructions used in
`LeanCondensedMatter/QuantumTheory/Entropy.lean`, since in infinite dimensions there is no finite
list of eigenvalues to sum over.
-/

open Polynomial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- An operator's polynomial functional calculus acts on an eigenvector by evaluating the
polynomial at the eigenvalue. No self-adjointness hypothesis is needed here — this is a
purely algebraic fact about `Polynomial.aeval`. -/
theorem Polynomial.aeval_apply_eigenvector {T : H →L[ℂ] H} {v : H} {c : ℝ}
    (hv : (T : H →ₗ[ℂ] H) v = (c : ℂ) • v) (q : ℝ[X]) :
    (Polynomial.aeval T q : H →L[ℂ] H) v = ((q.eval c : ℝ) : ℂ) • v := by
  rw [Polynomial.aeval_eq_aeval_map
    (φ := algebraMap ℝ ℂ) (by ext r; simp [RingHom.comp_apply]) q T]
  let p := q.map (algebraMap ℝ ℂ)
  change (ContinuousLinearMap.toLinearMapRingHom (Polynomial.aeval T p)) v = _
  rw [Polynomial.map_aeval_eq_aeval_map
    (R := ℂ) (S := H →L[ℂ] H) (T := ℂ) (U := H →ₗ[ℂ] H)
    (φ := RingHom.id ℂ)
    (ψ := ContinuousLinearMap.toLinearMapRingHom)
    (by ext z x; simp [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one]) p T]
  have heval : p.eval (c : ℂ) = ((q.eval c : ℝ) : ℂ) := by
    change (q.map (algebraMap ℝ ℂ)).eval (c : ℂ) = ((q.eval c : ℝ) : ℂ)
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (p := q) (algebraMap ℝ ℂ) c
  simp only [Polynomial.map_id]
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul
    (f := ContinuousLinearMap.toLinearMapRingHom T) (μ := (c : ℂ))
    (x := v) (p := p) (by simpa using hv), heval]

omit [CompleteSpace H] in
/-- Evaluating a real polynomial with zero constant coefficient at a compact operator gives a
compact operator. Algebraically, such a polynomial is divisible by `X`, so its evaluation factors
through the original compact operator. -/
theorem Polynomial.isCompactOperator_aeval_of_coeff_zero {T : H →L[ℂ] H}
    (hT : IsCompactOperator T) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    IsCompactOperator (Polynomial.aeval T p : H →L[ℂ] H) := by
  obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr hp
  rw [map_mul]
  simp only [aeval_X]
  change IsCompactOperator (fun x : H => T ((Polynomial.aeval T q : H →L[ℂ] H) x))
  exact hT.comp_clm (Polynomial.aeval T q : H →L[ℂ] H)

open Filter Topology

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

/-- If `T` is a compact self-adjoint operator and a continuous real function vanishes at zero,
then its continuous functional calculus `cfc f T` is compact.

The proof approximates `f` uniformly on `[-‖T‖, ‖T‖]` by polynomials and subtracts each
approximant's value at zero. The resulting polynomials still converge uniformly to `f`, have zero
constant coefficient, and therefore evaluate to compact operators. Compact operators are closed in
the operator norm, so the CFC limit is compact. -/
theorem isCompactOperator_cfc_of_zero {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (hcompact : IsCompactOperator T) {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) :
    IsCompactOperator (cfc f T : H →L[ℂ] H) := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · letI := hH
    have hz : (cfc f T : H →L[ℂ] H) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact isCompactOperator_zero
  · letI := hH
    set R := ‖T‖
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (-R) R := by
      simp [R]
    have hspec_sub : spectrum ℝ T ⊆ Set.Icc (-R) R := by
      intro x hx
      have hnorm := spectrum.norm_le_norm_of_mem hx
      rw [Real.norm_eq_abs] at hnorm
      exact abs_le.mp hnorm
    choose q hq using fun n : ℕ =>
      exists_polynomial_near_of_continuousOn (-R) R f hf.continuousOn (1 / (n + 1))
        (by positivity)
    let p : ℕ → ℝ[X] := fun n => q n - C ((q n).eval 0)
    have hp_near (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-R) R) :
        |(p n).eval x - f x| < 2 / (n + 1) := by
      have hxq := hq n x hx
      have h0q := hq n 0 hzero_mem
      have hrearrange :
          (p n).eval x - f x =
            ((q n).eval x - f x) - ((q n).eval 0 - f 0) := by
        simp [p, hf0]
        ring
      rw [hrearrange]
      calc
        |((q n).eval x - f x) - ((q n).eval 0 - f 0)| ≤
            |(q n).eval x - f x| + |(q n).eval 0 - f 0| := abs_sub _ _
        _ < 1 / (n + 1) + 1 / (n + 1) := add_lt_add hxq h0q
        _ = 2 / (n + 1) := by ring
    have hp_coeff_zero : ∀ n, (p n).coeff 0 = 0 := by
      intro n
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp [p]
    have hp_compact : ∀ n,
        IsCompactOperator (cfc (p n).eval T : H →L[ℂ] H) := by
      intro n
      rw [cfc_polynomial (p n) T]
      exact Polynomial.isCompactOperator_aeval_of_coeff_zero hcompact (p n) (hp_coeff_zero n)
    have hconv :
        Tendsto (fun n => (cfc (p n).eval T : H →L[ℂ] H)) atTop
          (𝓝 (cfc f T : H →L[ℂ] H)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_eq_norm, ← cfc_sub (p n).eval f T]
      obtain ⟨⟨x₀, hx₀_mem, hx₀_eq⟩, -⟩ :=
        IsGreatest.norm_cfc (fun x => (p n).eval x - f x) T
      rw [← hx₀_eq]
      change ‖(p n).eval x₀ - f x₀‖ < ε
      rw [Real.norm_eq_abs]
      calc
        |(p n).eval x₀ - f x₀| < 2 / (n + 1) := hp_near n x₀ (hspec_sub hx₀_mem)
        _ ≤ 2 / (N + 1) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            exact_mod_cast Nat.succ_le_succ hn
        _ < ε := by
            rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hε] at hN
            nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact isCompactOperator_of_tendsto hconv (Filter.Eventually.of_forall hp_compact)
