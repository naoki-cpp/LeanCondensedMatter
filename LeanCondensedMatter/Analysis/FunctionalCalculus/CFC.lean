import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Continuous functional calculus on eigenvectors and compact operators

For a self-adjoint bounded operator `T` on a Hilbert space, this module proves the eigenvector
functional-calculus law

`T v = c • v  ⟹  cfc f T v = f c • v`

for continuous `f`, using Mathlib's continuous-map induction principle.

It also proves that `cfc f T` is compact when `T` is compact and self-adjoint and `f 0 = 0`.
The condition at zero is essential in infinite dimensions because a nonzero constant term
contributes a multiple of the identity, which need not be compact.

These results provide the operator-level functional-calculus facts used by the spectral trace and
quantum thermodynamic layers.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open Filter Topology

/-- The continuous functional calculus acts on an eigenvector by evaluating the function
at its eigenvalue. This follows from Mathlib's continuous-map induction principle on the
spectrum, since the eigenvector identity is closed under addition, multiplication and limits. -/
theorem cfc_apply_eigenvector {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {v : H} {c : ℝ}
    (hv : (T : H →ₗ[ℂ] H) v = (c : ℂ) • v) {f : ℝ → ℝ} (hf : Continuous f) :
    cfc f T v = ((f c : ℝ) : ℂ) • v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hc : c ∈ spectrum ℝ T := by
    apply spectrum.of_algebraMap_mem ℂ
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      (x := v) ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩).mem_spectrum
  let z : spectrum ℝ T := ⟨c, hc⟩
  have h (g : C(spectrum ℝ T, ℝ)) :
      cfcHom hT g v = (g z : ℂ) • v := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      have hr : ContinuousMap.const (spectrum ℝ T) r =
          algebraMap ℝ C(spectrum ℝ T, ℝ) r := rfl
      rw [hr, AlgHomClass.commutes]
      rfl
    | id =>
      rw [cfcHom_id hT]
      exact hv
    | star_id =>
      rw [map_star, cfcHom_id hT, hT.star_eq]
      exact hv
    | add g k hg hk =>
      rw [map_add, add_apply, hg, hk]
      simp [add_smul]
    | mul g k hg hk =>
      rw [map_mul]
      change cfcHom hT g (cfcHom hT k v) = _
      rw [hk, map_smul, hg, smul_smul]
      simp [mul_comm]
    | frequently g hg =>
      have hleft : Continuous (fun k : C(spectrum ℝ T, ℝ) => cfcHom hT k v) :=
        (ContinuousLinearMap.apply ℂ H v).continuous.comp (cfcHom_continuous hT)
      have heval : Continuous (fun k : C(spectrum ℝ T, ℝ) => (k z : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_eval_const z)
      have hright : Continuous (fun k : C(spectrum ℝ T, ℝ) => (k z : ℂ) • v) :=
        heval.smul continuous_const
      have hclosed := isClosed_eq hleft hright
      change g ∈ {k : C(spectrum ℝ T, ℝ) | cfcHom hT k v = (k z : ℂ) • v}
      rw [← hclosed.closure_eq]
      exact mem_closure_iff_frequently.mpr hg
  rw [cfc_apply f T hT hf.continuousOn]
  exact h _

/-- If `T` is a compact self-adjoint operator and a continuous real function vanishes at zero,
then its continuous functional calculus is compact. The non-unital CFC induction principle
reduces the proof to algebraic closure and norm-closedness of the compact operators. -/
theorem isCompactOperator_cfc_of_zero {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (hcompact : IsCompactOperator T) {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) :
    IsCompactOperator (cfc f T : H →L[ℂ] H) := by
  open scoped NonUnitalContinuousFunctionalCalculus ContinuousMapZero in
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
