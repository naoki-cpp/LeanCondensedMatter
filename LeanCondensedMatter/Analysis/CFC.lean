import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.InnerProductSpace.Spectrum

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

/-- A self-adjoint operator's polynomial functional calculus acts on an eigenvector by
evaluating the polynomial at the eigenvalue. -/
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
