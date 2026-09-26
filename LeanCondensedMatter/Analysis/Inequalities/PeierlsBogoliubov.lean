import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Positive

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# The Peierls–Bogoliubov spectral inequality

For a self-adjoint bounded operator `T` on a Hilbert space, a unit vector `e`, and a convex
continuous function `g : ℝ → ℝ`, the diagonal matrix element of `g` applied by continuous
functional calculus is bounded below by `g` of the diagonal matrix element of `T`:

`g ⟪e, T e⟫ ≤ ⟪e, cfc g T e⟫`.

The public inequalities are stated in the complex positive order, so they also establish that the
relevant diagonal matrix elements are real rather than discarding an imaginary part with `.re`.

The proof uses an explicit supporting affine minorant for `g` at the relevant scalar point. The
pointwise affine inequality is lifted to an operator inequality by monotonicity of the continuous
functional calculus and then evaluated on the unit vector by positivity. The supporting-line
condition is therefore an explicit theorem hypothesis. For
`g x = exp (-β x)`, `exp_tangent` supplies that hypothesis, yielding the form used in the
Gibbs–Klein and Helmholtz free-energy arguments.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open ContinuousLinearMap ComplexOrder
open scoped ComplexOrder

/-- **The Peierls–Bogoliubov inequality.** For a self-adjoint bounded operator `T`, a unit
vector `e`, and a continuous `g : ℝ → ℝ` admitting a tangent line at the lossless real diagonal
expectation `x₀`, `g x₀` is below the diagonal matrix element of `g(T)` in the complex positive
order. -/
theorem peierls_bogoliubov (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (g : ℝ → ℝ)
    (hgc : ContinuousOn g (spectrum ℝ T)) (e : H) (he : ‖e‖ = 1)
    (m x₀ : ℝ) (hx0 : x₀ = diagonalExpectationValue T hT e)
    (htangent : ∀ x : ℝ, m * x + (g x₀ - m * x₀) ≤ g x) :
    (g x₀ : ℂ) ≤ inner ℂ (cfc (R := ℝ) g T e) e := by
  have hle : cfc (R := ℝ) (fun x : ℝ => m * x + (g x₀ - m * x₀)) T ≤ cfc (R := ℝ) g T :=
    cfc_mono (fun x _ => htangent x)
  rw [ContinuousLinearMap.le_def] at hle
  have hpos := hle.inner_nonneg_left e
  rw [cfc_add T (fun x => m * x) (fun x => g x₀ - m * x₀) (by fun_prop) (by fun_prop)] at hpos
  rw [cfc_const (R := ℝ) (g x₀ - m * x₀) T,
    show (fun x : ℝ => m * x) = fun x => m • x from rfl,
    cfc_smul_id (R := ℝ) m T, Algebra.algebraMap_eq_smul_one] at hpos
  have hreal : ∀ (r : ℝ) (x y : H), (inner ℂ (r • x) y : ℂ) = (r : ℂ) * inner ℂ x y := by
    intro r x y
    rw [← algebraMap_smul ℂ r x, RCLike.algebraMap_eq_ofReal, inner_smul_real_left,
      Complex.real_smul]
  simp only [sub_apply, add_apply, smul_apply, one_apply_eq_self, inner_sub_left,
    inner_add_left, hreal] at hpos
  have hnorm : (inner ℂ e e : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  rw [hnorm, mul_one] at hpos
  have hx0c : (x₀ : ℂ) = inner ℂ (T e) e := by
    rw [hx0]
    exact coe_diagonalExpectationValue T hT e
  rw [← hx0c] at hpos
  have hcollapse :
      (m : ℂ) * (x₀ : ℂ) + ((g x₀ - m * x₀ : ℝ) : ℂ) = (g x₀ : ℂ) := by
    push_cast
    ring
  rw [hcollapse] at hpos
  exact sub_nonneg.mp hpos

/-- The tangent-line minorant for `x ↦ exp(-β x)` at `x₀`, discharging `peierls_bogoliubov`'s
`htangent` hypothesis for this concrete `g` (the case needed for the Gibbs state
`e^{-βH}`). Proved directly from `Real.add_one_le_exp`, without any general convexity
machinery. -/
theorem exp_tangent (β x₀ x : ℝ) :
    (-β * Real.exp (-β * x₀)) * x + (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)
      ≤ Real.exp (-β * x) := by
  have h := Real.add_one_le_exp (-β * (x - x₀))
  have hexp : Real.exp (-β * x) = Real.exp (-β * x₀) * Real.exp (-β * (x - x₀)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hexp]
  nlinarith [Real.exp_pos (-β * x₀), h]

/-- **Peierls–Bogoliubov, specialized to the Gibbs weight `g = exp(-β·)`.** The inequality is
stated directly in the complex positive order, so it also records the reality of the Gibbs
diagonal matrix element. -/
theorem gibbs_peierls_bogoliubov (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (β : ℝ) (e : H)
    (he : ‖e‖ = 1) :
    (Real.exp (-β * diagonalExpectationValue T hT e) : ℂ) ≤
      inner ℂ (cfc (R := ℝ) (fun x => Real.exp (-β * x)) T e) e :=
  peierls_bogoliubov T hT (fun x => Real.exp (-β * x)) (by fun_prop) e he
    (-β * Real.exp (-β * diagonalExpectationValue T hT e))
    (diagonalExpectationValue T hT e) rfl (fun x => exp_tangent β _ x)
