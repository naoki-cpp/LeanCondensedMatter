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
continuous function `g : ℝ → ℝ`, the diagonal matrix element of `g` applied via the continuous
functional calculus is at least `g` applied to the diagonal matrix element of `T` itself:
`g ⟪e, T e⟫ ≤ ⟪e, cfc g T e⟫`. This is the Peierls–Bogoliubov inequality, the key spectral fact
underlying the Gibbs–Klein / Helmholtz free-energy inequality
(`QuantumTheory.helmholtzFreeEnergy_ge`, see `notes/roadmaps/quantum-theory-foundations.md`).

The public inequalities are stated in the complex positive order.  Consequently, they assert both
that the relevant diagonal matrix elements are real and that the inequality holds; no imaginary
part is discarded with `.re`.

**Route taken, and why.** The textbook proof integrates the convex function `g` against `T`'s
spectral measure at `e` and invokes Jensen's inequality. Mathlib has no spectral-measure
construction for `cfc`/self-adjoint operators (surveyed: no `spectralMeasure` declaration
anywhere in the pinned Mathlib revision, and no Riesz-representation route from `cfcHom` to a
measure either), so that route is not available here. Instead this file uses the **tangent-line
trick**: convexity of `g` at a point `x₀` is witnessed by an affine minorant `m * x + (g x₀ - m *
x₀) ≤ g x` for all `x` (a supporting line at `x₀`), which lifts to an operator inequality via
`cfc_mono` (Mathlib's order-monotonicity of `cfc` in the pointwise order on the spectrum), and
then to the diagonal matrix element via `ContinuousLinearMap.IsPositive.inner_nonneg_left`. This
sidesteps spectral measures and Jensen's inequality entirely, at the cost of taking the tangent
line's existence as an explicit hypothesis (`htangent` below) rather than deriving it from
`ConvexOn` — matching this project's established style of taking analytic side conditions as
explicit hypotheses (`notes/conventions.md`). For a general convex `g`, existence of `m` follows
from `g` having a subgradient at every point of `ℝ` (true for any convex function on all of `ℝ`,
by e.g. the sup of secant slopes on either side), but Mathlib does not currently package that
existence result, so it is left as a hypothesis; `exp_tangent` below discharges it concretely
for `g = fun x => Real.exp (-β * x)`, the case needed for the Gibbs state.
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
