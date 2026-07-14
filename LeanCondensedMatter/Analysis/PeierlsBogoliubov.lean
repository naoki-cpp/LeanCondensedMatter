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

/-- `cfc` of an affine function `m * x + c` is the affine combination `m • T + c • 1` of the
operator itself and the identity. Used to unfold the tangent-line minorant back into an
operator-level statement in `peierls_bogoliubov`. -/
theorem cfc_affine (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (m c : ℝ) :
    cfc (R := ℝ) (fun x : ℝ => m * x + c) T = m • T + c • (1 : H →L[ℂ] H) := by
  rw [cfc_add T (fun x => m * x) (fun x => c) (by fun_prop) (by fun_prop)]
  rw [cfc_const (R := ℝ) c T, show (fun x : ℝ => m * x) = fun x => m • x from rfl,
    cfc_smul_id (R := ℝ) m T, Algebra.algebraMap_eq_smul_one]

/-- **The Peierls–Bogoliubov inequality.** For a self-adjoint bounded operator `T`, a unit
vector `e`, and a continuous `g : ℝ → ℝ` admitting a tangent line at `x₀ = ⟪e, T e⟫` that
minorizes `g` everywhere (`htangent`, the hypothesis witnessing convexity of `g` at that point;
see the file docstring), `g ⟪e, T e⟫ ≤ ⟪e, cfc g T e⟫`. -/
theorem peierls_bogoliubov (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (g : ℝ → ℝ)
    (hgc : ContinuousOn g (spectrum ℝ T)) (e : H) (he : ‖e‖ = 1)
    (m x₀ : ℝ) (hx0 : x₀ = (inner ℂ (T e) e : ℂ).re)
    (htangent : ∀ x : ℝ, m * x + (g x₀ - m * x₀) ≤ g x) :
    g x₀ ≤ (inner ℂ (cfc (R := ℝ) g T e) e).re := by
  have hle : cfc (R := ℝ) (fun x : ℝ => m * x + (g x₀ - m * x₀)) T ≤ cfc (R := ℝ) g T :=
    cfc_mono (fun x _ => htangent x)
  rw [ContinuousLinearMap.le_def] at hle
  have hpos := hle.inner_nonneg_left e
  rw [cfc_affine T hT] at hpos
  have hreal : ∀ (r : ℝ) (x y : H), (inner ℂ (r • x) y : ℂ) = (r : ℂ) * inner ℂ x y := by
    intro r x y
    rw [← algebraMap_smul ℂ r x, RCLike.algebraMap_eq_ofReal, inner_smul_real_left,
      Complex.real_smul]
  simp only [sub_apply, add_apply, smul_apply, one_apply_eq_self, inner_sub_left,
    inner_add_left, hreal] at hpos
  have hnorm : (inner ℂ e e : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]; norm_num
  rw [hnorm, mul_one] at hpos
  have hre := (Complex.le_def.mp hpos).1
  simp only [Complex.zero_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  rw [← hx0] at hre
  linarith [hre]

/-- The tangent-line minorant for `x ↦ exp(-β x)` at `x₀`, discharging `peierls_bogoliubov`'s
`htangent` hypothesis for this concrete `g` (the case needed for the Gibbs state
`e^{-βH}`). Proved directly from `Real.add_one_le_exp`, without any general convexity
machinery. -/
theorem exp_tangent (β x₀ x : ℝ) :
    (-β * Real.exp (-β * x₀)) * x + (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)
      ≤ Real.exp (-β * x) := by
  have h := Real.add_one_le_exp (-β * (x - x₀))
  have hexp : Real.exp (-β * x) = Real.exp (-β * x₀) * Real.exp (-β * (x - x₀)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  nlinarith [Real.exp_pos (-β * x₀), h]

/-- **Peierls–Bogoliubov, specialized to the Gibbs weight `g = exp(-β·)`.** The instance of
`peierls_bogoliubov` actually needed for the Gibbs–Klein / Helmholtz free-energy inequality:
`exp(-β ⟪e, T e⟫) ≤ ⟪e, cfc (fun x => exp(-β x)) T e⟫`. -/
theorem gibbs_peierls_bogoliubov (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (β : ℝ) (e : H)
    (he : ‖e‖ = 1) :
    Real.exp (-β * (inner ℂ (T e) e : ℂ).re) ≤
      (inner ℂ (cfc (R := ℝ) (fun x => Real.exp (-β * x)) T e) e).re :=
  peierls_bogoliubov T hT (fun x => Real.exp (-β * x)) (by fun_prop) e he
    (-β * Real.exp (-β * (inner ℂ (T e) e : ℂ).re)) (inner ℂ (T e) e : ℂ).re rfl
    (fun x => exp_tangent β _ x)
