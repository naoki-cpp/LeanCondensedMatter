import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false

/-!
# Ordered-simplex iterated scalar integrals

Step 6 (PR 5a) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`): a
purely analytic, physics-free `ℂ`-valued iterated integral, defined recursively via
`intervalIntegral` rather than as a single integral over an explicit `MeasureTheory`-level simplex
subset of `ℝⁿ`. For `0 ≤ β`, this is the genuine iterated integral over the ordered simplex
`0 ≤ τₙ₋₁ ≤ ⋯ ≤ τ₁ ≤ τ₀ ≤ β`; for arbitrary real `β` (including negative), `intervalIntegral`'s
own orientation convention (`∫ x in a..b = -∫ x in b..a`) makes this the corresponding recursively
oriented interval-integral extension, not literally an integral over that simplex (which would be
empty for `β < 0`) — e.g. `orderedSimplexIntegral_const` gives `βⁿ/n!` for *every* real `β`, not
just `β ≥ 0`, and that value should be read as "simplex volume" only in the `0 ≤ β` case. Coordinate
`0` is the *latest*/*outermost* time — this orientation deliberately matches the existing Dyson
recursion (`Fermionic/DysonExpansion.lean`'s `dysonCoeff`), whose outer integration variable `σ`
also has range `[0, τ]` with `τ` the overall bound.

**Deliberately minimal.** No general "sum commutes with `orderedSimplexIntegral`" lemma is
included — that needs integrability hypotheses tailored to whatever the caller actually
integrates, and a maximally general abstract version would be premature here (`Fermionic/
WickDiagram/Amplitude.lean`, PR 5c, proves exactly the continuity/linearity facts its own
integrand needs). No claim of measurability/integrability beyond what each individual lemma's own
hypotheses require.

**The one exception**: `continuous_orderedSimplexIntegral_of_continuous`, continuity of
`orderedSimplexIntegral n (bound x) (f x)` jointly in an arbitrary parameter `x` — needed once a
caller's own bound (not just its integrand) varies with an outer parameter (Step 6 PR 6's own
`dysonCoeff`-recursion induction, where the *current* recursion's outer bound is itself the
*previous* level's integration variable). This is a genuinely different kind of fact from the
`_congr`/`_smul`/`_neg`/`_const` lemmas above (all stated for a *fixed* bound `β`), so it earns its
own name rather than being folded into any of them.
-/

namespace intervalIntegral

/-- **The iterated integral over the ordered simplex** `0 ≤ τₙ₋₁ ≤ ⋯ ≤ τ₁ ≤ τ₀ ≤ β` for `0 ≤ β`
(vacuously `f Fin.elim0` at `n = 0`, the empty simplex); for arbitrary `β : ℝ`, the corresponding
recursively oriented interval-integral extension (see the module docstring). Coordinate `0` is the
latest/outermost time: the recursion integrates the *outermost* coordinate `τ` over `[0, β]`, then
recurses into the remaining `n` coordinates over `[0, τ]`. -/
noncomputable def orderedSimplexIntegral :
    (n : ℕ) → ℝ → ((Fin n → ℝ) → ℂ) → ℂ
  | 0, _β, f => f Fin.elim0
  | n + 1, β, f =>
      ∫ τ in (0 : ℝ)..β, orderedSimplexIntegral n τ (fun rest => f (Fin.cons τ rest))

@[simp]
theorem orderedSimplexIntegral_zero (β : ℝ) (f : (Fin 0 → ℝ) → ℂ) :
    orderedSimplexIntegral 0 β f = f Fin.elim0 := rfl

theorem orderedSimplexIntegral_succ (n : ℕ) (β : ℝ) (f : (Fin (n + 1) → ℝ) → ℂ) :
    orderedSimplexIntegral (n + 1) β f =
      ∫ τ in (0 : ℝ)..β, orderedSimplexIntegral n τ (fun rest => f (Fin.cons τ rest)) := rfl

theorem orderedSimplexIntegral_congr {n : ℕ} {β : ℝ} {f g : (Fin n → ℝ) → ℂ}
    (h : ∀ τ, f τ = g τ) : orderedSimplexIntegral n β f = orderedSimplexIntegral n β g := by
  induction n generalizing β with
  | zero => simp [h]
  | succ n ih =>
    rw [orderedSimplexIntegral_succ, orderedSimplexIntegral_succ]
    exact intervalIntegral.integral_congr fun τ _ => ih fun rest => h (Fin.cons τ rest)

@[simp]
theorem orderedSimplexIntegral_zero_fun (n : ℕ) (β : ℝ) :
    orderedSimplexIntegral n β (fun _ => (0 : ℂ)) = 0 := by
  induction n generalizing β with
  | zero => rfl
  | succ n ih => simp [orderedSimplexIntegral_succ, ih]

theorem orderedSimplexIntegral_smul (n : ℕ) (β : ℝ) (c : ℂ) (f : (Fin n → ℝ) → ℂ) :
    orderedSimplexIntegral n β (fun τ => c * f τ) = c * orderedSimplexIntegral n β f := by
  induction n generalizing β with
  | zero => rfl
  | succ n ih =>
    rw [orderedSimplexIntegral_succ, orderedSimplexIntegral_succ]
    simp_rw [ih]
    rw [intervalIntegral.integral_const_mul]

theorem orderedSimplexIntegral_neg (n : ℕ) (β : ℝ) (f : (Fin n → ℝ) → ℂ) :
    orderedSimplexIntegral n β (fun τ => -f τ) = -orderedSimplexIntegral n β f := by
  have h := orderedSimplexIntegral_smul n β (-1) f
  simpa using h

/-- **Sanity check**: on a constant function, the ordered-simplex integral reduces to the
elementary-calculus volume `βⁿ/n!` of the simplex, times the constant. -/
theorem orderedSimplexIntegral_const (n : ℕ) (β : ℝ) (c : ℂ) :
    orderedSimplexIntegral n β (fun _ => c) = (β ^ n / n.factorial : ℝ) * c := by
  induction n generalizing β with
  | zero => simp
  | succ n ih =>
    rw [orderedSimplexIntegral_succ]
    simp_rw [ih]
    rw [show (fun τ : ℝ => (τ ^ n / n.factorial : ℝ) * c) =
        fun τ : ℝ => ((τ ^ n / n.factorial : ℝ) : ℂ) * c from rfl,
      intervalIntegral.integral_mul_const]
    rw [show (∫ τ in (0:ℝ)..β, ((τ ^ n / n.factorial : ℝ) : ℂ)) =
        ((∫ τ in (0:ℝ)..β, τ ^ n / n.factorial : ℝ) : ℂ) from by
      rw [← intervalIntegral.integral_ofReal]]
    rw [intervalIntegral.integral_div, integral_pow]
    have hfac : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hne : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    have hne1 : ((n : ℂ) + 1) ≠ 0 := by
      simp [Nat.cast_add_one_ne_zero]
    push_cast
    rw [hfac]
    field_simp
    ring

/-- **`orderedSimplexIntegral` is continuous in an outer parameter `x`, jointly through both its
own bound and its integrand.** For a continuous `bound : X → ℝ` and a jointly continuous
`f : X → (Fin n → ℝ) → ℂ`, `x ↦ orderedSimplexIntegral n (bound x) (f x)` is continuous — the
*bound itself* (not just the integrand, for a *fixed* bound) is allowed to vary continuously with
`x`. Proved by induction on `n`, generalizing the parameter space `X`/`bound`/`f` at each level
(the successor case's own inner recursion needs the inductive hypothesis at the *bigger* parameter
space `X × ℝ`, pairing the original parameter with the outer integral's own integration variable),
via `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` (Leibniz-rule-style
joint continuity of a parametrized interval integral with a variable, parameter-dependent, upper
limit) and `Continuous.finCons` (joint continuity of `Fin.cons`). -/
theorem continuous_orderedSimplexIntegral_of_continuous {X : Type*} [TopologicalSpace X] :
    ∀ (n : ℕ) (bound : X → ℝ) (f : X → (Fin n → ℝ) → ℂ), Continuous bound →
      Continuous (Function.uncurry f) →
      Continuous (fun x => orderedSimplexIntegral n (bound x) (f x))
  | 0, bound, f, _, hf => by
    simp only [orderedSimplexIntegral_zero]
    exact hf.comp (continuous_id.prodMk continuous_const)
  | n + 1, bound, f, hbound, hf => by
    simp_rw [orderedSimplexIntegral_succ]
    have hf' : Continuous (Function.uncurry
        (fun (y : X × ℝ) (rest : Fin n → ℝ) => f y.1 (Fin.cons y.2 rest))) := by
      have hcons : Continuous
          (fun z : (X × ℝ) × (Fin n → ℝ) => Fin.cons z.1.2 z.2 : (X × ℝ) × (Fin n → ℝ) →
            Fin (n + 1) → ℝ) :=
        Continuous.finCons (continuous_snd.comp continuous_fst) continuous_snd
      exact hf.comp ((continuous_fst.comp continuous_fst).prodMk hcons)
    have hF := continuous_orderedSimplexIntegral_of_continuous n Prod.snd
      (fun (y : X × ℝ) (rest : Fin n → ℝ) => f y.1 (Fin.cons y.2 rest)) continuous_snd hf'
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF hbound

end intervalIntegral
