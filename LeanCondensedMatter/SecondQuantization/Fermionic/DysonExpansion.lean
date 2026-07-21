import LeanCondensedMatter.SecondQuantization.Fermionic.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Common.FiniteOperatorIntegral

set_option linter.style.header false

/-!
# The Dyson-series coefficients, as genuine continuous imaginary-time iterated integrals

Step 5 (continued) of Phase 9's Dyson-series plan (`notes/roadmaps/second-quantization.md`): the
`n`-th order interaction-picture Dyson coefficient `Dₙ(τ)`, defined by the genuine continuous
recursion

`D₀(τ) = id`,  `Dₙ₊₁(τ) = -∫ σ in 0..τ, V_I(σ) ∘ Dₙ(σ)`,

where `V_I(σ) := interactionPicture ε V σ`. This recursion directly represents the time-ordered
iterated integral `Dₙ(τ) = (-1)ⁿ ∫_{0≤τₙ≤⋯≤τ₁≤τ} V_I(τ₁)⋯V_I(τₙ) dτₙ⋯dτ₁` — but unlike a
hypothetical infinite Dyson *series* `Σₙ λⁿ Dₙ(τ)`, no convergence, analytic operator exponential,
or equality with a genuine `e^{-β(H₀+λV)}` is claimed anywhere in this file. `dysonTruncation`
below is only a finite partial sum in the perturbation parameter `λ`, standing in for the
(not-yet-analytic) full series the same way `FormalExp.lean`'s `formalExpTruncation` stands in for
`exp(-H)`.

**Why a recursion, not an explicit closed form.** The recursion mirrors the physical
time-ordering directly: `Dₙ₊₁`'s integral variable `σ` ranges over `[0, τ]`, and the *inner*
`Dₙ(σ)` recursively constrains the remaining `n` variables to `0 ≤ τₙ ≤ ⋯ ≤ τ₂ ≤ σ`. Proving the
explicit multi-variable time-ordered-integral formula equal to this recursion, and connecting it
to an `n`-operator time-ordering `T_τ`, is deliberately **not** done here — the project's existing
`Common.timeOrderedProduct` is a *two*-operator API whose fermionic wrapper always inserts a `-1`
on exchange, which is physically wrong for the (fermion-even) interaction vertex `V`; a
genuine `n`-vertex even-operator time ordering is future work, out of scope for this file.

**Type design.** `ε : Mode → ℝ` fixes the free Hamiltonian `H₀ = freeHamiltonian ε`; `V` is an
arbitrary interaction operator; the perturbation-counting scalar `λ` appears only in
`dysonTruncation`, not in `dysonCoeff` itself — `H = H₀ + λV` is deliberately *not* bundled into a
single structure. The sign `(-1)ⁿ` is folded into `dysonCoeff`'s own recursion, so
`dysonTruncation` only multiplies by `λⁿ`, not `(-λ)ⁿ`.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The `n`-th Dyson coefficient** `Dₙ(τ)`, defined by the genuine continuous recursion
`D₀(τ) = id`, `Dₙ₊₁(τ) = -∫ σ in 0..τ, V_I(σ) ∘ Dₙ(σ)`. -/
noncomputable def dysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    ℕ → ℝ → FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode
  | 0, _ => LinearMap.id
  | n + 1, τ =>
      - Common.operatorIntervalIntegral
          (fun σ => (interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) 0 τ

omit [LinearOrder Mode] in
theorem dysonCoeff_zero (ε : Mode → ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (τ : ℝ) : dysonCoeff ε V 0 τ = LinearMap.id := rfl

omit [LinearOrder Mode] in
theorem dysonCoeff_succ (ε : Mode → ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (n : ℕ) (τ : ℝ) :
    dysonCoeff ε V (n + 1) τ =
      - Common.operatorIntervalIntegral
          (fun σ => (interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) 0 τ := rfl

omit [LinearOrder Mode] in
/-- **The first-order coefficient**, `D₁(τ) = -∫ σ in 0..τ, V_I(σ)`. -/
theorem dysonCoeff_one (ε : Mode → ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (τ : ℝ) : dysonCoeff ε V 1 τ = - Common.operatorIntervalIntegral (interactionPicture ε V) 0 τ
    := by
  rw [dysonCoeff_succ]
  congr 2

omit [LinearOrder Mode] in
/-- **`Dₙ(0) = id` if `n = 0`, else `0`**: at `τ = 0` the defining integral is over the degenerate
interval `[0, 0]`, hence `0` (`operatorIntervalIntegral_same`). -/
theorem dysonCoeff_at_zero (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    dysonCoeff ε V n 0 = if n = 0 then LinearMap.id else 0 := by
  cases n with
  | zero => simp [dysonCoeff_zero]
  | succ k => simp [dysonCoeff_succ, Common.operatorIntervalIntegral_same]

omit [LinearOrder Mode] in
/-- **The matrix-coefficient recursion**: `Dₙ₊₁(τ)`'s `(m, n')` entry is `-∫ σ in 0..τ` of the
`k`-summed product of `V_I(σ)`'s and `Dₙ(σ)`'s own matrix coefficients — the scalar shadow of the
operator recursion, via `matrixCoeff_comp` and `matrixCoeff_operatorIntervalIntegral`. -/
theorem matrixCoeff_dysonCoeff_succ (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) (τ : ℝ)
    (m n' : FermionOccupation Mode) :
    Common.matrixCoeff (dysonCoeff ε V (n + 1) τ) m n' =
      - ∫ σ in (0 : ℝ)..τ, ∑ k : FermionOccupation Mode,
          Common.matrixCoeff (interactionPicture ε V σ) m k *
            Common.matrixCoeff (dysonCoeff ε V n σ) k n' := by
  rw [dysonCoeff_succ]
  have hneg : Common.matrixCoeff
      (- Common.operatorIntervalIntegral
          (fun σ => (interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) 0 τ) m n' =
        - Common.matrixCoeff (Common.operatorIntervalIntegral
          (fun σ => (interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) 0 τ) m n' := by
    simp [Common.matrixCoeff]
  rw [hneg, Common.matrixCoeff_operatorIntervalIntegral]
  congr 1
  exact intervalIntegral.integral_congr fun σ _ => Common.matrixCoeff_comp _ _ m n'

omit [LinearOrder Mode] in
/-- **Continuity of each Dyson coefficient's matrix coefficients**, by induction on `n`. The base
case is constant (`Dₙ` at `n = 0` is the constant operator `id`); the successor case's integrand
is continuous (a finite sum of products of continuous functions, using the inductive hypothesis
and `continuous_matrixCoeff_interactionPicture`), so its `τ`-indexed primitive is continuous
(`MeasureTheory.continuous_primitive`). -/
theorem continuous_matrixCoeff_dysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    ∀ m n' : FermionOccupation Mode,
      Continuous (fun τ : ℝ => Common.matrixCoeff (dysonCoeff ε V n τ) m n') := by
  induction n with
  | zero =>
    intro m n'
    simp only [dysonCoeff_zero]
    exact continuous_const
  | succ k ih =>
    intro m n'
    simp only [matrixCoeff_dysonCoeff_succ]
    have hcont : Continuous (fun σ : ℝ => ∑ k' : FermionOccupation Mode,
        Common.matrixCoeff (interactionPicture ε V σ) m k' *
          Common.matrixCoeff (dysonCoeff ε V k σ) k' n') :=
      continuous_finsetSum _ fun k' _ =>
        (continuous_matrixCoeff_interactionPicture ε V m k').mul (ih k' n')
    exact (intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0).neg

omit [LinearOrder Mode] in
/-- **Interval-integrability of each Dyson coefficient's matrix coefficients**, on any interval —
immediate from continuity. -/
theorem intervalIntegrable_matrixCoeff_dysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ)
    (m n' : FermionOccupation Mode) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => Common.matrixCoeff (dysonCoeff ε V n τ) m n')
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_dysonCoeff ε V n m n').intervalIntegrable a b

/-- **The order-`N` Dyson truncation**, `Σₙ₌₀^N λⁿ • Dₙ(τ)` — the finite partial sum in the
perturbation parameter `λ` standing in for the (not-yet-established, not claimed here) full
`Σₙ λⁿ Dₙ(τ)` series. -/
noncomputable def dysonTruncation (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (lam : ℂ) (N : ℕ) (τ : ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ∑ n ∈ Finset.range (N + 1), lam ^ n • dysonCoeff ε V n τ

end SecondQuantization
