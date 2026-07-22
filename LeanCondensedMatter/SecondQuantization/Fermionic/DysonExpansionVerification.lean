import LeanCondensedMatter.SecondQuantization.Fermionic.DysonExpansion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false

/-!
# Sanity checks for the Dyson coefficients: time-independent interactions

Step 5 (PR 4) of Phase 9's Dyson-series plan (`notes/roadmaps/second-quantization.md`): if the
interaction picture leaves `V` fixed (`∀ τ, V_I(τ) = V`, e.g. because `V` commutes with the free
Hamiltonian), the continuous-integral recursion `dysonCoeff` degenerates to the ordinary scalar
Taylor coefficients `(-τ)ⁿ/n! • Vⁿ` — matching `FormalExp.lean`'s `formalExpTerm (τ • V) n`, i.e.
the formal Taylor coefficients of `exp(-τV)`. Specializing to the existing density–density
`interactionHamiltonian` (diagonal in the occupation basis, hence commuting with
`freeHamiltonian`) verifies the continuous-integral construction reduces to the expected
exponential-series coefficients on a genuine (if physically restrictive) example.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- **A time-independent interaction's Dyson coefficients collapse to the ordinary scalar Taylor
coefficients**: if `V_I(τ) = V` for every `τ`, then `Dₙ(τ) = (-τ)ⁿ/n! • Vⁿ`. Proved by induction
on `n`: the base case is `dysonCoeff_zero`; the successor case rewrites the recursion's integrand
to a fixed scalar multiple of `V^(k+1)` (via `hV` and the inductive hypothesis), reduces the
resulting scalar-times-fixed-operator interval integral to a scalar integral
(`Common.matrixCoeff_ext`), and evaluates that integral via `intervalIntegral.integral_pow`. -/
theorem dysonCoeff_eq_of_time_independent (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (hV : ∀ τ, interactionPicture ε V τ = V) :
    ∀ (n : ℕ) (τ : ℝ), dysonCoeff ε V n τ = ((-τ : ℂ) ^ n / n.factorial) • V ^ n := by
  intro n
  induction n with
  | zero => intro τ; simp [dysonCoeff_zero, Module.End.one_eq_id]
  | succ k ih =>
    intro τ
    rw [dysonCoeff_succ]
    have hcomp : V.comp (V ^ k) = V ^ (k + 1) := by rw [pow_succ', Module.End.mul_eq_comp]
    have hfun : (fun σ : ℝ => (interactionPicture ε V σ).comp (dysonCoeff ε V k σ)) =
        fun σ : ℝ => (((-σ : ℂ) ^ k / k.factorial)) • V ^ (k + 1) := by
      funext σ
      rw [hV σ, ih σ, LinearMap.comp_smul, hcomp]
    rw [hfun]
    have hval : Common.operatorIntervalIntegral
        (fun σ : ℝ => (((-σ : ℂ) ^ k / k.factorial)) • V ^ (k + 1)) 0 τ =
          (∫ σ in (0 : ℝ)..τ, ((-σ : ℂ) ^ k / k.factorial)) • V ^ (k + 1) := by
      apply Common.matrixCoeff_ext
      intro m n'
      rw [Common.matrixCoeff_operatorIntervalIntegral]
      simp only [Common.matrixCoeff_smul]
      rw [intervalIntegral.integral_mul_const]
    rw [hval]
    have hpow : (∫ σ in (0 : ℝ)..τ, (-σ) ^ k) = -(-τ) ^ (k + 1) / (k + 1) := by
      have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := τ) (fun x : ℝ => x ^ k)
      simp only [neg_zero] at h
      rw [h, integral_pow, zero_pow (Nat.succ_ne_zero k)]
      ring
    have hcint : (∫ σ in (0 : ℝ)..τ, ((-σ : ℂ) ^ k / (k.factorial : ℂ))) =
        - ((-τ : ℂ) ^ (k + 1) / ((k + 1).factorial : ℂ)) := by
      rw [intervalIntegral.integral_div]
      have hcast : (∫ σ in (0 : ℝ)..τ, ((-σ : ℂ)) ^ k) =
          ((∫ σ in (0 : ℝ)..τ, (-σ) ^ k : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]
        apply intervalIntegral.integral_congr
        intro σ _
        push_cast
        ring
      rw [hcast, hpow, Nat.factorial_succ]
      push_cast
      field_simp
    rw [hcint, neg_smul, neg_neg]

/-- **`interactionHamiltonian` is time-independent in the interaction picture**: it is diagonal in
the occupation basis (`interactionHamiltonian_basisState`), so it commutes with `freeHamiltonian`
and hence with the free evolution `e^{τH₀}` for any `τ` — the same cancellation
`imaginaryTimeEvolve_freeHamiltonian` uses for the free Hamiltonian's own trivial evolution. -/
theorem imaginaryTimeEvolve_interactionHamiltonian (ε : Mode → ℝ) (Vint : Mode → Mode → ℝ)
    (τ : ℝ) : imaginaryTimeEvolve ε τ (interactionHamiltonian Vint) = interactionHamiltonian Vint
    := by
  apply linearMap_ext_basisState
  intro n
  rw [imaginaryTimeEvolve_apply, imaginaryTimeEvolveFree_basisState, map_smul,
    interactionHamiltonian_basisState, smul_smul, map_smul, imaginaryTimeEvolveFree_basisState,
    smul_smul]
  congr 1
  have hx : (↑(-τ) : ℂ) * ∑ i ∈ n, (ε i : ℂ) = -((τ : ℂ) * ∑ i ∈ n, (ε i : ℂ)) := by
    push_cast; ring
  rw [hx, mul_right_comm, Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]

/-- **`interactionHamiltonian`'s Dyson coefficients reduce to the ordinary scalar Taylor
coefficients**: combining `imaginaryTimeEvolve_interactionHamiltonian` (time-independence) with
`dysonCoeff_eq_of_time_independent`, the continuous-integral construction reduces to
`(-τ)ⁿ/n! • Vintⁿ` on this genuine (if basis-diagonal, hence physically restrictive) example. -/
theorem dysonCoeff_interactionHamiltonian_eq (ε : Mode → ℝ) (Vint : Mode → Mode → ℝ) (n : ℕ)
    (τ : ℝ) :
    dysonCoeff ε (interactionHamiltonian Vint) n τ =
      ((-τ : ℂ) ^ n / n.factorial) • (interactionHamiltonian Vint) ^ n :=
  dysonCoeff_eq_of_time_independent ε (interactionHamiltonian Vint)
    (imaginaryTimeEvolve_interactionHamiltonian ε Vint) n τ

end SecondQuantization
