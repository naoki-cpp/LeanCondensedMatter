import LeanCondensedMatter.QuantumTheory.DensityOperator
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Von Neumann entropy and Boltzmann's principle

Formalizes the von Neumann entropy of a density operator, the mathematical content of
**Boltzmann's principle**: the postulate that `k_B` times the von Neumann entropy equals
the thermodynamic entropy `S[U,V,N]`.

**Scope note:** Boltzmann's principle itself — the equality of `k_B * vonNeumannEntropy ρ`
with a thermodynamic entropy `S[U,V,N]` — is a postulate connecting this formal quantity to
thermodynamics, which is not formalized in this project (see `notes/model-and-assumptions.md`
and the scope discussion for the Linked Cluster Theorem target in `notes/roadmap.md`, which
argues thermodynamics proper is out of scope for that target). Only the mathematical object
the postulate is about — the von Neumann entropy of a density operator — is defined here.
-/

namespace QuantumTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]
variable {n : ℕ} (hn : Module.finrank ℂ H = n)

/-- The von Neumann entropy `-Tr[ρ ln ρ]` of a density operator `ρ`, computed from its
eigenvalues (which are real since `ρ` is self-adjoint). The physical entropy of Boltzmann's
principle is `k_B` times this quantity. -/
noncomputable def vonNeumannEntropy (ρ : DensityOperator H) : ℝ :=
  ∑ i : Fin n, Real.negMulLog (ρ.2.1.isSymmetric.eigenvalues hn i)

/-- The eigenvalues of a density operator are nonnegative — they are the probabilities
`p_i` of measuring the system in the corresponding eigenstate. -/
theorem eigenvalues_nonneg (ρ : DensityOperator H) (i : Fin n) :
    0 ≤ ρ.2.1.isSymmetric.eigenvalues hn i :=
  ρ.2.1.toLinearMap.nonneg_eigenvalues hn i

/-- The quantum relative entropy `Σ_{m,k} p_m (ln p_m - ln q_k) |⟨k|m⟩|²` between two density
operators, expressed via their eigenvalues `p`/`q` and eigenvectors. This computes
`Tr[ρ ln ρ] - Tr[ρ ln ρ']`, the quantity whose nonnegativity is the Gibbs–Klein inequality. -/
noncomputable def relEntropy (ρ ρ' : DensityOperator H) : ℝ :=
  ∑ m : Fin n, ∑ k : Fin n,
    ρ.2.1.isSymmetric.eigenvalues hn m *
      (Real.log (ρ.2.1.isSymmetric.eigenvalues hn m) -
        Real.log (ρ'.2.1.isSymmetric.eigenvalues hn k)) *
      ‖inner ℂ (ρ'.2.1.isSymmetric.eigenvectorBasis hn k)
        (ρ.2.1.isSymmetric.eigenvectorBasis hn m)‖ ^ 2

/-- **Gibbs–Klein inequality.** The quantum relative entropy is nonnegative, provided `ρ'` has
full support (all eigenvalues strictly positive) — which holds automatically for a canonical
(Gibbs) state `e^{-βH}/Z`, the intended application (see `notes/roadmap.md`). -/
theorem relEntropy_nonneg (ρ ρ' : DensityOperator H)
    (hq : ∀ k, 0 < ρ'.2.1.isSymmetric.eigenvalues hn k) :
    0 ≤ relEntropy hn ρ ρ' := by
  -- Extract opaque copies of the symmetry/trace facts first, so that later rewriting the
  -- trace facts cannot disturb the (dependent) type of `ρ.property` used elsewhere.
  have hsymmρ : LinearMap.IsSymmetric (ρ.1 : H →ₗ[ℂ] H) := ρ.2.1.isSymmetric
  have hsymmρ' : LinearMap.IsSymmetric (ρ'.1 : H →ₗ[ℂ] H) := ρ'.2.1.isSymmetric
  have htrρ : LinearMap.trace ℂ H (ρ.1 : H →ₗ[ℂ] H) = 1 := ρ.2.2
  have htrρ' : LinearMap.trace ℂ H (ρ'.1 : H →ₗ[ℂ] H) = 1 := ρ'.2.2
  set p := hsymmρ.eigenvalues hn with hp_def
  set q := hsymmρ'.eigenvalues hn with hq_def
  set bρ := hsymmρ.eigenvectorBasis hn with hbρ_def
  set bρ' := hsymmρ'.eigenvectorBasis hn with hbρ'_def
  set c : Fin n → Fin n → ℝ := fun m k => ‖inner ℂ (bρ' k) (bρ m)‖ ^ 2 with hc_def
  have hc_nonneg : ∀ m k, 0 ≤ c m k := fun m k => sq_nonneg _
  have hres1 : ∀ m, ∑ k, c m k = 1 := fun m => by
    simpa [hc_def] using bρ'.sum_sq_norm_inner_right (bρ m)
  have hres2 : ∀ k, ∑ m, c m k = 1 := fun k => by
    simpa [hc_def] using bρ.sum_sq_norm_inner_left (bρ' k)
  have hp_sum : ∑ m, p m = 1 := by
    have h := hsymmρ.re_trace_eq_sum_eigenvalues (hn := hn)
    rw [htrρ] at h
    simpa [hp_def] using h.symm
  have hq_sum : ∑ k, q k = 1 := by
    have h := hsymmρ'.re_trace_eq_sum_eigenvalues (hn := hn)
    rw [htrρ'] at h
    simpa [hq_def] using h.symm
  have hp_nonneg : ∀ m, 0 ≤ p m := fun m => eigenvalues_nonneg hn ρ m
  have key : ∀ m k, (p m - q k) * c m k ≤ p m * (Real.log (p m) - Real.log (q k)) * c m k := by
    intro m k
    rcases (hp_nonneg m).eq_or_lt with hp0 | hp0
    · rw [← hp0]
      nlinarith [hc_nonneg m k, (hq k).le]
    · have hlog : Real.log (q k / p m) ≤ q k / p m - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hq k) hp0)
      rw [Real.log_div (ne_of_gt (hq k)) (ne_of_gt hp0)] at hlog
      have hlog' : (Real.log (q k) - Real.log (p m) + 1) * p m ≤ q k := by
        rw [← le_div_iff₀ hp0]; linarith [hlog]
      have step : p m - q k ≤ p m * (Real.log (p m) - Real.log (q k)) := by
        nlinarith [hlog']
      exact mul_le_mul_of_nonneg_right step (hc_nonneg m k)
  have expand : ∑ m, ∑ k, (p m - q k) * c m k = 0 := by
    have step1 : ∑ m : Fin n, ∑ k : Fin n, (p m - q k) * c m k
        = ∑ m : Fin n, ∑ k : Fin n, p m * c m k - ∑ m : Fin n, ∑ k : Fin n, q k * c m k := by
      simp_rw [sub_mul, Finset.sum_sub_distrib]
    have step2 : ∑ m : Fin n, ∑ k : Fin n, p m * c m k = ∑ m, p m := by
      simp_rw [← Finset.mul_sum, hres1, mul_one]
    have step3 : ∑ m : Fin n, ∑ k : Fin n, q k * c m k = ∑ k, q k := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hres2, mul_one]
    rw [step1, step2, step3, hp_sum, hq_sum, sub_self]
  calc (0:ℝ) = ∑ m, ∑ k, (p m - q k) * c m k := expand.symm
    _ ≤ ∑ m, ∑ k, p m * (Real.log (p m) - Real.log (q k)) * c m k :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun k _ => key m k
    _ = relEntropy hn ρ ρ' := rfl

/-- The partition function `Z(β) = Σᵢ e^{-βEᵢ}` for a Hamiltonian `Hop` at inverse
temperature `β`, where `Eᵢ` are `Hop`'s eigenvalues. -/
noncomputable def partitionFunction (Hop : Observable H) (β : ℝ) : ℝ :=
  ∑ i : Fin n, Real.exp (-β * Hop.2.isSymmetric.eigenvalues hn i)

theorem partitionFunction_pos [NeZero n] (Hop : Observable H) (β : ℝ) :
    0 < partitionFunction hn Hop β :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨⟨0, NeZero.pos n⟩, Finset.mem_univ _⟩

/-- The canonical (Gibbs) density operator `e^{-βH}/Z(β)` associated to a Hamiltonian `Hop`
at inverse temperature `β`. -/
noncomputable def gibbsState [NeZero n] (Hop : Observable H) (β : ℝ) : DensityOperator H :=
  ⟨∑ i : Fin n,
      ((Real.exp (-β * Hop.2.isSymmetric.eigenvalues hn i) / partitionFunction hn Hop β : ℝ) : ℂ) •
        InnerProductSpace.rankOne ℂ (Hop.2.isSymmetric.eigenvectorBasis hn i)
          (Hop.2.isSymmetric.eigenvectorBasis hn i),
    by
      have hZpos := partitionFunction_pos hn Hop β
      refine ⟨ContinuousLinearMap.isPositive_sum Finset.univ fun i _ =>
        (InnerProductSpace.isPositive_rankOne_self _).smul_of_nonneg
          (RCLike.ofReal_nonneg.mpr (div_nonneg (Real.exp_pos _).le hZpos.le)), ?_⟩
      have hsum1 : (∑ i : Fin n, Real.exp (-β * Hop.2.isSymmetric.eigenvalues hn i) /
          partitionFunction hn Hop β) = 1 := by
        rw [← Finset.sum_div]
        show partitionFunction hn Hop β / partitionFunction hn Hop β = 1
        exact div_self hZpos.ne'
      have step : ∀ i : Fin n, (LinearMap.trace ℂ H)
          ((((Real.exp (-β * Hop.2.isSymmetric.eigenvalues hn i) /
              partitionFunction hn Hop β : ℝ) : ℂ) •
            InnerProductSpace.rankOne ℂ (Hop.2.isSymmetric.eigenvectorBasis hn i)
              (Hop.2.isSymmetric.eigenvectorBasis hn i) : H →L[ℂ] H) : H →ₗ[ℂ] H) =
          ((Real.exp (-β * Hop.2.isSymmetric.eigenvalues hn i) /
              partitionFunction hn Hop β : ℝ) : ℂ) := by
        intro i
        rw [ContinuousLinearMap.toLinearMap_smul, map_smul, InnerProductSpace.trace_rankOne,
          inner_self_eq_norm_sq_to_K, OrthonormalBasis.norm_eq_one]
        norm_num
      rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
      simp_rw [step]
      rw [← Complex.ofReal_sum, hsum1, Complex.ofReal_one]⟩

end QuantumTheory
