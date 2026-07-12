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

/-- The expectation value `Tr[ρĤ]` of the Hamiltonian `Hop` in the state `ρ`. -/
noncomputable def energyExpValue (ρ : DensityOperator H) (Hop : Observable H) : ℝ :=
  (LinearMap.trace ℂ H ((ρ.1 ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H)).re

/-- `Tr[ρĤ]` expanded via the eigenvalues/eigenbases of `ρ` and `Hop` separately (which need
not coincide, since `ρ` and `Hop` need not commute). -/
theorem energyExpValue_eq_sum (ρ : DensityOperator H) (Hop : Observable H) :
    energyExpValue ρ Hop = ∑ m : Fin n, ∑ k : Fin n,
      ρ.2.1.isSymmetric.eigenvalues hn m * Hop.2.isSymmetric.eigenvalues hn k *
        ‖inner ℂ (Hop.2.isSymmetric.eigenvectorBasis hn k)
          (ρ.2.1.isSymmetric.eigenvectorBasis hn m)‖ ^ 2 := by
  have hsymmρ : LinearMap.IsSymmetric (ρ.1 : H →ₗ[ℂ] H) := ρ.2.1.isSymmetric
  have hsymmHop : LinearMap.IsSymmetric (Hop.1 : H →ₗ[ℂ] H) := Hop.2.isSymmetric
  set p := hsymmρ.eigenvalues hn with hp_def
  set E := hsymmHop.eigenvalues hn with hE_def
  set bρ := hsymmρ.eigenvectorBasis hn with hbρ_def
  set bE := hsymmHop.eigenvectorBasis hn with hbE_def
  have hEigenρ : ∀ m, (ρ.1 : H →ₗ[ℂ] H) (bρ m) = (p m : ℂ) • bρ m := fun m =>
    hsymmρ.apply_eigenvectorBasis hn m
  have hEigenHop : ∀ k, (Hop.1 : H →ₗ[ℂ] H) (bE k) = (E k : ℂ) • bE k := fun k =>
    hsymmHop.apply_eigenvectorBasis hn k
  have hρbE : ∀ k, (ρ.1 : H →ₗ[ℂ] H) (bE k) =
      ∑ m : Fin n, ((p m : ℂ) * inner ℂ (bρ m) (bE k)) • bρ m := by
    intro k
    conv_lhs => rw [← bρ.sum_repr' (bE k)]
    rw [map_sum]
    simp_rw [map_smul, hEigenρ, smul_smul]
    congr 1; ext m; rw [mul_comm]
  have hinner : ∀ k, inner ℂ (bE k) ((ρ.1 : H →ₗ[ℂ] H) (bE k)) =
      ∑ m : Fin n, (p m : ℂ) * (inner ℂ (bρ m) (bE k) * inner ℂ (bE k) (bρ m)) := by
    intro k
    rw [hρbE, inner_sum]
    congr 1
    ext m
    rw [inner_smul_right, mul_assoc]
  have htrace : (LinearMap.trace ℂ H ((ρ.1 ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H)) =
      ∑ k : Fin n, ∑ m : Fin n,
        (p m : ℂ) * (E k : ℂ) * (inner ℂ (bρ m) (bE k) * inner ℂ (bE k) (bρ m)) := by
    rw [LinearMap.trace_eq_sum_inner ((ρ.1 ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) bE]
    have step1 : ∀ k : Fin n,
        inner ℂ (bE k) (((ρ.1 ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) (bE k)) =
          (E k : ℂ) * inner ℂ (bE k) ((ρ.1 : H →ₗ[ℂ] H) (bE k)) := by
      intro k
      show inner ℂ (bE k) ((ρ.1 : H →ₗ[ℂ] H) ((Hop.1 : H →ₗ[ℂ] H) (bE k))) =
        (E k : ℂ) * inner ℂ (bE k) ((ρ.1 : H →ₗ[ℂ] H) (bE k))
      rw [hEigenHop, map_smul, inner_smul_right]
    simp_rw [step1, hinner, Finset.mul_sum]
    congr 1; ext k; congr 1; ext m
    ring
  have hfinal : (LinearMap.trace ℂ H ((ρ.1 ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H)).re =
      ∑ m : Fin n, ∑ k : Fin n, p m * E k * ‖inner ℂ (bE k) (bρ m)‖ ^ 2 := by
    rw [htrace, Finset.sum_comm]
    rw [show (∑ m : Fin n, ∑ k : Fin n,
        (p m : ℂ) * (E k : ℂ) * (inner ℂ (bρ m) (bE k) * inner ℂ (bE k) (bρ m))) =
        ((∑ m : Fin n, ∑ k : Fin n, p m * E k * ‖inner ℂ (bE k) (bρ m)‖ ^ 2 : ℝ) : ℂ) from ?_]
    · exact Complex.ofReal_re _
    · rw [Complex.ofReal_sum]
      congr 1; ext m
      rw [Complex.ofReal_sum]
      congr 1; ext k
      have hnormsq : inner ℂ (bρ m) (bE k) * inner ℂ (bE k) (bρ m) =
          ((‖inner ℂ (bE k) (bρ m)‖ ^ 2 : ℝ) : ℂ) := by
        have hc : inner ℂ (bρ m) (bE k) = starRingEnd ℂ (inner ℂ (bE k) (bρ m)) := by
          rw [inner_conj_symm]
        rw [hc, mul_comm, Complex.mul_conj]
        norm_cast
        exact Complex.normSq_eq_norm_sq _
      push_cast [hnormsq]
      ring
  exact hfinal

/-- **Helmholtz free energy inequality.** For any density operator `ρ`, the free energy
`F[ρ] = Tr[ρĤ] - (1/β)·vonNeumannEntropy ρ` is bounded below by `-(1/β)·ln Z(β)` — the free
energy of the canonical (Gibbs) state. This is the precise sense (see `notes/roadmap.md`) in
which the canonical distribution minimizes the Helmholtz free energy: `-(1/β)·ln Z(β)` is
`gibbsState`'s own free energy (not separately verified here, but follows from
`vonNeumannEntropy (gibbsState hn Hop β) = β·energyExpValue (gibbsState hn Hop β) Hop + ln Z(β)`,
a direct computation from `gibbsState`'s definition). -/
theorem helmholtzFreeEnergy_ge [NeZero n] (ρ : DensityOperator H) (Hop : Observable H)
    (β : ℝ) (hβ : 0 < β) :
    -(1 / β) * Real.log (partitionFunction hn Hop β) ≤
      energyExpValue ρ Hop - (1 / β) * vonNeumannEntropy hn ρ := by
  have hsymmρ : LinearMap.IsSymmetric (ρ.1 : H →ₗ[ℂ] H) := ρ.2.1.isSymmetric
  have hsymmHop : LinearMap.IsSymmetric (Hop.1 : H →ₗ[ℂ] H) := Hop.2.isSymmetric
  have htrρ : LinearMap.trace ℂ H (ρ.1 : H →ₗ[ℂ] H) = 1 := ρ.2.2
  set p := hsymmρ.eigenvalues hn with hp_def
  set E := hsymmHop.eigenvalues hn with hE_def
  set bρ := hsymmρ.eigenvectorBasis hn with hbρ_def
  set bE := hsymmHop.eigenvectorBasis hn with hbE_def
  set Z := partitionFunction hn Hop β with hZ_def
  have hZpos : 0 < Z := partitionFunction_pos hn Hop β
  set w : Fin n → ℝ := fun k => Real.exp (-β * E k) / Z with hw_def
  have hw_pos : ∀ k, 0 < w k := fun k => div_pos (Real.exp_pos _) hZpos
  have hw_sum : ∑ k, w k = 1 := by
    show (∑ k : Fin n, Real.exp (-β * E k) / Z) = 1
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  set c : Fin n → Fin n → ℝ := fun m k => ‖inner ℂ (bE k) (bρ m)‖ ^ 2 with hc_def
  have hc_nonneg : ∀ m k, 0 ≤ c m k := fun m k => sq_nonneg _
  have hres1 : ∀ m, ∑ k, c m k = 1 := fun m => by
    simpa [hc_def] using bE.sum_sq_norm_inner_right (bρ m)
  have hres2 : ∀ k, ∑ m, c m k = 1 := fun k => by
    simpa [hc_def] using bρ.sum_sq_norm_inner_left (bE k)
  have hp_sum : ∑ m, p m = 1 := by
    have h := hsymmρ.re_trace_eq_sum_eigenvalues (hn := hn)
    rw [htrρ] at h
    simpa [hp_def] using h.symm
  have hp_nonneg : ∀ m, 0 ≤ p m := fun m => eigenvalues_nonneg hn ρ m
  have key : ∀ m k, (p m - w k) * c m k ≤ p m * (Real.log (p m) - Real.log (w k)) * c m k := by
    intro m k
    rcases (hp_nonneg m).eq_or_lt with hp0 | hp0
    · rw [← hp0]
      nlinarith [hc_nonneg m k, (hw_pos k).le]
    · have hlog : Real.log (w k / p m) ≤ w k / p m - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hw_pos k) hp0)
      rw [Real.log_div (ne_of_gt (hw_pos k)) (ne_of_gt hp0)] at hlog
      have hlog' : (Real.log (w k) - Real.log (p m) + 1) * p m ≤ w k := by
        rw [← le_div_iff₀ hp0]; linarith [hlog]
      have step : p m - w k ≤ p m * (Real.log (p m) - Real.log (w k)) := by
        nlinarith [hlog']
      exact mul_le_mul_of_nonneg_right step (hc_nonneg m k)
  have expand : ∑ m, ∑ k, (p m - w k) * c m k = 0 := by
    have step1 : ∑ m : Fin n, ∑ k : Fin n, (p m - w k) * c m k
        = ∑ m : Fin n, ∑ k : Fin n, p m * c m k - ∑ m : Fin n, ∑ k : Fin n, w k * c m k := by
      simp_rw [sub_mul, Finset.sum_sub_distrib]
    have step2 : ∑ m : Fin n, ∑ k : Fin n, p m * c m k = ∑ m, p m := by
      simp_rw [← Finset.mul_sum, hres1, mul_one]
    have step3 : ∑ m : Fin n, ∑ k : Fin n, w k * c m k = ∑ k, w k := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hres2, mul_one]
    rw [step1, step2, step3, hp_sum, hw_sum, sub_self]
  have hklein : 0 ≤ ∑ m, ∑ k, p m * (Real.log (p m) - Real.log (w k)) * c m k := by
    calc (0:ℝ) = ∑ m, ∑ k, (p m - w k) * c m k := expand.symm
      _ ≤ _ := Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun k _ => key m k
  have hlogw : ∀ k, Real.log (w k) = -β * E k - Real.log Z := by
    intro k
    show Real.log (Real.exp (-β * E k) / Z) = -β * E k - Real.log Z
    rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hrw : ∑ m, ∑ k, p m * (Real.log (p m) - Real.log (w k)) * c m k =
      -vonNeumannEntropy hn ρ + β * energyExpValue ρ Hop + Real.log Z := by
    have expand2 : ∑ m : Fin n, ∑ k : Fin n,
        p m * (Real.log (p m) - Real.log (w k)) * c m k =
        ∑ m : Fin n, ∑ k : Fin n,
          (p m * Real.log (p m) * c m k + β * (p m * E k * c m k) +
            Real.log Z * (p m * c m k)) := by
      congr 1; ext m; congr 1; ext k
      rw [hlogw k]; ring
    rw [expand2]
    simp_rw [Finset.sum_add_distrib]
    have t1 : ∑ m : Fin n, ∑ k : Fin n, p m * Real.log (p m) * c m k =
        ∑ m, p m * Real.log (p m) := by
      simp_rw [← Finset.mul_sum, hres1, mul_one]
    have t2 : ∑ m : Fin n, ∑ k : Fin n, β * (p m * E k * c m k) =
        β * energyExpValue ρ Hop := by
      simp_rw [← Finset.mul_sum]
      congr 1
      exact (energyExpValue_eq_sum hn ρ Hop).symm
    have t3 : ∑ m : Fin n, ∑ k : Fin n, Real.log Z * (p m * c m k) = Real.log Z := by
      simp_rw [← Finset.mul_sum, hres1, mul_one]
      rw [hp_sum, mul_one]
    rw [t1, t2, t3]
    have hvN : vonNeumannEntropy hn ρ = -∑ m, p m * Real.log (p m) := by
      show (∑ i : Fin n, Real.negMulLog (p i)) = -∑ m, p m * Real.log (p m)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by rw [Real.negMulLog]; ring
    rw [hvN]; ring
  rw [hrw] at hklein
  have hgoal' : vonNeumannEntropy hn ρ ≤ β * energyExpValue ρ Hop + Real.log Z := by linarith
  have hmul := mul_le_mul_of_nonneg_left hgoal' (by positivity : (0:ℝ) ≤ 1 / β)
  rw [mul_add, ← mul_assoc, one_div, inv_mul_cancel₀ hβ.ne', one_mul] at hmul
  simp only [one_div]
  linarith [hmul]

end QuantumTheory
