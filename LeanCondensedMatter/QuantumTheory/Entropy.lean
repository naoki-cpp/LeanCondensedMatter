import LeanCondensedMatter.QuantumTheory.DensityOperator
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

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

/-- **The finite-dimensional Gibbs–Klein inequality, as a pure real-analysis fact.** Given
probability distributions `p`, `q` (nonneg, summing to `1`, `q` everywhere positive) and a
`Fin n × Fin n`-indexed nonnegative "coupling" `c` whose row sums and column sums are each `1`,
`Σ_m Σ_k p m (ln(p m) - ln(q k)) c m k ≥ 0`. No Hilbert-space content: `c` abstracts the squared
inner products `‖⟨k|m⟩‖²` used by `relEntropy`/`helmholtzFreeEnergy_ge`, whose row/column sums are
`1` by completeness of each eigenbasis. -/
theorem gibbs_klein_double_sum {n : ℕ} (p q : Fin n → ℝ) (c : Fin n → Fin n → ℝ)
    (hp_nonneg : ∀ m, 0 ≤ p m) (hq_pos : ∀ k, 0 < q k) (hc_nonneg : ∀ m k, 0 ≤ c m k)
    (hp_sum : ∑ m, p m = 1) (hq_sum : ∑ k, q k = 1) (hrow : ∀ m, ∑ k, c m k = 1)
    (hcol : ∀ k, ∑ m, c m k = 1) :
    0 ≤ ∑ m, ∑ k, p m * (Real.log (p m) - Real.log (q k)) * c m k := by
  have key : ∀ m k, (p m - q k) * c m k ≤ p m * (Real.log (p m) - Real.log (q k)) * c m k := by
    intro m k
    rcases (hp_nonneg m).eq_or_lt with hp0 | hp0
    · rw [← hp0]
      nlinarith [hc_nonneg m k, (hq_pos k).le]
    · have hlog : Real.log (q k / p m) ≤ q k / p m - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hq_pos k) hp0)
      rw [Real.log_div (ne_of_gt (hq_pos k)) (ne_of_gt hp0)] at hlog
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
      simp_rw [← Finset.mul_sum, hrow, mul_one]
    have step3 : ∑ m : Fin n, ∑ k : Fin n, q k * c m k = ∑ k, q k := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hcol, mul_one]
    rw [step1, step2, step3, hp_sum, hq_sum, sub_self]
  calc (0:ℝ) = ∑ m, ∑ k, (p m - q k) * c m k := expand.symm
    _ ≤ ∑ m, ∑ k, p m * (Real.log (p m) - Real.log (q k)) * c m k :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun k _ => key m k

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
  exact gibbs_klein_double_sum p q c hp_nonneg hq hc_nonneg hp_sum hq_sum hres1 hres2

/-- The partition function `Z(β) = Σᵢ e^{-βEᵢ}` for a Hamiltonian `Hop` at inverse
temperature `β`, where `Eᵢ` are `Hop`'s eigenvalues. -/
noncomputable def partitionFunction (Hop : Observable H) (β : ℝ) : ℝ :=
  ∑ i : Fin n, Real.exp (-β * Hop.2.isSymmetric.eigenvalues hn i)

theorem partitionFunction_pos [NeZero n] (Hop : Observable H) (β : ℝ) :
    0 < partitionFunction hn Hop β :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨⟨0, NeZero.pos n⟩, Finset.mem_univ _⟩

/-- **Diagonal presentation determines eigenvalues up to reindexing.** If a self-adjoint
operator `T` is presented as `∑ i, w i • |b i⟩⟨b i|` for an orthonormal basis `b` and
real weights `w`, then the multiset of weights `w` coincides with the multiset of `T`'s own
(Mathlib-sorted) spectral eigenvalues. This lets a sum `∑ i, f (w i)` over the hand-built
weights be identified with `∑ i, f (T's own eigenvalues i)` — in particular with
`vonNeumannEntropy` — without needing to know the explicit reindexing permutation, since both
sides are the sum of `f` over the same multiset. Proved via the characteristic polynomial,
which is basis-independent (`LinearMap.charpoly_toMatrix`) and whose roots are the operator's
eigenvalues (`LinearMap.IsSymmetric.charpoly_eq`) as well as, for a diagonal matrix, literally
the diagonal entries (`Matrix.charpoly_diagonal`). -/
theorem diagOp_eigenvalues_map_eq (b : OrthonormalBasis (Fin n) ℂ H) (w : Fin n → ℝ)
    (hself : IsSelfAdjoint
      ((∑ i : Fin n, (w i : ℂ) • InnerProductSpace.rankOne ℂ (b i) (b i)) : H →L[ℂ] H)) :
    Finset.univ.val.map w = Finset.univ.val.map (hself.isSymmetric.eigenvalues hn) := by
  classical
  open Polynomial in
  set T : H →L[ℂ] H := ∑ i : Fin n, (w i : ℂ) • InnerProductSpace.rankOne ℂ (b i) (b i) with hT_def
  have hTb : ∀ j, (T : H →ₗ[ℂ] H) (b j) = (w j : ℂ) • b j := by
    intro j
    have hTapply : (T : H →ₗ[ℂ] H) (b j) =
        ∑ i : Fin n, (w i : ℂ) • InnerProductSpace.rankOne ℂ (b i) (b i) (b j) := by
      simp [hT_def]
    rw [hTapply, Finset.sum_eq_single j]
    · simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, b.orthonormal.1 j]
    · intro i _ hij
      simp [InnerProductSpace.rankOne_apply, b.orthonormal.2 hij]
    · simp
  have htoMatrix : (T : H →ₗ[ℂ] H).toMatrix b.toBasis b.toBasis =
      Matrix.diagonal (fun i => (w i : ℂ)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, hTb j, map_smul, PiLp.smul_apply, b.repr_self]
    simp only [Matrix.diagonal_apply, PiLp.single_apply]
    split_ifs with h <;> simp [h, smul_eq_mul]
  have hcharpoly1 : (T : H →ₗ[ℂ] H).charpoly = ∏ i : Fin n, (X - C (w i : ℂ)) := by
    rw [← (T : H →ₗ[ℂ] H).charpoly_toMatrix b.toBasis, htoMatrix, Matrix.charpoly_diagonal]
  have hcharpoly2 : (T : H →ₗ[ℂ] H).charpoly =
      ∏ i : Fin n, (X - C (hself.isSymmetric.eigenvalues hn i : ℂ)) :=
    hself.isSymmetric.charpoly_eq hn
  have hroots : (∏ i : Fin n, (X - C (w i : ℂ))).roots =
      (∏ i : Fin n, (X - C (hself.isSymmetric.eigenvalues hn i : ℂ))).roots := by
    rw [← hcharpoly1, hcharpoly2]
  have hroots_eq : ∀ f : Fin n → ℝ,
      (∏ i : Fin n, (X - C (f i : ℂ))).roots =
        Multiset.map Complex.ofReal (Finset.univ.val.map f) := by
    intro f
    have hne : (∏ i : Fin n, (X - C (f i : ℂ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _
    rw [show (∏ i : Fin n, (X - C (f i : ℂ))) = Finset.univ.prod (fun i => X - C (f i : ℂ)) from
      rfl, roots_prod _ _ hne]
    simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton, Multiset.map_map]
    rfl
  rw [hroots_eq w, hroots_eq (hself.isSymmetric.eigenvalues hn)] at hroots
  exact Multiset.map_injective Complex.ofReal_injective hroots

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
`gibbsState`'s own free energy, verified separately by `vonNeumannEntropy_gibbsState` below. -/
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

/-- **`gibbsState`'s own free energy.** The canonical state's von Neumann entropy is exactly
`β·Tr[ρĤ] + ln Z(β)`, so its Helmholtz free energy `Tr[ρĤ] - (1/β)·S_vN(ρ)` equals
`-(1/β)·ln Z(β)` — the lower bound of `helmholtzFreeEnergy_ge` is attained by `gibbsState`
itself. This closes the gap left open in `helmholtzFreeEnergy_ge`'s docstring, using
`diagOp_eigenvalues_map_eq` to identify `gibbsState`'s own (Mathlib-sorted) spectral data
with its hand-built Boltzmann weights without needing an explicit reindexing permutation. -/
theorem vonNeumannEntropy_gibbsState [NeZero n] (Hop : Observable H) (β : ℝ) :
    vonNeumannEntropy hn (gibbsState hn Hop β) =
      β * energyExpValue (gibbsState hn Hop β) Hop + Real.log (partitionFunction hn Hop β) := by
  set Z := partitionFunction hn Hop β with hZ_def
  set E := Hop.2.isSymmetric.eigenvalues hn with hE_def
  set bE := Hop.2.isSymmetric.eigenvectorBasis hn with hbE_def
  set w : Fin n → ℝ := fun i => Real.exp (-β * E i) / Z with hw_def
  have hgibbs_eq : (gibbsState hn Hop β).1 =
      ∑ i : Fin n, (w i : ℂ) • InnerProductSpace.rankOne ℂ (bE i) (bE i) := rfl
  have hself : IsSelfAdjoint (gibbsState hn Hop β).1 := (gibbsState hn Hop β).2.1.isSelfAdjoint
  have hmap := diagOp_eigenvalues_map_eq hn bE w (hgibbs_eq ▸ hself)
  have hsum_eq : ∀ F : ℝ → ℝ,
      ∑ i, F (w i) = ∑ i, F ((gibbsState hn Hop β).2.1.isSymmetric.eigenvalues hn i) := by
    intro F
    have h1 : Finset.univ.val.map (F ∘ w) =
        Finset.univ.val.map (F ∘ (gibbsState hn Hop β).2.1.isSymmetric.eigenvalues hn) := by
      rw [← Multiset.map_map, ← Multiset.map_map, hmap]
      rfl
    calc ∑ i, F (w i) = (Finset.univ.val.map (F ∘ w)).sum := rfl
      _ = (Finset.univ.val.map (F ∘ (gibbsState hn Hop β).2.1.isSymmetric.eigenvalues hn)).sum := by
          rw [h1]
      _ = ∑ i, F ((gibbsState hn Hop β).2.1.isSymmetric.eigenvalues hn i) := rfl
  have hvN : vonNeumannEntropy hn (gibbsState hn Hop β) = ∑ i, Real.negMulLog (w i) :=
    (hsum_eq Real.negMulLog).symm
  have hEbE : ∀ j, (Hop.1 : H →ₗ[ℂ] H) (bE j) = (E j : ℂ) • bE j :=
    fun j => Hop.2.isSymmetric.apply_eigenvectorBasis hn j
  have hρbE : ∀ j, ((gibbsState hn Hop β).1 : H →ₗ[ℂ] H) (bE j) = (w j : ℂ) • bE j := by
    intro j
    have : ((gibbsState hn Hop β).1 : H →ₗ[ℂ] H) (bE j) =
        ∑ i : Fin n, (w i : ℂ) • InnerProductSpace.rankOne ℂ (bE i) (bE i) (bE j) := by
      simp [hgibbs_eq]
    rw [this, Finset.sum_eq_single j]
    · simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, bE.orthonormal.1 j]
    · intro i _ hij
      simp [InnerProductSpace.rankOne_apply, bE.orthonormal.2 hij]
    · simp
  have henergy : energyExpValue (gibbsState hn Hop β) Hop = ∑ i, w i * E i := by
    show (LinearMap.trace ℂ H
        (((gibbsState hn Hop β).1 ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H)).re = ∑ i, w i * E i
    rw [LinearMap.trace_eq_sum_inner (𝕜 := ℂ) _ bE]
    have hterm : ∀ j : Fin n, inner ℂ (bE j) ((((gibbsState hn Hop β).1 ∘L Hop.1 : H →L[ℂ] H) :
        H →ₗ[ℂ] H) (bE j)) = (w j : ℂ) * (E j : ℂ) := by
      intro j
      show inner ℂ (bE j) (((gibbsState hn Hop β).1 : H →ₗ[ℂ] H) ((Hop.1 : H →ₗ[ℂ] H) (bE j))) =
        (w j : ℂ) * (E j : ℂ)
      rw [hEbE j, map_smul, hρbE j, inner_smul_right, inner_smul_right,
        inner_self_eq_norm_sq_to_K, bE.norm_eq_one]
      push_cast
      ring
    simp_rw [hterm]
    have : (∑ i : Fin n, (w i : ℂ) * (E i : ℂ)) = ((∑ i, w i * E i : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [hvN, henergy]
  have hZpos : 0 < Z := partitionFunction_pos hn Hop β
  have hlogw : ∀ i, Real.log (w i) = -β * E i - Real.log Z := by
    intro i
    show Real.log (Real.exp (-β * E i) / Z) = -β * E i - Real.log Z
    rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hw_sum : ∑ i, w i = 1 := by
    show (∑ i : Fin n, Real.exp (-β * E i) / Z) = 1
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  have hexpand : ∑ i, Real.negMulLog (w i) =
      β * ∑ i, w i * E i + Real.log Z * ∑ i, w i := by
    have : ∀ i, Real.negMulLog (w i) = β * (w i * E i) + Real.log Z * w i := by
      intro i
      rw [Real.negMulLog, hlogw i]
      ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexpand, hw_sum, mul_one]

end QuantumTheory
