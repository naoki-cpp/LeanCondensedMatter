import LeanCondensedMatter.QuantumTheory.SpinHalf.Finite
import Mathlib.Data.ZMod.Basic

set_option linter.style.header false

/-!
# The finite spin-1/2 ferromagnetic ring

The ring has uniform nearest-neighbor exchange and no external field. Each bond
is counted once. The convention is `H = -(2J / ℏ²) ∑ Sⱼ · Sⱼ₊₁` and `J > 0`
is ferromagnetic. Source: Stancil-Prabhakar, Section 2.5, equations (2.71)-(2.89).
The full spin Hamiltonian restricts exactly to the one-magnon discrete Laplacian.
-/

namespace Models.Heisenberg

open QuantumTheory.SpinHalf
open scoped BigOperators InnerProductSpace

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The zero-field spin-1/2 ring Hamiltonian in the exchange representation. -/
def hamiltonian (J : ℝ) : QuantumTheory.LocalizedSpin.State 1 (ZMod N) →ₗ[ℂ] QuantumTheory.LocalizedSpin.State 1 (ZMod N) :=
  ∑ i : ZMod N, (J : ℂ) •
    ((1 / 2 : ℂ) • LinearMap.id - (exchange i (i + 1)).toLinearMap)

/-- Energy of the fully polarized reference state, in the bond-once convention. -/
def groundEnergy (N : ℕ) (J : ℝ) : ℝ := -J * N / 2

/-- The exchange Hamiltonian measured relative to the polarized energy. -/
def excitationHamiltonian (J : ℝ) : QuantumTheory.LocalizedSpin.State 1 (ZMod N) →ₗ[ℂ] QuantumTheory.LocalizedSpin.State 1 (ZMod N) :=
  (J : ℂ) • ∑ i : ZMod N, (LinearMap.id - (exchange i (i + 1)).toLinearMap)

theorem hamiltonian_eq_excitation_add_ground (J : ℝ) :
    hamiltonian (N := N) J = excitationHamiltonian J +
      (groundEnergy N J : ℂ) • LinearMap.id := by
  ext ψ c
  simp [hamiltonian, excitationHamiltonian, groundEnergy, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_sub, ZMod.card]
  ring

theorem excitationHamiltonian_isPositive (J : ℝ) (hJ : 0 ≤ J) :
    (excitationHamiltonian (N := N) J).IsPositive := by
  exact (LinearMap.isPositive_sum Finset.univ
    (fun i _ => id_sub_exchange_isPositive i (i + 1))).smul_of_nonneg (by exact_mod_cast hJ)

theorem hamiltonian_isSymmetric (J : ℝ) :
    (hamiltonian (N := N) J).IsSymmetric := by
  apply LinearMap.isSymmetric_sum
  intro i _
  exact ((LinearMap.IsSymmetric.id.smul (by simp [map_ofNat])).sub
    (exchange_isSymmetric i (i + 1))).smul (by simp)

theorem hamiltonian_isSelfAdjoint (J : ℝ) : IsSelfAdjoint (hamiltonian (N := N) J) :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp (hamiltonian_isSymmetric J)

theorem hamiltonian_polarized (J : ℝ) :
    hamiltonian (N := N) J polarized = (groundEnergy N J : ℂ) • polarized := by
  rw [hamiltonian_eq_excitation_add_ground]
  simp [excitationHamiltonian, exchange_polarized]

variable (hN : 2 < N)

include hN in
omit [NeZero N] in
private theorem site_ne_next (i : ZMod N) : i ≠ i + 1 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  exact fun h => one_ne_zero (add_left_cancel (by simpa using h.symm : i + 1 = i + 0))

include hN in
/-- Equality with the dimensionful Heisenberg spin-product Hamiltonian. -/
theorem hamiltonian_eq_spinSum (J hbar : ℝ) (hhbar : hbar ≠ 0) :
    hamiltonian (N := N) J =
      (-2 * (J : ℂ) / (hbar : ℂ) ^ 2) •
        ∑ i : ZMod N, spinDot hbar i (i + 1) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [spinDot_eq_exchange hbar i (i + 1) (site_ne_next hN i)]
  have hh : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar
  ext ψ c
  simp
  field_simp [hh]
  ring

include hN in
/-- Exact action on a single reversed spin; neighboring sites are understood modulo N. -/
theorem excitationHamiltonian_oneMagnonKet (J : ℝ) (k : ZMod N) :
    excitationHamiltonian J (oneMagnonKet k) =
      (J : ℂ) • ((oneMagnonKet k - oneMagnonKet (k + 1)) +
        (oneMagnonKet k - oneMagnonKet (k - 1))) := by
  have hprev : k - 1 ≠ k := by
    intro h
    apply site_ne_next hN k
    calc
      k = (k - 1) + 1 := by abel
      _ = k + 1 := by rw [h]
  have hterm (i : ZMod N) :
      ((LinearMap.id : QuantumTheory.LocalizedSpin.State 1 (ZMod N) →ₗ[ℂ] QuantumTheory.LocalizedSpin.State 1 (ZMod N)) -
        (exchange i (i + 1)).toLinearMap) (oneMagnonKet k) =
        (if i = k then oneMagnonKet k - oneMagnonKet (k + 1) else 0) +
        (if i = k - 1 then oneMagnonKet k - oneMagnonKet (k - 1) else 0) := by
    change oneMagnonKet k - exchange i (i + 1) (oneMagnonKet k) = _
    rw [exchange_oneMagnonKet]
    by_cases hik : i = k
    · subst i
      simp [hprev.symm]
    · by_cases hip : i = k - 1
      · subst i
        simp [sub_add_cancel, hprev]
      · have hki : k ≠ i := Ne.symm hik
        have hkip : k ≠ i + 1 := by
          intro h
          apply hip
          rw [h]
          abel
        simp [Equiv.swap_apply_of_ne_of_ne hki hkip, hik, hip]
  simp only [excitationHamiltonian, LinearMap.smul_apply, LinearMap.sum_apply]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib]

/-- The periodic nearest-neighbor discrete Laplacian acting on magnon amplitudes. -/
def oneMagnonLaplacian (J : ℝ) : EuclideanSpace ℂ (ZMod N) →ₗ[ℂ]
    EuclideanSpace ℂ (ZMod N) where
  toFun ψ := WithLp.toLp 2 fun i => (J : ℂ) * (2 * ψ i - ψ (i - 1) - ψ (i + 1))
  map_add' ψ φ := by ext i; simp; ring
  map_smul' a ψ := by ext i; simp; ring

omit [NeZero N] in
private theorem oneMagnonLaplacian_single (J : ℝ) (k : ZMod N) :
    oneMagnonLaplacian J (EuclideanSpace.single k 1) =
      (J : ℂ) • ((EuclideanSpace.single k 1 - EuclideanSpace.single (k + 1) 1) +
        (EuclideanSpace.single k 1 - EuclideanSpace.single (k - 1) 1)) := by
  ext i
  have hleft : i - 1 = k ↔ i = k + 1 := sub_eq_iff_eq_add
  have hright : i + 1 = k ↔ i = k - 1 := eq_sub_iff_add_eq.symm
  simp [oneMagnonLaplacian, PiLp.single_apply, hleft, hright]
  split_ifs <;> ring

include hN in
/-- The exact one-magnon restriction of the full spin Hamiltonian. The embedding is
isometric, and this identity proves that its range is invariant. -/
theorem excitationHamiltonian_comp_oneMagnonEmbedding (J : ℝ) :
    (excitationHamiltonian (N := N) J).comp oneMagnonEmbedding.toLinearMap =
      oneMagnonEmbedding.toLinearMap.comp (oneMagnonLaplacian J) := by
  apply (EuclideanSpace.basisFun (ZMod N) ℂ).toBasis.ext
  intro k
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    LinearMap.comp_apply, LinearIsometry.coe_toLinearMap]
  have hemb (i : ZMod N) : oneMagnonEmbedding (EuclideanSpace.single i 1) =
      oneMagnonKet i := by
    simp [oneMagnonEmbedding_apply, PiLp.single_apply]
  rw [hemb, excitationHamiltonian_oneMagnonKet hN, oneMagnonLaplacian_single]
  simp only [map_smul, map_add, map_sub, hemb]

end
end Models.Heisenberg
