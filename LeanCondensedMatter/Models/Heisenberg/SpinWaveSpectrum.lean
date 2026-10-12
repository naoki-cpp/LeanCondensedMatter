import LeanCondensedMatter.Models.Heisenberg
import LeanCondensedMatter.Analysis.Fourier.FiniteCyclic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

set_option linter.style.header false

/-!
# Exact finite-ring one-magnon spectrum

The positive-exponent Fourier convention labels modes by `q : ZMod N`.
Energies are measured relative to the polarized energy in the bond-once convention.
Source: Stancil-Prabhakar, Section 2.5, equations (2.90)-(2.94).
The small-wavevector limit concerns the dispersion expression, not a limit of spin states.
-/

namespace Models.Heisenberg

open QuantumTheory.SpinHalf
open scoped BigOperators InnerProductSpace Topology

noncomputable section
variable {N : ℕ} [NeZero N]

/-- Shifted one-magnon energy of the zero-field uniform ring, with each bond counted once.
Stancil-Prabhakar, Section 2.5, equation (2.91). -/
def oneMagnonEnergy (J : ℝ) (q : ZMod N) : ℝ :=
  2 * J * (1 - Real.cos (2 * Real.pi * (q.val / N)))

private theorem phase_sum (q : ZMod N) :
    ZMod.stdAddChar q + ZMod.stdAddChar (-q) =
      (2 * Real.cos (2 * Real.pi * (q.val / N)) : ℝ) := by
  let θ : ℝ := 2 * Real.pi * (q.val / N)
  have he : ZMod.stdAddChar q = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
  rw [← ZMod.stdAddChar_conj, he, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem oneMagnonLaplacian_fourierMode (J : ℝ) (q : ZMod N) :
    oneMagnonLaplacian J (ZMod.fourierMode q) =
      (oneMagnonEnergy J q : ℂ) • ZMod.fourierMode q := by
  ext j
  change (J : ℂ) * (2 * ZMod.fourierMode q j - ZMod.fourierMode q (j - 1) -
    ZMod.fourierMode q (j + 1)) = _
  have hp := phase_sum q
  simp only [ZMod.fourierMode, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
    mul_add, mul_one, sub_eq_add_neg, AddChar.map_add_eq_mul,
    mul_neg]
  simp only [oneMagnonEnergy, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_ofNat, Complex.ofReal_one] at *
  linear_combination -(J : ℂ) * (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (q * j) * hp

/-- The complete normalized Fourier basis consists of eigenvectors of the exact
one-magnon operator. -/
theorem oneMagnonLaplacian_fourierBasis (J : ℝ) (q : ZMod N) :
    oneMagnonLaplacian J (ZMod.fourierBasis q) =
      (oneMagnonEnergy J q : ℂ) • ZMod.fourierBasis q := by
  simpa only [ZMod.fourierBasis_apply] using oneMagnonLaplacian_fourierMode J q

/-- Exact full-spin one-magnon eigenstates, using the isometric embedding from SW1. -/
theorem excitationHamiltonian_fourierMode (hN : 2 < N) (J : ℝ) (q : ZMod N) :
    excitationHamiltonian J (oneMagnonEmbedding (ZMod.fourierMode q)) =
      (oneMagnonEnergy J q : ℂ) • oneMagnonEmbedding (ZMod.fourierMode q) := by
  have h := LinearMap.congr_fun
    (excitationHamiltonian_comp_oneMagnonEmbedding hN J) (ZMod.fourierMode q)
  change excitationHamiltonian J (oneMagnonEmbedding (ZMod.fourierMode q)) =
    oneMagnonEmbedding (oneMagnonLaplacian J (ZMod.fourierMode q)) at h
  rw [oneMagnonLaplacian_fourierMode, map_smul] at h
  exact h

omit [NeZero N] in
theorem oneMagnonEnergy_nonneg (J : ℝ) (hJ : 0 ≤ J) (q : ZMod N) :
    0 ≤ oneMagnonEnergy J q := by
  unfold oneMagnonEnergy
  exact mul_nonneg (mul_nonneg (by norm_num) hJ) (sub_nonneg.mpr (Real.cos_le_one _))

omit [NeZero N] in
theorem oneMagnonEnergy_zero (J : ℝ) : oneMagnonEnergy (N := N) J 0 = 0 := by
  simp [oneMagnonEnergy]

theorem oneMagnonEnergy_pos (J : ℝ) (hJ : 0 < J) (q : ZMod N) (hq : q ≠ 0) :
    0 < oneMagnonEnergy J q := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hqv : (0 : ℝ) < q.val := by
    exact_mod_cast Nat.pos_of_ne_zero ((ZMod.val_eq_zero q).not.mpr hq)
  have hqN : (q.val : ℝ) < N := by exact_mod_cast q.val_lt
  have ht : 0 < 2 * Real.pi * (q.val / N) := by positivity
  have hlt : 2 * Real.pi * (q.val / N) < 2 * Real.pi := by
    have := (div_lt_one hN).mpr hqN
    nlinarith [Real.pi_pos]
  have hc : Real.cos (2 * Real.pi * (q.val / N)) ≠ 1 := by
    intro heq
    exact ht.ne' ((Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [Real.pi_pos]) hlt).mp heq)
  unfold oneMagnonEnergy
  exact mul_pos (mul_pos (by norm_num) hJ)
    (sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one _) hc))

/-- Continuous dispersion expression for lattice spacing `a`; this is not an
infinite-volume construction. Stancil-Prabhakar, equation (2.91). -/
def dispersion (J a k : ℝ) : ℝ := 2 * J * (1 - Real.cos (a * k))

/-- For positive spacing `a`, the nonnegative representative of an allowed periodic wavevector.
The mode label is modulo N; representatives differing by 2 pi/a have the same energy. -/
def wavevector (a : ℝ) (q : ZMod N) : ℝ := 2 * Real.pi * q.val / (N * a)

theorem dispersion_wavevector (J a : ℝ) (ha : a ≠ 0) (q : ZMod N) :
    dispersion J a (wavevector a q) = oneMagnonEnergy J q := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold dispersion wavevector oneMagnonEnergy
  congr 2
  field_simp [hN, ha]

/-- Quadratic small-wavevector behavior through nonzero k, for a positive lattice spacing.
This is a limit of the dispersion expression, not a thermodynamic-limit theorem. -/
theorem tendsto_dispersion_div_sq (J a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun k => dispersion J a k / k ^ 2) (𝓝[≠] 0)
      (𝓝 (J * a ^ 2)) := by
  have hs : Filter.Tendsto (fun k : ℝ => Real.sinc (a * k / 2)) (𝓝[≠] 0) (𝓝 1) := by
    have hi : Filter.Tendsto (fun k : ℝ => a * k / 2) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((tendsto_const_nhds.mul
        (Filter.tendsto_id.mono_left nhdsWithin_le_nhds)).div_const 2 :
        Filter.Tendsto (fun k : ℝ => a * k / 2) (𝓝[≠] 0) (𝓝 (a * 0 / 2)))
    have hc : ContinuousAt Real.sinc 0 := Real.continuous_sinc.continuousAt
    simpa [Function.comp_def] using hc.tendsto.comp hi
  have hlim : Filter.Tendsto (fun k : ℝ => J * (a ^ 2 * Real.sinc (a * k / 2) ^ 2))
      (𝓝[≠] 0) (𝓝 (J * a ^ 2)) := by
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.mul (hs.pow 2)) :
      Filter.Tendsto (fun k : ℝ => J * (a ^ 2 * Real.sinc (a * k / 2) ^ 2))
        (𝓝[≠] 0) (𝓝 (J * (a ^ 2 * 1 ^ 2))))
  apply Filter.Tendsto.congr' _ (by simpa using hlim :
    Filter.Tendsto (fun k : ℝ => J * (a ^ 2 * Real.sinc (a * k / 2) ^ 2))
      (𝓝[≠] 0) (𝓝 (J * a ^ 2)))
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk0 : k ≠ 0 := hk
  have hak : a * k / 2 ≠ 0 := div_ne_zero (mul_ne_zero ha.ne' hk0) (by norm_num)
  rw [Real.sinc_of_ne_zero hak]
  have hc := Real.cos_two_mul (a * k / 2)
  have hsc := Real.sin_sq_add_cos_sq (a * k / 2)
  have harg : 2 * (a * k / 2) = a * k := by ring
  rw [harg] at hc
  have hid : 1 - Real.cos (a * k) = 2 * Real.sin (a * k / 2) ^ 2 := by
    nlinarith
  unfold dispersion
  rw [hid]
  field_simp [hk0, ha.ne'] <;> ring

end
end Models.Heisenberg
