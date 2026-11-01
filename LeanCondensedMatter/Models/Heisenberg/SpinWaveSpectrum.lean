import LeanCondensedMatter.Models.Heisenberg
import LeanCondensedMatter.Analysis.Fourier.CyclicLaplacian
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

/-- Exact full-spin one-magnon eigenstates, using the isometric one-magnon embedding. -/
theorem excitationHamiltonian_fourierMode (hN : 2 < N) (J : ℝ) (q : ZMod N) :
    excitationHamiltonian J (oneMagnonEmbedding (ZMod.fourierMode q)) =
      (ZMod.cyclicLaplacianEigenvalue J q : ℂ) • oneMagnonEmbedding (ZMod.fourierMode q) := by
  have h := LinearMap.congr_fun
    (excitationHamiltonian_comp_oneMagnonEmbedding hN J) (ZMod.fourierMode q)
  change excitationHamiltonian J (oneMagnonEmbedding (ZMod.fourierMode q)) =
    oneMagnonEmbedding (ZMod.cyclicLaplacian J (ZMod.fourierMode q)) at h
  rw [ZMod.cyclicLaplacian_fourierMode, map_smul] at h
  exact h

/-- Continuous dispersion expression for lattice spacing `a`; this is not an
infinite-volume construction. Stancil-Prabhakar, equation (2.91). -/
def dispersion (J a k : ℝ) : ℝ := 2 * J * (1 - Real.cos (a * k))

/-- For positive spacing `a`, the nonnegative representative of an allowed periodic wavevector.
The mode label is modulo N; representatives differing by 2 pi/a have the same energy. -/
def wavevector (a : ℝ) (q : ZMod N) : ℝ := 2 * Real.pi * q.val / (N * a)

theorem dispersion_wavevector (J a : ℝ) (ha : a ≠ 0) (q : ZMod N) :
    dispersion J a (wavevector a q) = ZMod.cyclicLaplacianEigenvalue J q := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold dispersion wavevector ZMod.cyclicLaplacianEigenvalue
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
  field_simp [hk0, ha.ne']

end
end Models.Heisenberg
