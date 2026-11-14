import LeanCondensedMatter.Transport.Disorder.TwoParticle
import LeanCondensedMatter.Transport.Disorder.BornNormBound
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Fixed-regulator control of the exact connected two-Green insertion

An exact finite-disorder covariance is not the Born ladder. Nevertheless, at nonzero
independent signed regulators and a uniformly small bounded self-adjoint impurity potential,
the connected insertion is at most **quadratic in the potential norm**.

The bound is uniform in the disorder configurations and Hilbert-space dimension, but **not**
in zero broadening, and does not imply any NCA/SCBA closure, diagrammatic classification,
conductivity normalization, or DC/thermodynamic limit.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- A single exact resolvent differs from the clean resolvent by at most a first-order
impurity contribution, uniformly at a fixed nonzero signed regulator. -/
theorem norm_configurationGreen_sub_free_le
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (ω : Ω)
    (potentialBound : ℝ)
    (hpotential : ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound) :
    ‖ensemble.configurationGreenOfRegulator energy regulator ω -
        ensemble.freeGreenOfRegulator energy regulator‖ ≤
      (|regulator|⁻¹) ^ 2 * potentialBound := by
  let G₀ := ensemble.freeGreenOfRegulator energy regulator
  let Gω := ensemble.configurationGreenOfRegulator energy regulator ω
  let V := (ensemble.impurityPotential ω).1
  let B : ℝ := |regulator|⁻¹
  have hfree : ‖G₀‖ ≤ B :=
    norm_resolvent_spectralParameterOfRegulator_le
      ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energy regulator hregulator
  have hconfig : ‖Gω‖ ≤ B :=
    norm_resolvent_spectralParameterOfRegulator_le
      (ensemble.configurationHamiltonian ω).1
      (ensemble.configurationHamiltonian ω).2 energy regulator hregulator
  have hdyson : Gω - G₀ = G₀ * V * Gω := by
    have h := ensemble.configurationGreenOfRegulator_eq_free_add_dyson_left
      energy regulator hregulator ω
    change Gω = G₀ + G₀ * V * Gω at h
    nth_rw 1 [h]
    abel
  change ‖Gω - G₀‖ ≤ B ^ 2 * potentialBound
  rw [hdyson]
  calc
    ‖G₀ * V * Gω‖ ≤ (‖G₀‖ * ‖V‖) * ‖Gω‖ := by
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le G₀ V) (norm_nonneg Gω))
    _ ≤ (B * potentialBound) * B := by
      have hMnonneg : 0 ≤ potentialBound :=
        (norm_nonneg V).trans hpotential
      have hBnonneg : 0 ≤ B := inv_nonneg.mpr (abs_nonneg regulator)
      have hleft : ‖G₀‖ * ‖V‖ ≤ B * potentialBound := by
        calc
          ‖G₀‖ * ‖V‖ ≤ ‖G₀‖ * potentialBound :=
            mul_le_mul_of_nonneg_left hpotential (norm_nonneg G₀)
          _ ≤ B * potentialBound :=
            mul_le_mul_of_nonneg_right hfree hMnonneg
      calc
        (‖G₀‖ * ‖V‖) * ‖Gω‖ ≤ (B * potentialBound) * ‖Gω‖ :=
          mul_le_mul_of_nonneg_right hleft (norm_nonneg Gω)
        _ ≤ (B * potentialBound) * B :=
          mul_le_mul_of_nonneg_left hconfig (mul_nonneg hBnonneg hMnonneg)
    _ = B ^ 2 * potentialBound := by ring

/-- A finite disorder average is as close to the clean Green operator as each configuration
at a common uniform potential bound. -/
theorem norm_averagedGreen_sub_free_le
    (energy regulator : ℝ) (hregulator : regulator ≠ 0)
    (potentialBound : ℝ) (hbound : 0 ≤ potentialBound)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound) :
    ‖ensemble.averagedGreenOfRegulator energy regulator -
        ensemble.freeGreenOfRegulator energy regulator‖ ≤
      (|regulator|⁻¹) ^ 2 * potentialBound := by
  let G₀ := ensemble.freeGreenOfRegulator energy regulator
  let G : Ω → H →L[ℂ] H :=
    fun ω => ensemble.configurationGreenOfRegulator energy regulator ω
  have hshift :
      ensemble.averagedGreenOfRegulator energy regulator - G₀ =
        ensemble.average (fun ω => G ω - G₀) := by
    calc
      ensemble.averagedGreenOfRegulator energy regulator - G₀ =
          ensemble.average G - ensemble.average (fun _ : Ω => G₀) := by
            rw [ensemble.average_const]
            rfl
      _ = ensemble.average (fun ω => G ω - G₀) := by
        simpa only [Pi.sub_apply] using
          (map_sub ensemble.average G (fun _ : Ω => G₀)).symm
  rw [hshift]
  apply ensemble.norm_average_le_of_forall _ _
  intro ω
  exact ensemble.norm_configurationGreen_sub_free_le
    energy regulator hregulator ω potentialBound (hpotential ω)

/-- The configuration-to-average Green fluctuation is first order in a uniform
impurity bound, without any centering or Gaussian assumption. -/
theorem norm_configurationGreen_sub_averaged_le
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (ω : Ω)
    (potentialBound : ℝ) (hbound : 0 ≤ potentialBound)
    (hpotential : ∀ ξ, ‖(ensemble.impurityPotential ξ).1‖ ≤ potentialBound) :
    ‖ensemble.configurationGreenOfRegulator energy regulator ω -
        ensemble.averagedGreenOfRegulator energy regulator‖ ≤
      2 * (|regulator|⁻¹) ^ 2 * potentialBound := by
  let G₀ := ensemble.freeGreenOfRegulator energy regulator
  let Gω := ensemble.configurationGreenOfRegulator energy regulator ω
  let Gbar := ensemble.averagedGreenOfRegulator energy regulator
  let B : ℝ := |regulator|⁻¹
  have hconfig :
      ‖Gω - G₀‖ ≤ B ^ 2 * potentialBound :=
    ensemble.norm_configurationGreen_sub_free_le
      energy regulator hregulator ω potentialBound (hpotential ω)
  have hmean :
      ‖Gbar - G₀‖ ≤ B ^ 2 * potentialBound :=
    ensemble.norm_averagedGreen_sub_free_le
      energy regulator hregulator potentialBound hbound hpotential
  have hdiff : Gω - Gbar = (Gω - G₀) - (Gbar - G₀) := by abel
  change ‖Gω - Gbar‖ ≤ 2 * B ^ 2 * potentialBound
  rw [hdiff]
  calc
    _ ≤ ‖Gω - G₀‖ + ‖Gbar - G₀‖ := norm_sub_le _ _
    _ ≤ B ^ 2 * potentialBound + B ^ 2 * potentialBound :=
      add_le_add hconfig hmean
    _ = 2 * B ^ 2 * potentialBound := by ring

/-- Exact connected two-Green disorder insertion is quadratically bounded at two
independent nonzero regulators for a uniform operator-norm potential bound.

This is a **nonasymptotic** estimate for exact disorder covariance, *not* an identification
with a noncrossing Born-ladder vertex. No assumption `E[V]=0` is required. -/
theorem norm_connectedTwoGreenInsertion_le_uniformPotential_sq
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (hregLeft : regulatorLeft ≠ 0) (hregRight : regulatorRight ≠ 0)
    (vertex : H →L[ℂ] H)
    (potentialBound : ℝ) (hbound : 0 ≤ potentialBound)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound) :
    ‖ensemble.connectedTwoGreenInsertionOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight vertex‖ ≤
      (2 * (|regulatorLeft|⁻¹) ^ 2 * potentialBound) * ‖vertex‖ *
        (2 * (|regulatorRight|⁻¹) ^ 2 * potentialBound) := by
  let leftBound := 2 * (|regulatorLeft|⁻¹) ^ 2 * potentialBound
  let rightBound := 2 * (|regulatorRight|⁻¹) ^ 2 * potentialBound
  have hleftNonneg : 0 ≤ leftBound := by
    dsimp [leftBound]
    positivity
  let L : Ω → H →L[ℂ] H :=
    fun ω => ensemble.configurationGreenOfRegulator energyLeft regulatorLeft ω -
      ensemble.averagedGreenOfRegulator energyLeft regulatorLeft
  let R : Ω → H →L[ℂ] H :=
    fun ω => ensemble.configurationGreenOfRegulator energyRight regulatorRight ω -
      ensemble.averagedGreenOfRegulator energyRight regulatorRight
  have hpoint (ω : Ω) :
      ‖L ω * vertex * R ω‖ ≤ leftBound * ‖vertex‖ * rightBound := by
    have hleft : ‖L ω‖ ≤ leftBound :=
      ensemble.norm_configurationGreen_sub_averaged_le
        energyLeft regulatorLeft hregLeft ω potentialBound hbound hpotential
    have hright : ‖R ω‖ ≤ rightBound :=
      ensemble.norm_configurationGreen_sub_averaged_le
        energyRight regulatorRight hregRight ω potentialBound hbound hpotential
    calc
      ‖L ω * vertex * R ω‖ ≤ (‖L ω‖ * ‖vertex‖) * ‖R ω‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le (L ω) vertex) (norm_nonneg (R ω)))
      _ ≤ leftBound * ‖vertex‖ * rightBound := by
        have hleftMul : ‖L ω‖ * ‖vertex‖ ≤ leftBound * ‖vertex‖ :=
          mul_le_mul_of_nonneg_right hleft (norm_nonneg vertex)
        calc
          (‖L ω‖ * ‖vertex‖) * ‖R ω‖ ≤
              (leftBound * ‖vertex‖) * ‖R ω‖ :=
            mul_le_mul_of_nonneg_right hleftMul (norm_nonneg (R ω))
          _ ≤ leftBound * ‖vertex‖ * rightBound :=
            mul_le_mul_of_nonneg_left hright
              (mul_nonneg hleftNonneg (norm_nonneg vertex))
  change ‖ensemble.average (fun ω => L ω * vertex * R ω)‖ ≤
    leftBound * ‖vertex‖ * rightBound
  exact ensemble.norm_average_le_of_forall _ _ hpoint

end FiniteDisorderEnsemble

end
end QuantumTheory.Transport
