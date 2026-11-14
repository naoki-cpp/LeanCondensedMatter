import LeanCondensedMatter.Transport.Disorder.TwoParticleNormBound
import LeanCondensedMatter.Transport.Disorder.Moments
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Centered Green fluctuations around the first Dyson scattering term

For centered finite self-adjoint impurity ensembles, the random fluctuation
`Gω - E[G]` is approximated by the first clean Dyson insertion `G₀ Vω G₀`.
At fixed nonzero signed regulator and uniform potential bound `‖Vω‖ ≤ M`, its
operator-norm error is bounded by `2 M² / |γ|³`.

This is exact finite-ensemble perturbation control, with no Gaussian statistics,
noncrossing approximation, or zero-regulator/DC limit.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

private theorem norm_mul_five_le
    (a b c d e : H →L[ℂ] H) :
    ‖a * b * c * d * e‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by
  calc
    _ ≤ ‖a * b * c * d‖ * ‖e‖ := norm_mul_le _ _
    _ ≤ (‖a * b * c‖ * ‖d‖) * ‖e‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ((‖a * b‖ * ‖c‖) * ‖d‖) * ‖e‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ((‖a‖ * ‖b‖) * ‖c‖ * ‖d‖) * ‖e‖ := by
      gcongr
      exact norm_mul_le _ _

/-- The exact centered configuration-wise resolvent fluctuation differs from the
first Dyson insertion `G₀ Vω G₀` by at most `2 |γ|⁻³ M²`. In particular,
this controls a centered random operator, not an averaged Born–Dyson closure. -/
theorem norm_configurationGreen_fluctuation_sub_firstDyson_le
    (energy regulator : ℝ) (hregulator : regulator ≠ 0)
    (hcentered : ensemble.IsCentered) (ω : Ω)
    (potentialBound : ℝ) (hbound : 0 ≤ potentialBound)
    (hpotential : ∀ ξ, ‖(ensemble.impurityPotential ξ).1‖ ≤ potentialBound) :
    ‖(ensemble.configurationGreenOfRegulator energy regulator ω -
        ensemble.averagedGreenOfRegulator energy regulator) -
      ensemble.freeGreenOfRegulator energy regulator *
        (ensemble.impurityPotential ω).1 *
          ensemble.freeGreenOfRegulator energy regulator‖ ≤
      2 * (|regulator|⁻¹) ^ 3 * potentialBound ^ 2 := by
  let G₀ := ensemble.freeGreenOfRegulator energy regulator
  let G : Ω → H →L[ℂ] H :=
    fun ξ => ensemble.configurationGreenOfRegulator energy regulator ξ
  let V : Ω → H →L[ℂ] H :=
    fun ξ => (ensemble.impurityPotential ξ).1
  let A : Ω → H →L[ℂ] H := fun ξ => G₀ * V ξ * G₀
  let R : Ω → H →L[ℂ] H := fun ξ => G₀ * V ξ * G₀ * V ξ * G ξ
  let B : ℝ := |regulator|⁻¹
  have hfree : ‖G₀‖ ≤ B :=
    norm_resolvent_spectralParameterOfRegulator_le
      ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energy regulator hregulator
  have hconfig (ξ : Ω) : ‖G ξ‖ ≤ B :=
    norm_resolvent_spectralParameterOfRegulator_le
      (ensemble.configurationHamiltonian ξ).1
      (ensemble.configurationHamiltonian ξ).2 energy regulator hregulator
  have hR (ξ : Ω) : ‖R ξ‖ ≤ B ^ 3 * potentialBound ^ 2 := by
    calc
      ‖R ξ‖ ≤ ‖G₀‖ * ‖V ξ‖ * ‖G₀‖ * ‖V ξ‖ * ‖G ξ‖ :=
        norm_mul_five_le G₀ (V ξ) G₀ (V ξ) (G ξ)
      _ ≤ B * potentialBound * B * potentialBound * B := by
        gcongr <;> first | exact hfree | exact hpotential ξ | exact hconfig ξ | exact hbound
      _ = B ^ 3 * potentialBound ^ 2 := by ring
  have hpoint (ξ : Ω) : G ξ = G₀ + A ξ + R ξ := by
    have h := ensemble.configurationGreenOfRegulator_eq_secondOrder_add_exactRemainder_left
      energy regulator hregulator ξ
    change G ξ = G₀ + A ξ + R ξ at h
    exact h
  have hAavg : ensemble.average A = 0 := by
    have hfactor :
        ensemble.average A = G₀ * ensemble.average V * G₀ := by
      simpa only [A] using
        (ensemble.map_average
          ((ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H)) G₀ G₀).toLinearMap
          V).symm
    rw [hfactor]
    have hcenter : ensemble.average V = 0 := hcentered
    rw [hcenter]
    simp
  have hGavg :
      ensemble.averagedGreenOfRegulator energy regulator =
        G₀ + ensemble.average R := by
    calc
      ensemble.averagedGreenOfRegulator energy regulator =
          ensemble.average (fun ξ => G₀ + A ξ + R ξ) := by
        apply congrArg ensemble.average
        funext ξ
        exact hpoint ξ
      _ = G₀ + ensemble.average R := by
        change ensemble.average ((fun _ : Ω => G₀) + A + R) = _
        rw [map_add, map_add, ensemble.average_const, hAavg]
        simp
  have hRavg : ‖ensemble.average R‖ ≤ B ^ 3 * potentialBound ^ 2 :=
    ensemble.norm_average_le_of_forall R _ hR
  have hdiff :
      (G ω - ensemble.averagedGreenOfRegulator energy regulator) - A ω =
        R ω - ensemble.average R := by
    rw [hpoint ω, hGavg]
    abel
  change ‖(G ω - ensemble.averagedGreenOfRegulator energy regulator) - A ω‖ ≤
    2 * B ^ 3 * potentialBound ^ 2
  rw [hdiff]
  calc
    ‖R ω - ensemble.average R‖ ≤ ‖R ω‖ + ‖ensemble.average R‖ :=
      norm_sub_le _ _
    _ ≤ B ^ 3 * potentialBound ^ 2 + B ^ 3 * potentialBound ^ 2 :=
      add_le_add (hR ω) hRavg
    _ = 2 * B ^ 3 * potentialBound ^ 2 := by ring

end FiniteDisorderEnsemble

end
end QuantumTheory.Transport
