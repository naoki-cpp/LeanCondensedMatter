import LeanCondensedMatter.Transport.Disorder.LinearizedFluctuation
import LeanCondensedMatter.Transport.Disorder.Ladder
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Controlled first Born rung in exact finite-disorder two-Green covariance

For a *centered* normalized finite impurity ensemble with `‖Vω‖ ≤ M`, the leading
connected two-Green insertion at independent nonzero signed regulators is precisely

```text
G₀ᴸ · C₂(G₀ᴸ J G₀ᴿ) · G₀ᴿ.
```

The difference between the **exact** connected insertion and this single second-moment
rung is bounded by a quantity cubic in `M`, with explicit regulator dependence.
This controls **one rung**, not an iterated/resummed noncrossing ladder, nor a DC,
continuum-disorder, momentum-integrated, or conductivity approximation.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Canonical first covariance rung, using exactly the same finite second-moment
operator `C₂` as the Born self-energy and RA ladder. -/
noncomputable def firstBornTwoGreenRungOfRegulators
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (vertex : H →L[ℂ] H) : H →L[ℂ] H :=
  let left := ensemble.freeGreenOfRegulator energyLeft regulatorLeft
  let right := ensemble.freeGreenOfRegulator energyRight regulatorRight
  left * ensemble.exactSecondMoment (left * vertex * right) * right

/-- The first covariance rung is the exact average of two first-order Dyson insertions.
The order of all noncommuting operators is preserved. -/
theorem firstBornTwoGreenRungOfRegulators_eq_average_firstDyson
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (vertex : H →L[ℂ] H) :
    ensemble.firstBornTwoGreenRungOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight vertex =
      ensemble.average (fun ω =>
        (ensemble.freeGreenOfRegulator energyLeft regulatorLeft *
            (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energyLeft regulatorLeft) *
          vertex *
          (ensemble.freeGreenOfRegulator energyRight regulatorRight *
            (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energyRight regulatorRight)) := by
  let freeLeft := ensemble.freeGreenOfRegulator energyLeft regulatorLeft
  let freeRight := ensemble.freeGreenOfRegulator energyRight regulatorRight
  let V : Ω → H →L[ℂ] H := fun ω => (ensemble.impurityPotential ω).1
  let term : Ω → H →L[ℂ] H :=
    fun ω => V ω * (freeLeft * vertex * freeRight) * V ω
  have hfactor :
      freeLeft * ensemble.average term * freeRight =
        ensemble.average (fun ω => freeLeft * term ω * freeRight) := by
    simpa using (ensemble.map_average
      ((ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H)) freeLeft freeRight).toLinearMap term)
  have hterm :
      ensemble.exactSecondMoment (freeLeft * vertex * freeRight) = ensemble.average term := by
    exact ensemble.exactSecondMoment_eq_average (freeLeft * vertex * freeRight)
  calc
    ensemble.firstBornTwoGreenRungOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight vertex =
        freeLeft * ensemble.exactSecondMoment (freeLeft * vertex * freeRight) * freeRight := rfl
    _ = freeLeft * ensemble.average term * freeRight := by rw [hterm]
    _ = ensemble.average (fun ω => freeLeft * term ω * freeRight) := hfactor
    _ = ensemble.average (fun ω =>
        (freeLeft * V ω * freeLeft) * vertex * (freeRight * V ω * freeRight)) := by
      apply congrArg ensemble.average
      funext ω
      dsimp only [term]
      noncomm_ring

private theorem norm_mul_three_le
    (a b c : H →L[ℂ] H) :
    ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  calc
    _ ≤ ‖a * b‖ * ‖c‖ := norm_mul_le _ _
    _ ≤ (‖a‖ * ‖b‖) * ‖c‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

/-- Exact connected two-Green insertion differs from the first Born covariance rung
by at most a *cubic* expression in a uniform impurity-norm bound. The bound is
independent of the Hilbert-space dimension and requires no Gaussian moments.

Write `Bᴸ = |γᴸ|⁻¹` and `Bᴿ = |γᴿ|⁻¹`. The right-hand side equals
`(4 (Bᴸ)^3 (Bᴿ)^2 + 2 (Bᴸ)^2 (Bᴿ)^3) M³ ‖J‖`.
No statement about higher ladder rungs, SCBA, or vanishing broadening follows. -/
theorem norm_connectedTwoGreen_sub_firstBornRung_le_cubic
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (hregLeft : regulatorLeft ≠ 0) (hregRight : regulatorRight ≠ 0)
    (hcentered : ensemble.IsCentered)
    (vertex : H →L[ℂ] H)
    (potentialBound : ℝ) (hbound : 0 ≤ potentialBound)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound) :
    ‖ensemble.connectedTwoGreenInsertionOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight vertex -
      ensemble.firstBornTwoGreenRungOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight vertex‖ ≤
      (2 * (|regulatorLeft|⁻¹) ^ 3 * potentialBound ^ 2) *
          ‖vertex‖ * (2 * (|regulatorRight|⁻¹) ^ 2 * potentialBound) +
      ((|regulatorLeft|⁻¹) ^ 2 * potentialBound) * ‖vertex‖ *
          (2 * (|regulatorRight|⁻¹) ^ 3 * potentialBound ^ 2) := by
  let BL : ℝ := |regulatorLeft|⁻¹
  let BR : ℝ := |regulatorRight|⁻¹
  let freeLeft := ensemble.freeGreenOfRegulator energyLeft regulatorLeft
  let freeRight := ensemble.freeGreenOfRegulator energyRight regulatorRight
  let V : Ω → H →L[ℂ] H := fun ω => (ensemble.impurityPotential ω).1
  let L : Ω → H →L[ℂ] H :=
    fun ω => ensemble.configurationGreenOfRegulator energyLeft regulatorLeft ω -
      ensemble.averagedGreenOfRegulator energyLeft regulatorLeft
  let R : Ω → H →L[ℂ] H :=
    fun ω => ensemble.configurationGreenOfRegulator energyRight regulatorRight ω -
      ensemble.averagedGreenOfRegulator energyRight regulatorRight
  let AL : Ω → H →L[ℂ] H := fun ω => freeLeft * V ω * freeLeft
  let AR : Ω → H →L[ℂ] H := fun ω => freeRight * V ω * freeRight
  let EL : ℝ := 2 * BL ^ 3 * potentialBound ^ 2
  let ER : ℝ := 2 * BR ^ 3 * potentialBound ^ 2
  let CL : ℝ := BL ^ 2 * potentialBound
  let CR : ℝ := 2 * BR ^ 2 * potentialBound
  have hEL : 0 ≤ EL := by dsimp [EL]; positivity
  have hCL : 0 ≤ CL := by dsimp [CL]; positivity
  have hLerr (ω : Ω) : ‖L ω - AL ω‖ ≤ EL :=
    ensemble.norm_configurationGreen_fluctuation_sub_firstDyson_le
      energyLeft regulatorLeft hregLeft hcentered ω potentialBound hbound hpotential
  have hRerr (ω : Ω) : ‖R ω - AR ω‖ ≤ ER :=
    ensemble.norm_configurationGreen_fluctuation_sub_firstDyson_le
      energyRight regulatorRight hregRight hcentered ω potentialBound hbound hpotential
  have hRfluct (ω : Ω) : ‖R ω‖ ≤ CR :=
    ensemble.norm_configurationGreen_sub_averaged_le
      energyRight regulatorRight hregRight ω potentialBound hpotential
  have hAL (ω : Ω) : ‖AL ω‖ ≤ CL := by
    have hfree : ‖freeLeft‖ ≤ BL :=
      norm_resolvent_spectralParameterOfRegulator_le
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
        energyLeft regulatorLeft hregLeft
    calc
      ‖AL ω‖ ≤ ‖freeLeft‖ * ‖V ω‖ * ‖freeLeft‖ :=
        norm_mul_three_le freeLeft (V ω) freeLeft
      _ ≤ BL * potentialBound * BL := by
        gcongr
        exact hpotential ω
      _ = CL := by dsimp [CL]; ring
  have hpointEq (ω : Ω) :
      L ω * vertex * R ω - AL ω * vertex * AR ω =
        (L ω - AL ω) * vertex * R ω +
          AL ω * vertex * (R ω - AR ω) := by
    noncomm_ring
  have hpoint (ω : Ω) :
      ‖L ω * vertex * R ω - AL ω * vertex * AR ω‖ ≤
        EL * ‖vertex‖ * CR + CL * ‖vertex‖ * ER := by
    rw [hpointEq]
    have hfirst :
        ‖(L ω - AL ω) * vertex * R ω‖ ≤ EL * ‖vertex‖ * CR := by
      calc
        _ ≤ ‖L ω - AL ω‖ * ‖vertex‖ * ‖R ω‖ :=
          norm_mul_three_le _ _ _
        _ ≤ EL * ‖vertex‖ * CR := by
          have hmul :
              ‖L ω - AL ω‖ * ‖vertex‖ ≤ EL * ‖vertex‖ :=
            mul_le_mul_of_nonneg_right (hLerr ω) (norm_nonneg vertex)
          calc
            _ ≤ (EL * ‖vertex‖) * ‖R ω‖ :=
              mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
            _ ≤ (EL * ‖vertex‖) * CR :=
              mul_le_mul_of_nonneg_left (hRfluct ω)
                (mul_nonneg hEL (norm_nonneg vertex))
    have hsecond :
        ‖AL ω * vertex * (R ω - AR ω)‖ ≤ CL * ‖vertex‖ * ER := by
      calc
        _ ≤ ‖AL ω‖ * ‖vertex‖ * ‖R ω - AR ω‖ :=
          norm_mul_three_le _ _ _
        _ ≤ CL * ‖vertex‖ * ER := by
          have hmul :
              ‖AL ω‖ * ‖vertex‖ ≤ CL * ‖vertex‖ :=
            mul_le_mul_of_nonneg_right (hAL ω) (norm_nonneg vertex)
          calc
            _ ≤ (CL * ‖vertex‖) * ‖R ω - AR ω‖ :=
              mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
            _ ≤ (CL * ‖vertex‖) * ER :=
              mul_le_mul_of_nonneg_left (hRerr ω)
                (mul_nonneg hCL (norm_nonneg vertex))
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  have hfirstRung :
      ensemble.firstBornTwoGreenRungOfRegulators
          energyLeft regulatorLeft energyRight regulatorRight vertex =
        ensemble.average (fun ω => AL ω * vertex * AR ω) := by
    simpa only [AL, AR, V, freeLeft, freeRight] using
      (ensemble.firstBornTwoGreenRungOfRegulators_eq_average_firstDyson
        energyLeft regulatorLeft energyRight regulatorRight vertex)
  change ‖ensemble.average (fun ω => L ω * vertex * R ω) -
      ensemble.firstBornTwoGreenRungOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight vertex‖ ≤
    EL * ‖vertex‖ * CR + CL * ‖vertex‖ * ER
  rw [hfirstRung]
  have hsub :
      ensemble.average (fun ω => L ω * vertex * R ω) -
        ensemble.average (fun ω => AL ω * vertex * AR ω) =
      ensemble.average (fun ω =>
        L ω * vertex * R ω - AL ω * vertex * AR ω) := by
    have hfam :
        ((fun ω => L ω * vertex * R ω) -
          (fun ω => AL ω * vertex * AR ω)) =
        (fun ω => L ω * vertex * R ω - AL ω * vertex * AR ω) := by
      funext ω
      rfl
    exact (map_sub ensemble.average _ _).symm.trans
      (congrArg ensemble.average hfam)
  rw [hsub]
  exact ensemble.norm_average_le_of_forall _ _ hpoint

end FiniteDisorderEnsemble

end
end QuantumTheory.Transport
