import LeanCondensedMatter.Transport.Resolvent.Spectral
import LeanCondensedMatter.Analysis.Lorentzian.Pole
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Model-independent isolated interband Bastin pole algebra

For an isolated target band, measure probe energy relative to the target pole.  Let

```text
gap = E_target - E_source.
```

The opposite-band source resolvent then has denominator

```text
gap + offset ± i broadening.
```

All model dependence of the regular two-band Hall spectator is carried by `gap` and two ordered
current blocks `forward` and `reverse`.  This module owns the resulting scalar denominator
algebra, fixed-window regularity, Lorentzian pole extraction, and the corresponding `-2 i` Bastin
pole limit.

No band type, Hamiltonian, current operator, Berry curvature, occupation, momentum variable, or
conductivity normalization appears here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open Filter

/-- Retarded-minus-advanced scalar coefficient at a real target energy. -/
noncomputable def scalarSpectralDifferenceCoefficient
    (targetEnergy probeEnergy broadening : ℝ) : ℂ :=
  scalarResolventCoefficient
      (retardedSpectralParameter probeEnergy broadening) targetEnergy -
    scalarResolventCoefficient
      (advancedSpectralParameter probeEnergy broadening) targetEnergy

/-- The scalar retarded-minus-advanced coefficient is exactly the Lorentzian spectral pole. -/
theorem scalarSpectralDifferenceCoefficient_eq_lorentzian
    (targetEnergy probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    scalarSpectralDifferenceCoefficient targetEnergy probeEnergy broadening =
      (-2 * Complex.I) *
        (lorentzianSpectralKernel
          (probeEnergy - targetEnergy) broadening : ℂ) := by
  unfold scalarSpectralDifferenceCoefficient scalarResolventCoefficient
    retardedSpectralParameter advancedSpectralParameter
  rw [spectralParameter_retarded_ofRegulator, spectralParameter_advanced_ofRegulator]
  unfold spectralParameterOfRegulator
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    inv_add_I_sub_inv_sub_I_eq_lorentzian
      (probeEnergy - targetEnergy) broadening hbroadening

/-- Source-band scalar resolvent in coordinates centered at the target-band pole. -/
noncomputable def targetCenteredSourceCoefficient
    (side : SpectralSide) (gap offset broadening : ℝ) : ℂ :=
  scalarResolventCoefficient
    (spectralParameter side offset broadening) (-gap)

/-- Target-centered source denominator in the explicit `gap + offset + iγ` form. -/
theorem targetCenteredSourceCoefficient_eq
    (side : SpectralSide) (gap offset broadening : ℝ) :
    targetCenteredSourceCoefficient side gap offset broadening =
      ((((gap + offset : ℝ) : ℂ) +
        ((side.regulator broadening : ℝ) : ℂ) * Complex.I))⁻¹ := by
  unfold targetCenteredSourceCoefficient scalarResolventCoefficient
    spectralParameter spectralParameterOfRegulator
  congr 1
  push_cast
  ring

/-- If `|offset| ≤ radius`, a real shifted gap stays at least `|gap| - radius` away from zero. -/
theorem abs_gap_sub_radius_le_abs_gap_add_offset
    (gap offset radius : ℝ) (hoffset : |offset| ≤ radius) :
    |gap| - radius ≤ |gap + offset| := by
  have htri : |gap| ≤ |gap + offset| + |offset| := by
    calc
      |gap| = |(gap + offset) + (-offset)| := by
        congr 1
        ring
      _ ≤ |gap + offset| + |-offset| := abs_add_le _ _
      _ = |gap + offset| + |offset| := by rw [abs_neg]
  linarith

/-- A symmetric target-centered window narrower than the interband gap excludes the source pole. -/
theorem gap_add_offset_ne_zero_on_targetWindow
    (gap offset radius : ℝ)
    (hradius : radius < |gap|)
    (hoffset : |offset| ≤ radius) :
    gap + offset ≠ 0 := by
  have hlower := abs_gap_sub_radius_le_abs_gap_add_offset
    gap offset radius hoffset
  have hshiftAbs : 0 < |gap + offset| := by
    have hpositive : 0 < |gap| - radius := sub_pos.mpr hradius
    exact lt_of_lt_of_le hpositive hlower
  exact abs_pos.mp hshiftAbs

/-- Regular opposite-source interband current factor in target-centered coordinates. -/
noncomputable def interbandPoleRegularFactor
    (gap : ℝ) (forward reverse : ℂ) (offsetBroadening : ℝ × ℝ) : ℂ :=
  let r := targetCenteredSourceCoefficient
    .retarded gap offsetBroadening.1 offsetBroadening.2
  let a := targetCenteredSourceCoefficient
    .advanced gap offsetBroadening.1 offsetBroadening.2
  r ^ 2 * forward - a ^ 2 * reverse

/-- At the target pole the regular factor is the inverse-gap-squared antisymmetric current block. -/
theorem interbandPoleRegularFactor_zero
    (gap : ℝ) (forward reverse : ℂ) :
    interbandPoleRegularFactor gap forward reverse (0, 0) =
      ((((gap : ℂ)⁻¹) ^ 2) * (forward - reverse)) := by
  unfold interbandPoleRegularFactor targetCenteredSourceCoefficient
    scalarResolventCoefficient spectralParameter spectralParameterOfRegulator
  simp [SpectralSide.regulator, mul_sub]

/-- The regular interband factor is jointly continuous wherever the shifted real source denominator
does not vanish. -/
theorem continuousAt_interbandPoleRegularFactor_of_gap_add_offset_ne_zero
    (gap : ℝ) (forward reverse : ℂ) (p : ℝ × ℝ)
    (hshift : gap + p.1 ≠ 0) :
    ContinuousAt (interbandPoleRegularFactor gap forward reverse) p := by
  have hside : ∀ side : SpectralSide, ContinuousAt
      (fun q : ℝ × ℝ =>
        targetCenteredSourceCoefficient side gap q.1 q.2) p := by
    intro side
    have hparameter : ContinuousAt
        (fun q : ℝ × ℝ => spectralParameter side q.1 q.2) p := by
      unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
      fun_prop
    have hden :
        spectralParameter side p.1 p.2 - ((-gap : ℝ) : ℂ) ≠ 0 := by
      intro hzero
      have hre : gap + p.1 = 0 := by
        simpa [spectralParameter, spectralParameterOfRegulator] using
          congrArg Complex.re hzero
      exact hshift hre
    change ContinuousAt
      (fun q : ℝ × ℝ =>
        (spectralParameter side q.1 q.2 - ((-gap : ℝ) : ℂ))⁻¹) p
    exact (hparameter.sub continuousAt_const).inv₀ hden
  have hret := hside .retarded
  have hadv := hside .advanced
  unfold interbandPoleRegularFactor
  exact ((hret.mul hret).mul continuousAt_const).sub
    ((hadv.mul hadv).mul continuousAt_const)

/-- Lorentzian-weighted fixed-window integral of the regular interband factor. -/
noncomputable def interbandPoleRegularFactorIntegral
    (gap : ℝ) (forward reverse : ℂ) (radius broadening : ℝ) : ℂ :=
  lorentzianRegularFactorIntegral
    (interbandPoleRegularFactor gap forward reverse) radius broadening

/-- On a positive fixed window narrower than `|gap|`, the regular interband factor is extracted at
the target pole by the Lorentzian approximate identity. -/
theorem tendsto_interbandPoleRegularFactorIntegral
    (gap : ℝ) (forward reverse : ℂ) (radius : ℝ)
    (hradiusPos : 0 < radius)
    (hradius : radius < |gap|) :
    Tendsto
      (fun broadening : ℝ =>
        interbandPoleRegularFactorIntegral
          gap forward reverse radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (Real.pi • interbandPoleRegularFactor gap forward reverse (0, 0))) := by
  let factor : ℝ × ℝ → ℂ := interbandPoleRegularFactor gap forward reverse
  have hgap : gap ≠ 0 := by
    exact abs_pos.mp (lt_trans hradiusPos hradius)
  have hcontinuous : ContinuousAt factor (0, 0) := by
    simpa [factor] using
      continuousAt_interbandPoleRegularFactor_of_gap_add_offset_ne_zero
        gap forward reverse (0, 0) (by simpa using hgap)
  have hslice : ∀ broadening : ℝ, broadening ≠ 0 →
      ContinuousOn (fun offset : ℝ => factor (offset, broadening))
        (Set.Icc (-radius) radius) := by
    intro broadening _ offset hoffset
    have hshift : gap + offset ≠ 0 :=
      gap_add_offset_ne_zero_on_targetWindow
        gap offset radius hradius (abs_le.mpr hoffset)
    have hfactor :=
      continuousAt_interbandPoleRegularFactor_of_gap_add_offset_ne_zero
        gap forward reverse (offset, broadening) hshift
    have hpair : ContinuousAt (fun x : ℝ => (x, broadening)) offset := by
      fun_prop
    have hcomp : ContinuousAt
        (fun x : ℝ => factor (x, broadening)) offset := by
      change Filter.Tendsto
        (fun x : ℝ => interbandPoleRegularFactor
          gap forward reverse (x, broadening))
        (Filter.nhds offset)
        (Filter.nhds
          (interbandPoleRegularFactor gap forward reverse (offset, broadening)))
      exact Filter.Tendsto.comp hfactor hpair
    exact hcomp.continuousWithinAt
  have hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1,
        ‖factor p - factor (0, 0)‖ ≤ C := by
    have hcompact : IsCompact
        (Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    have hfactorContinuous : ContinuousOn factor
        (Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro p hp
      have hshift : gap + p.1 ≠ 0 :=
        gap_add_offset_ne_zero_on_targetWindow
          gap p.1 radius hradius (abs_le.mpr hp.1)
      exact
        (continuousAt_interbandPoleRegularFactor_of_gap_add_offset_ne_zero
          gap forward reverse p hshift).continuousWithinAt
    have hconstant : ContinuousOn (fun _ : ℝ × ℝ => factor (0, 0))
        (Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1) :=
      continuousOn_const
    rcases hcompact.exists_bound_of_continuousOn
      (hfactorContinuous.sub hconstant) with ⟨C, hC⟩
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro p hp
    exact le_trans (hC p hp) (le_max_left _ _)
  have hgeneric := tendsto_lorentzianRegularFactorIntegral
    factor radius hradiusPos hcontinuous hslice hbound
  simpa [factor, interbandPoleRegularFactorIntegral] using hgeneric

/-- Canonical isolated interband Bastin pole integral after exact factorization of the target-band
retarded-minus-advanced coefficient. -/
noncomputable def interbandBastinPoleIntegral
    (gap : ℝ) (forward reverse : ℂ) (radius broadening : ℝ) : ℂ :=
  (-2 * Complex.I) *
    interbandPoleRegularFactorIntegral gap forward reverse radius broadening

/-- The isolated interband Bastin pole converges to `-2 i π` times its regular target-pole factor. -/
theorem tendsto_interbandBastinPoleIntegral
    (gap : ℝ) (forward reverse : ℂ) (radius : ℝ)
    (hradiusPos : 0 < radius)
    (hradius : radius < |gap|) :
    Tendsto
      (fun broadening : ℝ =>
        interbandBastinPoleIntegral gap forward reverse radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((-2 * Complex.I) *
          (Real.pi • interbandPoleRegularFactor gap forward reverse (0, 0)))) := by
  have hpole :=
    tendsto_interbandPoleRegularFactorIntegral
      gap forward reverse radius hradiusPos hradius
  exact (tendsto_const_nhds.mul hpole)

/-- The real part of the isolated Bastin pole limit is `2π` times the imaginary part of the
regular target-pole factor. -/
theorem tendsto_interbandBastinPoleIntegral_re
    (gap : ℝ) (forward reverse : ℂ) (radius : ℝ)
    (hradiusPos : 0 < radius)
    (hradius : radius < |gap|) :
    Tendsto
      (fun broadening : ℝ =>
        (interbandBastinPoleIntegral gap forward reverse radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (2 * Real.pi *
          (interbandPoleRegularFactor gap forward reverse (0, 0)).im)) := by
  have h :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_interbandBastinPoleIntegral
        gap forward reverse radius hradiusPos hradius)
  have hlimit :
      (((-2 * Complex.I) *
        (Real.pi • interbandPoleRegularFactor gap forward reverse (0, 0))).re) =
        2 * Real.pi *
          (interbandPoleRegularFactor gap forward reverse (0, 0)).im := by
    rw [Complex.mul_re]
    simp
    ring
  rw [hlimit] at h
  exact h

end
end Transport
end QuantumTheory
