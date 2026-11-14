import LeanCondensedMatter.Models.OrbitalRelaxation.SphereMoments
import LeanCondensedMatter.Models.OrbitalRelaxation.OctahedralScattering
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.header false

/-!
# Continuous polar-angle scattering integrals

For a fixed incoming north-pole direction, a rotation-invariant differential
scattering rate has the form `W(cos θ)`. The normalized spherical-coordinate
measure reduces to `dμ / 2`, where `μ = cos θ ∈ [-1, 1]`.
We prove this change of variables against the already formalized 2D sphere
average and then derive the Legendre-weighted polar collision rates.

These theorems address the *zonal integral at a reference direction*. They
do not establish the all-directions Funk–Hecke eigenfunction theorem or an
SO(3)-equivariant scattering operator, nor do they derive a microscopic
second-order kinetic closure.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

open MeasureTheory
open scoped Interval

/-- Normalized polar-angle integral after `μ = cos θ`. -/
noncomputable def polarCosineAverage (f : ℝ → ℝ) : ℝ :=
  (∫ μ in (-1 : ℝ)..1, f μ) / 2

/-- The polar-angle reduction is genuinely the existing normalized continuous
spherical-coordinate average, for continuous functions of `k_z`. -/
theorem sphericalAverage_zonal (f : ℝ → ℝ) (hf : Continuous f) :
    sphericalAverage 1 (fun k => f (k 2)) = polarCosineAverage f := by
  unfold sphericalAverage polarCosineAverage
  have hφ (θ : ℝ) :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
        f ((sphericalMomentum 1 θ φ) 2)) =
        (2 * Real.pi) * f (Real.cos θ) := by
    simp [sphericalMomentum, intervalIntegral.integral_const]
  simp_rw [hφ]
  have hpoint (θ : ℝ) :
      ((2 * Real.pi) * f (Real.cos θ)) * Real.sin θ =
        (-2 * Real.pi) * (f (Real.cos θ) * (-Real.sin θ)) := by ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  have hsubst :
      (∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ) * (-Real.sin θ)) =
        ∫ μ in (1 : ℝ)..(-1), f μ := by
    have hs := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := Real.pi)
      (f := Real.cos) (f' := fun θ => -Real.sin θ) (g := f)
      (fun θ _ => Real.hasDerivAt_cos θ)
      (Real.continuous_sin.neg.continuousOn) hf
    simpa only [Function.comp_apply, Real.cos_zero, Real.cos_pi] using hs
  rw [hsubst, intervalIntegral.integral_symm]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring

private theorem polarCosineAverage_const (c : ℝ) :
    polarCosineAverage (fun _ => c) = c := by
  unfold polarCosineAverage
  rw [intervalIntegral.integral_const]
  ring

private theorem polarCosineAverage_const_mul (c : ℝ) (f : ℝ → ℝ) :
    polarCosineAverage (fun μ => c * f μ) = c * polarCosineAverage f := by
  unfold polarCosineAverage
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem polarCosineAverage_neg (f : ℝ → ℝ) :
    polarCosineAverage (fun μ => -f μ) = -polarCosineAverage f := by
  unfold polarCosineAverage
  rw [intervalIntegral.integral_neg]
  ring

private theorem polarCosineAverage_add (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    polarCosineAverage (fun μ => f μ + g μ) =
      polarCosineAverage f + polarCosineAverage g := by
  unfold polarCosineAverage
  rw [intervalIntegral.integral_add
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

private theorem polarCosineAverage_sub (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    polarCosineAverage (fun μ => f μ - g μ) =
      polarCosineAverage f - polarCosineAverage g := by
  unfold polarCosineAverage
  rw [intervalIntegral.integral_sub
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

private theorem polarCosineAverage_sq :
    polarCosineAverage (fun μ => μ ^ 2) = 1 / 3 := by
  unfold polarCosineAverage
  rw [integral_pow]
  norm_num

private theorem polarCosineAverage_four :
    polarCosineAverage (fun μ => μ ^ 4) = 1 / 5 := by
  unfold polarCosineAverage
  rw [integral_pow]
  norm_num

/-- Legendre-weighted continuous degree-two loss rate at the north pole.
The integral is normalized by `1/(4π)` in the original sphere chart. -/
noncomputable def continuousDegreeTwoRate (W : ℝ → ℝ) : ℝ :=
  polarCosineAverage (fun μ => W μ * (1 - legendreP2 μ))

/-- Continuous degree-one (transport) rate at the same reference pole. -/
noncomputable def continuousMomentumRate (W : ℝ → ℝ) : ℝ :=
  polarCosineAverage (fun μ => W μ * (1 - μ))

/-- Gain-minus-loss operator on zonal observables evaluated at the reference
incoming direction `+e_z`. This is not yet an operator on *all* incoming
directions. -/
noncomputable def continuousZonalCollisionAtNorth (W f : ℝ → ℝ) : ℝ :=
  polarCosineAverage (fun μ => W μ * (f μ - f 1))

/-- At the reference pole, the degree-two Legendre profile loses amplitude
with the explicitly integrated degree-two rate, for any kernel `W`. -/
theorem continuousZonalCollisionAtNorth_P2 (W : ℝ → ℝ) :
    continuousZonalCollisionAtNorth W legendreP2 =
      -continuousDegreeTwoRate W := by
  unfold continuousZonalCollisionAtNorth continuousDegreeTwoRate
  have hp : legendreP2 1 = 1 := by norm_num [legendreP2]
  rw [hp]
  have hpoint (μ : ℝ) :
      W μ * (legendreP2 μ - 1) =
        -(W μ * (1 - legendreP2 μ)) := by ring
  simp_rw [hpoint]
  exact polarCosineAverage_neg _

/-- The same degree-two loss rate is a genuine continuous spherical-coordinate
integral, rather than the six-direction cubature. -/
theorem continuousDegreeTwoRate_eq_sphericalAverage (W : ℝ → ℝ)
    (hW : Continuous W) :
    continuousDegreeTwoRate W =
      sphericalAverage 1 (fun q => W (q 2) * (1 - legendreP2 (q 2))) := by
  unfold continuousDegreeTwoRate
  symm
  apply sphericalAverage_zonal
  have hp : Continuous legendreP2 := by
    unfold legendreP2
    fun_prop
  exact hW.mul (continuous_const.sub hp)

/-- A nonconstant, nonnegative-on-the-sphere zonal scattering kernel for
`a,c ≥ 0`, including the nontrivial forward/backward anisotropy `c μ²`. -/
def quadraticZonalKernel (a c μ : ℝ) : ℝ := a + c * μ ^ 2

theorem quadraticZonalKernel_nonneg (a c μ : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    0 ≤ quadraticZonalKernel a c μ := by
  unfold quadraticZonalKernel
  positivity

/-- Exact Legendre `l=2` rate for a nonconstant continuous scattering
cross-section `W(μ)=a+cμ²`. -/
theorem quadraticZonal_degreeTwoRate (a c : ℝ) :
    continuousDegreeTwoRate (quadraticZonalKernel a c) = a + c / 5 := by
  have hp (μ : ℝ) :
      quadraticZonalKernel a c μ * (1 - legendreP2 μ) =
        (3 * a / 2) + (3 * (c - a) / 2) * μ ^ 2 -
          (3 * c / 2) * μ ^ 4 := by
    unfold quadraticZonalKernel legendreP2
    ring
  unfold continuousDegreeTwoRate
  simp_rw [hp]
  rw [polarCosineAverage_sub _ _ (by fun_prop) (by fun_prop)]
  rw [polarCosineAverage_add _ _ (by fun_prop) (by fun_prop)]
  rw [polarCosineAverage_const_mul, polarCosineAverage_const_mul,
    polarCosineAverage_const, polarCosineAverage_sq, polarCosineAverage_four]
  ring

theorem quadraticZonal_degreeTwoRate_pos (a c : ℝ)
    (ha : 0 < a) (hc : 0 ≤ c) :
    0 < continuousDegreeTwoRate (quadraticZonalKernel a c) := by
  rw [quadraticZonal_degreeTwoRate]
  positivity

end QuantumTheory.Models.OrbitalRelaxation
