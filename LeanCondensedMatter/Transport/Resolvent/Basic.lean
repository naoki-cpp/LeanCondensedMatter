import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent

set_option linter.style.header false

/-!
# Dimension-independent retarded and advanced resolvents

For a bounded self-adjoint Hamiltonian `H`, write the complex spectral parameter as

```text
z(E, γ) = E + iγ.
```

A positive signed regulator is retarded and a negative one is advanced. The `SpectralSide` API
packages these two physical branches through `side.regulator η`, while the underlying algebraic
results are stated for any nonzero signed regulator.

Because the spectrum of a self-adjoint bounded operator is real, every spectral parameter with
nonzero imaginary part lies in the resolvent set. This module defines the signed and side-indexed
spectral parameters and resolvents, and proves their basic opposite-side, adjoint, inverse, and
resolvent identities without a finite-dimensional assumption.

Trace, trace-class, finite-volume, thermodynamic-limit, disorder, and conductivity statements are
outside this module.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Retarded/advanced choice for a complex spectral parameter. -/
inductive SpectralSide
  | retarded
  | advanced
  deriving DecidableEq

namespace SpectralSide

/-- Sign distinguishing the retarded (`+1`) and advanced (`-1`) spectral sides. -/
def sign : SpectralSide → ℝ
  | .retarded => 1
  | .advanced => -1

@[simp] theorem sign_retarded : sign .retarded = 1 := rfl
@[simp] theorem sign_advanced : sign .advanced = -1 := rfl

theorem sign_ne_zero (side : SpectralSide) : side.sign ≠ 0 := by
  cases side <;> simp [sign]

/-- Signed analytic regulator selected by a physical spectral side and real broadening parameter.
This is the canonical physical-to-analytic boundary for retarded/advanced APIs; physical consumers
impose positivity of the broadening where required. -/
def regulator (side : SpectralSide) (broadening : ℝ) : ℝ :=
  side.sign * broadening

@[simp] theorem regulator_retarded (broadening : ℝ) :
    SpectralSide.retarded.regulator broadening = broadening := by
  simp [regulator]

@[simp] theorem regulator_advanced (broadening : ℝ) :
    SpectralSide.advanced.regulator broadening = -broadening := by
  simp [regulator]

theorem regulator_ne_zero (side : SpectralSide) {broadening : ℝ}
    (hbroadening : broadening ≠ 0) : side.regulator broadening ≠ 0 := by
  exact mul_ne_zero (sign_ne_zero side) hbroadening

/-- The opposite physical boundary-value side. -/
def opposite : SpectralSide → SpectralSide
  | .retarded => .advanced
  | .advanced => .retarded

@[simp]
theorem opposite_opposite (side : SpectralSide) : side.opposite.opposite = side := by
  cases side <;> rfl

@[simp]
theorem sign_opposite (side : SpectralSide) : side.opposite.sign = -side.sign := by
  cases side <;> simp [opposite, sign]

@[simp]
theorem regulator_opposite (side : SpectralSide) (broadening : ℝ) :
    side.opposite.regulator broadening = -side.regulator broadening := by
  simp [regulator]

end SpectralSide

/-- Spectral parameter `E + iγ` with an arbitrary signed imaginary regulator `γ`. -/
def spectralParameterOfRegulator (energy regulator : ℝ) : ℂ :=
  (energy : ℂ) + (regulator : ℂ) * Complex.I

@[simp]
theorem spectralParameterOfRegulator_re (energy regulator : ℝ) :
    (spectralParameterOfRegulator energy regulator).re = energy := by
  simp [spectralParameterOfRegulator]

@[simp]
theorem spectralParameterOfRegulator_im (energy regulator : ℝ) :
    (spectralParameterOfRegulator energy regulator).im = regulator := by
  simp [spectralParameterOfRegulator]

/-- Complex conjugation reverses the signed imaginary regulator. -/
@[simp]
theorem star_spectralParameterOfRegulator (energy regulator : ℝ) :
    star (spectralParameterOfRegulator energy regulator) =
      spectralParameterOfRegulator energy (-regulator) := by
  apply Complex.ext <;>
    simp [spectralParameterOfRegulator]

/-- A nonzero signed regulator keeps the spectral parameter away from every real energy. -/
theorem spectralParameterOfRegulator_sub_real_ne_zero
    (energy regulator eigenvalue : ℝ) (hregulator : regulator ≠ 0) :
    spectralParameterOfRegulator energy regulator - (eigenvalue : ℂ) ≠ 0 := by
  intro hzero
  have him : regulator = 0 := by
    simpa [spectralParameterOfRegulator] using congrArg Complex.im hzero
  exact hregulator him

/-- Side-indexed spectral parameter `E + iγˢ`, where `γˢ = side.regulator η`. -/
def spectralParameter (side : SpectralSide) (energy broadening : ℝ) : ℂ :=
  spectralParameterOfRegulator energy (side.regulator broadening)

/-- The retarded side normalizes to the positive signed regulator. -/
@[simp]
theorem spectralParameter_retarded_ofRegulator (energy broadening : ℝ) :
    spectralParameter .retarded energy broadening =
      spectralParameterOfRegulator energy broadening := by
  simp [spectralParameter]

/-- The advanced side normalizes to the negative signed regulator. -/
@[simp]
theorem spectralParameter_advanced_ofRegulator (energy broadening : ℝ) :
    spectralParameter .advanced energy broadening =
      spectralParameterOfRegulator energy (-broadening) := by
  simp [spectralParameter]

@[simp]
theorem spectralParameter_re (side : SpectralSide) (energy broadening : ℝ) :
    (spectralParameter side energy broadening).re = energy := by
  simp [spectralParameter]

@[simp]
theorem spectralParameter_im (side : SpectralSide) (energy broadening : ℝ) :
    (spectralParameter side energy broadening).im = side.regulator broadening := by
  simp [spectralParameter]

/-- Complex conjugation exchanges physical spectral sides. -/
@[simp]
theorem star_spectralParameter (side : SpectralSide) (energy broadening : ℝ) :
    star (spectralParameter side energy broadening) =
      spectralParameter side.opposite energy broadening := by
  simp [spectralParameter]

/-- The retarded spectral parameter `E + iη`. -/
def retardedSpectralParameter (energy broadening : ℝ) : ℂ :=
  spectralParameter .retarded energy broadening

/-- The advanced spectral parameter `E - iη`. -/
def advancedSpectralParameter (energy broadening : ℝ) : ℂ :=
  spectralParameter .advanced energy broadening

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For an arbitrary nonzero signed regulator, the spectral shift multiplied by its resolvent is
the identity. -/
theorem spectralShift_mul_resolvent_spectralParameterOfRegulator
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) - hamiltonian) *
        resolvent hamiltonian (spectralParameterOfRegulator energy regulator) = 1 := by
  exact QuantumTheory.spectralShift_mul_resolvent_of_not_mem
    hamiltonian (spectralParameterOfRegulator energy regulator)
    (QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
      hamiltonian hself (spectralParameterOfRegulator energy regulator)
      (by
        rw [spectralParameterOfRegulator_im]
        exact hregulator))

/-- For an arbitrary nonzero signed regulator, its resolvent multiplied by the spectral shift is
the identity. -/
theorem resolvent_spectralParameterOfRegulator_mul_spectralShift
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    resolvent hamiltonian (spectralParameterOfRegulator energy regulator) *
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) - hamiltonian) =
      1 := by
  exact QuantumTheory.resolvent_mul_spectralShift_of_not_mem
    hamiltonian (spectralParameterOfRegulator energy regulator)
    (QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
      hamiltonian hself (spectralParameterOfRegulator energy regulator)
      (by
        rw [spectralParameterOfRegulator_im]
        exact hregulator))

/-- The resolvent quadratic form has the signed-regulator Herglotz identity in the orientation
`⟪Gv,v⟫`. -/
theorem im_inner_resolvent_spectralParameterOfRegulator_apply_self
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (v : H) :
    (inner ℂ
      (resolvent hamiltonian (spectralParameterOfRegulator energy regulator) v) v).im =
      regulator *
        ‖resolvent hamiltonian (spectralParameterOfRegulator energy regulator) v‖ ^ 2 := by
  let green := resolvent hamiltonian (spectralParameterOfRegulator energy regulator)
  let w := green v
  have hshift :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) - hamiltonian) *
          green = 1 := by
    simpa [green] using
      spectralShift_mul_resolvent_spectralParameterOfRegulator
        hamiltonian hself energy regulator hregulator
  have hshiftApply :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) - hamiltonian)
          w = v := by
    have h := congrArg (fun operator : H →L[ℂ] H => operator v) hshift
    simpa [w] using h
  have hshiftApply' :
      spectralParameterOfRegulator energy regulator • w - hamiltonian w = v := by
    simpa [Algebra.algebraMap_eq_smul_one] using hshiftApply
  have hsymm : (hamiltonian : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  have hinner :
      inner ℂ w v =
        inner ℂ w (spectralParameterOfRegulator energy regulator • w - hamiltonian w) :=
    congrArg (fun x : H => inner ℂ w x) hshiftApply'.symm
  have himHamiltonian : (inner ℂ w (hamiltonian w)).im = 0 :=
    hsymm.im_inner_self_apply w
  have himSelf : (inner ℂ w w).im = 0 := by
    exact inner_self_im (𝕜 := ℂ) w
  have hreSelf : (inner ℂ w w).re = ‖w‖ ^ 2 := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) w).symm
  change (inner ℂ w v).im = regulator * ‖w‖ ^ 2
  rw [hinner, inner_sub_right, inner_smul_right]
  simp only [Complex.sub_im, Complex.mul_im, himHamiltonian, himSelf, hreSelf,
    spectralParameterOfRegulator_im, sub_zero, mul_zero, zero_add]

/-- For a self-adjoint Hamiltonian, taking the adjoint of a resolvent reverses the arbitrary signed
imaginary regulator. -/
theorem star_resolvent_spectralParameterOfRegulator
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy regulator : ℝ) :
    star (resolvent hamiltonian (spectralParameterOfRegulator energy regulator)) =
      resolvent hamiltonian (spectralParameterOfRegulator energy (-regulator)) := by
  unfold resolvent
  rw [← Ring.inverse_star]
  congr 1
  rw [star_sub, hself]
  simp [Algebra.algebraMap_eq_smul_one]

/-- Green operator on either spectral side, `((E + iγˢ) I - H)⁻¹`. -/
noncomputable def spectralResolvent
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  resolvent hamiltonian (spectralParameter side energy broadening)

omit [CompleteSpace H] in
/-- The retarded side normalizes to the arbitrary-regulator resolvent at `+η`. -/
@[simp]
theorem spectralResolvent_retarded_ofRegulator
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) :
    spectralResolvent .retarded hamiltonian energy broadening =
      resolvent hamiltonian (spectralParameterOfRegulator energy broadening) := by
  simp [spectralResolvent]

omit [CompleteSpace H] in
/-- The advanced side normalizes to the arbitrary-regulator resolvent at `-η`. -/
@[simp]
theorem spectralResolvent_advanced_ofRegulator
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) :
    spectralResolvent .advanced hamiltonian energy broadening =
      resolvent hamiltonian (spectralParameterOfRegulator energy (-broadening)) := by
  simp [spectralResolvent]

/-- Retarded Green operator `((E + iη) I - H)⁻¹`. -/
noncomputable def retardedResolvent
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  spectralResolvent .retarded hamiltonian energy broadening

/-- Advanced Green operator `((E - iη) I - H)⁻¹`. -/
noncomputable def advancedResolvent
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  spectralResolvent .advanced hamiltonian energy broadening

/-- The side-indexed shifted operator multiplied by the canonical spectral resolvent is the
identity. -/
theorem spectralShift_mul_spectralResolvent
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) *
        spectralResolvent side hamiltonian energy broadening = 1 := by
  simpa only [spectralResolvent, spectralParameter] using
    spectralShift_mul_resolvent_spectralParameterOfRegulator
      hamiltonian hself energy (side.regulator broadening)
      (side.regulator_ne_zero hbroadening)

/-- The canonical spectral resolvent multiplied by its side-indexed shift is the identity. -/
theorem spectralResolvent_mul_spectralShift
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    spectralResolvent side hamiltonian energy broadening *
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) =
      1 := by
  simpa only [spectralResolvent, spectralParameter] using
    resolvent_spectralParameterOfRegulator_mul_spectralShift
      hamiltonian hself energy (side.regulator broadening)
      (side.regulator_ne_zero hbroadening)

end
end Transport
end QuantumTheory
