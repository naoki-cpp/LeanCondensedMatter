import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.Transport.Core.ContinuumMeasure
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Two-dimensional massive Dirac model for anomalous Hall transport

This file fixes the clean two-band conventions and the closed Berry-curvature benchmark used
throughout the transport stack. The momentum variables `px`, `py` are physical momenta (not wave
vectors), so

```text
H₀(p) = v (pₓ σₓ + pᵧ σᵧ) + m σ_z,
v_μ = ∂H₀/∂p_μ,
j_μ = -e v_μ,  μ ∈ {x,y}.
```

The in-plane direction is represented explicitly by `Direction2`; the direction-indexed `velocity`
and `current` definitions are the public model-level owners used throughout the transport stack.
The Pauli-vector basis uses the model-independent `InternalSpace.PauliAxis`, since its `z` component
is an internal mass/pseudospin channel rather than a third momentum direction.
The closed Berry-curvature benchmark is recorded directly here; its agreement with the
model-specific force-matrix expression is proved downstream.

The generic charge-like current theory is the authority for the canonical `q v` interpretation;
this model file records only its concrete electron-current realization `j_μ = -e v_μ`.

With this convention the continuum measure is `d²p / (2πℏ)²`; its scalar normalization is owned by
`Transport.Core.ContinuumMeasure`.

Disorder, Fermi occupation, Kubo–Středa integration, and ultraviolet regularization remain
separate downstream phases.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Complex two-band matrices. -/
abbrev Matrix2 := InternalSpace.PauliMatrix

/-- Massive-Dirac notation for the common Pauli matrix `σₓ`. -/
abbrev sigmaX : Matrix2 := InternalSpace.pauliX

/-- Massive-Dirac notation for the common Pauli matrix `σᵧ`. -/
abbrev sigmaY : Matrix2 := InternalSpace.pauliY

/-- Massive-Dirac notation for the common Pauli matrix `σ_z`. -/
abbrev sigmaZ : Matrix2 := InternalSpace.pauliZ

/-- Massive-Dirac notation for the model-independent Pauli-basis axis. -/
abbrev PauliAxis := InternalSpace.PauliAxis

/-- Cartesian directions in the two-dimensional Dirac plane. -/
inductive Direction2 where
  | x
  | y
  deriving DecidableEq

instance : Fintype Direction2 where
  elems := {.x, .y}
  complete := by
    intro direction
    cases direction <;> simp

/-- Select a component of a Pauli vector. -/
def pauliAxisComponent {α : Type*} (axis : PauliAxis) (x y z : α) : α :=
  match axis with
  | .x => x
  | .y => y
  | .z => z

/-- Pauli matrix associated with an in-plane Cartesian direction. -/
def directionPauli : Direction2 → Matrix2
  | .x => sigmaX
  | .y => sigmaY

/-- Axis-indexed coefficient vector `d(p) = (v pₓ, v pᵧ, m)` of the clean Dirac Hamiltonian. -/
def diracPauliCoefficients (v m px py : ℝ) : PauliAxis → ℂ
  | .x => ((v * px : ℝ) : ℂ)
  | .y => ((v * py : ℝ) : ℂ)
  | .z => ((m : ℝ) : ℂ)

/-- Clean two-dimensional massive Dirac Hamiltonian
`H₀(p) = v (pₓ σₓ + pᵧ σᵧ) + m σ_z`. -/
def hamiltonian (v m px py : ℝ) : Matrix2 :=
  ((v * px : ℝ) : ℂ) • sigmaX +
    ((v * py : ℝ) : ℂ) • sigmaY +
      ((m : ℝ) : ℂ) • sigmaZ

/-- The clean Hamiltonian is the Pauli synthesis `d(p) · σ`. -/
@[simp] theorem hamiltonian_eq_pauliCombination (v m px py : ℝ) :
    hamiltonian v m px py =
      InternalSpace.pauliCombination (diracPauliCoefficients v m px py) := by
  rfl

/-- Velocity operator `v_μ = ∂H₀/∂p_μ = v σ_μ`. -/
def velocity (direction : Direction2) (v : ℝ) : Matrix2 :=
  ((v : ℝ) : ℂ) • directionPauli direction

/-- Concrete massive-Dirac realization `j_μ = -e v_μ` of the canonical charge-like current
representative. The parameter `e > 0` denotes the elementary-charge magnitude, so the electron
charge is `-e`. -/
def current (direction : Direction2) (e v : ℝ) : Matrix2 :=
  (((-e : ℝ) : ℂ)) • velocity direction v

/-- Positive energy squared of the clean massive Dirac dispersion. -/
def energySq (v m px py : ℝ) : ℝ :=
  v ^ 2 * (px ^ 2 + py ^ 2) + m ^ 2

/-- Simultaneous momentum inversion leaves the massive-Dirac dispersion polynomial unchanged. -/
@[simp] theorem energySq_neg_momentum (v m px py : ℝ) :
    energySq v m (-px) (-py) = energySq v m px py := by
  simp [energySq]

/-- The bilinear square of the Dirac Pauli coefficient vector is the dispersion polynomial. -/
theorem diracPauliCoefficients_dot_self (v m px py : ℝ) :
    dotProduct (diracPauliCoefficients v m px py) (diracPauliCoefficients v m px py) =
      ((energySq v m px py : ℝ) : ℂ) := by
  rw [InternalSpace.dotProduct_pauliAxis]
  simp [diracPauliCoefficients, energySq]
  push_cast
  ring

/-- Positive Dirac energy `E = √(v²(pₓ²+pᵧ²)+m²)`. -/
def energy (v m px py : ℝ) : ℝ :=
  Real.sqrt (energySq v m px py)

/-- Two bands of the massive Dirac Hamiltonian. -/
inductive Band where
  | lower
  | upper
  deriving DecidableEq

instance : Fintype Band where
  elems := {.lower, .upper}
  complete := by
    intro band
    cases band <;> simp

/-- A finite sum over the massive-Dirac bands is the lower-band term plus the upper-band term. -/
theorem sum_band {M : Type*} [AddCommMonoid M] (f : Band → M) :
    ∑ band : Band, f band = f .lower + f .upper := by
  change ∑ band ∈ ({.lower, .upper} : Finset Band), f band = _
  simp

/-- The other band in the two-band massive-Dirac model. -/
def oppositeBand : Band → Band
  | .lower => .upper
  | .upper => .lower

@[simp] theorem oppositeBand_lower : oppositeBand .lower = .upper := rfl
@[simp] theorem oppositeBand_upper : oppositeBand .upper = .lower := rfl
@[simp] theorem oppositeBand_oppositeBand (band : Band) : oppositeBand (oppositeBand band) = band := by
  cases band <;> rfl

/-- Sign of the band energy: lower `↦ -1`, upper `↦ +1`. -/
def bandSign : Band → ℝ
  | .lower => -1
  | .upper => 1

@[simp] theorem bandSign_oppositeBand (band : Band) :
    bandSign (oppositeBand band) = -bandSign band := by
  cases band <;> simp [oppositeBand, bandSign]

/-- Band energy `E_± = ±E`. -/
def bandEnergy (band : Band) (v m px py : ℝ) : ℝ :=
  bandSign band * energy v m px py

/-- Closed clean massive-Dirac Berry-curvature benchmark before occupation/integration. -/
def berryCurvature (band : Band) (v m px py : ℝ) : ℝ :=
  -(bandSign band * m * v ^ 2) / (2 * energy v m px py ^ 3)

/-- The dispersion polynomial is nonnegative. -/
theorem energySq_nonneg (v m px py : ℝ) : 0 ≤ energySq v m px py := by
  unfold energySq
  positivity

/-- `E²` recovers the dispersion polynomial. -/
theorem energy_sq (v m px py : ℝ) :
    energy v m px py ^ 2 = energySq v m px py := by
  exact Real.sq_sqrt (energySq_nonneg v m px py)

/-- A Pauli shift means `a I - (x σₓ + y σᵧ + z σ_z)`; when its quadratic denominator is nonzero,
its closed inverse is the denominator-scaled companion Pauli numerator. -/
theorem pauliShiftMatrix_mul_closedInverse
    (a x y z : ℂ) (hden : a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 ≠ 0) :
    (a • (1 : Matrix2) - (x • sigmaX + y • sigmaY + z • sigmaZ)) *
      ((a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2)⁻¹ •
        (a • (1 : Matrix2) + (x • sigmaX + y • sigmaY + z • sigmaZ))) = 1 := by
  let u : PauliAxis → ℂ
    | .x => x
    | .y => y
    | .z => z
  have hcombination :
      InternalSpace.pauliCombination u = x • sigmaX + y • sigmaY + z • sigmaZ := by
    rfl
  have hdot : dotProduct u u = x ^ 2 + y ^ 2 + z ^ 2 := by
    rw [InternalSpace.dotProduct_pauliAxis]
    simp [u, pow_two]
  have hquadratic := InternalSpace.pauliShift_mul_companion a u
  rw [hcombination, hdot] at hquadratic
  have hdenEq :
      a ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) = a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := by
    ring
  rw [hdenEq] at hquadratic
  rw [mul_smul_comm, hquadratic, smul_smul]
  simp [hden]

/-- The massive-Dirac Hamiltonian squares to `E² I`. -/
theorem hamiltonian_mul_self (v m px py : ℝ) :
    hamiltonian v m px py * hamiltonian v m px py =
      ((energySq v m px py : ℝ) : ℂ) • (1 : Matrix2) := by
  rw [hamiltonian_eq_pauliCombination, InternalSpace.pauliCombination_mul_self,
    diracPauliCoefficients_dot_self]

@[simp] theorem bandSign_lower : bandSign .lower = -1 := rfl
@[simp] theorem bandSign_upper : bandSign .upper = 1 := rfl

@[simp] theorem bandEnergy_lower (v m px py : ℝ) :
    bandEnergy .lower v m px py = -energy v m px py := by
  simp [bandEnergy]

@[simp] theorem bandEnergy_upper (v m px py : ℝ) :
    bandEnergy .upper v m px py = energy v m px py := by
  simp [bandEnergy]

/-- Upper-band Berry curvature `Ω₊ = -m v²/(2E³)`. -/
theorem berryCurvature_upper (v m px py : ℝ) :
    berryCurvature .upper v m px py =
      -(m * v ^ 2) / (2 * energy v m px py ^ 3) := by
  simp [berryCurvature]

/-- Lower-band Berry curvature `Ω₋ = +m v²/(2E³)`. -/
theorem berryCurvature_lower (v m px py : ℝ) :
    berryCurvature .lower v m px py =
      (m * v ^ 2) / (2 * energy v m px py ^ 3) := by
  simp [berryCurvature]

end

end QuantumTheory.Transport.Models.MassiveDirac
