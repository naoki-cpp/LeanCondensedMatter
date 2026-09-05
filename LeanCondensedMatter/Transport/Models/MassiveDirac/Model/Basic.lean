import LeanCondensedMatter.Transport.Core.ContinuumMeasure
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Two-dimensional massive Dirac model for anomalous Hall transport

This file fixes the clean two-band conventions and the first Berry-curvature benchmark used by
#1269. The momentum variables `px`, `py` are physical momenta (not wave vectors), so

```text
H₀(p) = v (pₓ σₓ + pᵧ σᵧ) + m σ_z,
v_μ = ∂H₀/∂p_μ,
j_μ = -e v_μ,  μ ∈ {x,y}.
```

The in-plane direction is represented explicitly by `Direction2`; the direction-indexed `velocity`
and `current` definitions are the public model-level owners used throughout the transport stack.
The closed Berry-curvature benchmark is recorded directly here; its agreement with the
model-specific force-matrix expression is proved downstream.

The generic charge-like current theory is the authority for the canonical `q v` interpretation;
this model file records only its concrete electron-current realization `j_μ = -e v_μ`.

With this convention the continuum measure is `d²p / (2πℏ)²`; its scalar normalization is owned by
`Transport.Core.ContinuumMeasure`.

Disorder, Fermi occupation, Kubo–Středa integration, and ultraviolet regularization remain
separate downstream phases.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Complex two-band matrices. -/
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli matrix `σₓ`. -/
def sigmaX : Matrix2 :=
  !![0, 1; 1, 0]

/-- Pauli matrix `σᵧ`. -/
def sigmaY : Matrix2 :=
  !![0, -Complex.I; Complex.I, 0]

/-- Pauli matrix `σ_z`. -/
def sigmaZ : Matrix2 :=
  !![1, 0; 0, -1]

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

/-- Pauli matrix associated with an in-plane Cartesian direction. -/
def directionPauli : Direction2 → Matrix2
  | .x => sigmaX
  | .y => sigmaY

/-- Clean two-dimensional massive Dirac Hamiltonian
`H₀(p) = v (pₓ σₓ + pᵧ σᵧ) + m σ_z`. -/
def hamiltonian (v m px py : ℝ) : Matrix2 :=
  ((v * px : ℝ) : ℂ) • sigmaX +
    ((v * py : ℝ) : ℂ) • sigmaY +
      ((m : ℝ) : ℂ) • sigmaZ

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

/-- Positive Dirac energy `E = √(v²(pₓ²+pᵧ²)+m²)`. -/
def energy (v m px py : ℝ) : ℝ :=
  Real.sqrt (energySq v m px py)

/-- Two bands of the massive Dirac Hamiltonian. -/
inductive Band where
  | lower
  | upper
  deriving DecidableEq

/-- Sign of the band energy: lower `↦ -1`, upper `↦ +1`. -/
def bandSign : Band → ℝ
  | .lower => -1
  | .upper => 1

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

/-- A Pauli shift means `a I - x σₓ - y σᵧ - z σ_z`; when its quadratic denominator is nonzero,
its closed inverse is the denominator-scaled conjugate Pauli numerator. -/
theorem pauliShiftMatrix_mul_closedInverse
    (a x y z : ℂ) (hden : a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 ≠ 0) :
    (a • (1 : Matrix2) - x • sigmaX - y • sigmaY - z • sigmaZ) *
      ((a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2)⁻¹ •
        (a • (1 : Matrix2) + x • sigmaX + y • sigmaY + z • sigmaZ)) = 1 := by
  rw [mul_smul_comm]
  have hquadratic :
      (a • (1 : Matrix2) - x • sigmaX - y • sigmaY - z • sigmaZ) *
          (a • (1 : Matrix2) + x • sigmaX + y • sigmaY + z • sigmaZ) =
        (a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) • (1 : Matrix2) := by
    have hI : Complex.I ^ 2 = (-1 : ℂ) := by
      simpa [pow_two] using Complex.I_mul_I
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, sigmaX, sigmaY, sigmaZ] <;>
      ring_nf <;>
      simp [hI] <;>
      ring
  rw [hquadratic, smul_smul]
  simp [hden]

/-- The massive-Dirac Hamiltonian squares to `E² I`. -/
theorem hamiltonian_mul_self (v m px py : ℝ) :
    hamiltonian v m px py * hamiltonian v m px py =
      ((energySq v m px py : ℝ) : ℂ) • (1 : Matrix2) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, hamiltonian, sigmaX, sigmaY, sigmaZ, energySq] <;>
    ring_nf <;>
    simp [hI]

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

end AnomalousHall.MassiveDirac
