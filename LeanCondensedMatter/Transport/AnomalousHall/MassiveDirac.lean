import LeanCondensedMatter.Analysis.Operator.Spectral.BerryCurvature
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Two-dimensional massive Dirac model for anomalous Hall transport

This file fixes the clean two-band conventions and the first Berry-curvature benchmark used by
#1269.  The momentum variables `px`, `py` are physical momenta (not wave vectors), so

```text
H₀(p) = v (pₓ σₓ + pᵧ σᵧ) + m σ_z,
vₓ = ∂H₀/∂pₓ = v σₓ,
vᵧ = ∂H₀/∂pᵧ = v σᵧ,
jₓ = -e vₓ,
jᵧ = -e vᵧ.
```

With this convention the continuum measure is `d²p / (2πℏ)²`.  The generic pointwise spectral
Berry-curvature identities live upstream in `Analysis.Operator.Spectral.BerryCurvature`; this file
supplies the concrete massive-Dirac algebra that will be connected to that force-matrix API.

Disorder, Fermi occupation, Kubo–Středa integration, and ultraviolet regularization remain
separate downstream phases.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

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

/-- Clean two-dimensional massive Dirac Hamiltonian
`H₀(p) = v (pₓ σₓ + pᵧ σᵧ) + m σ_z`. -/
def hamiltonian (v m px py : ℝ) : Matrix2 :=
  ((v * px : ℝ) : ℂ) • sigmaX +
    ((v * py : ℝ) : ℂ) • sigmaY +
      ((m : ℝ) : ℂ) • sigmaZ

/-- Velocity operator `vₓ = ∂H₀/∂pₓ = v σₓ`. -/
def velocityX (v : ℝ) : Matrix2 :=
  ((v : ℝ) : ℂ) • sigmaX

/-- Velocity operator `vᵧ = ∂H₀/∂pᵧ = v σᵧ`. -/
def velocityY (v : ℝ) : Matrix2 :=
  ((v : ℝ) : ℂ) • sigmaY

/-- Charge-current vertex `jₓ = -e vₓ`.  The parameter `e > 0` denotes the elementary-charge
magnitude, so the electron charge is `-e`. -/
def currentX (e v : ℝ) : Matrix2 :=
  (((-e * v : ℝ) : ℂ)) • sigmaX

/-- Charge-current vertex `jᵧ = -e vᵧ`. -/
def currentY (e v : ℝ) : Matrix2 :=
  (((-e * v : ℝ) : ℂ)) • sigmaY

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
  deriving DecidableEq, Repr

/-- Sign of the band energy: lower `↦ -1`, upper `↦ +1`. -/
def bandSign : Band → ℝ
  | .lower => -1
  | .upper => 1

/-- Band energy `E_± = ±E`. -/
def bandEnergy (band : Band) (v m px py : ℝ) : ℝ :=
  bandSign band * energy v m px py

/-- The `ℏ`-dependent prefactor in the physical-momentum continuum measure
`d²p / (2πℏ)²`. -/
def momentumMeasurePrefactor (hbar : ℝ) : ℝ :=
  1 / (2 * Real.pi * hbar) ^ 2

/-- A small component representation for the two-band `d` vector. -/
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving Repr

/-- Scalar triple product `a · (b × c)`. -/
def scalarTriple (a b c : Vec3) : ℝ :=
  a.x * (b.y * c.z - b.z * c.y) -
    a.y * (b.x * c.z - b.z * c.x) +
      a.z * (b.x * c.y - b.y * c.x)

/-- Massive-Dirac `d` vector, `d(p) = (v pₓ, v pᵧ, m)`. -/
def dVector (v m px py : ℝ) : Vec3 :=
  ⟨v * px, v * py, m⟩

/-- `∂d/∂pₓ = (v,0,0)`. -/
def dMomentumX (v : ℝ) : Vec3 :=
  ⟨v, 0, 0⟩

/-- `∂d/∂pᵧ = (0,v,0)`. -/
def dMomentumY (v : ℝ) : Vec3 :=
  ⟨0, v, 0⟩

/-- Gauge-independent two-band curvature expression
`-s d·(∂ₓd×∂ᵧd)/(2 E³)` for band sign `s = ±1`.

A later theorem in this consumer will identify this concrete expression with the upstream spectral
force-matrix Berry curvature. -/
def twoBandCurvatureFromTriple (sign triple radius : ℝ) : ℝ :=
  -sign * triple / (2 * radius ^ 3)

/-- Closed clean massive-Dirac Berry-curvature benchmark before occupation/integration. -/
def berryCurvature (band : Band) (v m px py : ℝ) : ℝ :=
  twoBandCurvatureFromTriple (bandSign band)
    (scalarTriple (dVector v m px py) (dMomentumX v) (dMomentumY v))
    (energy v m px py)

@[simp] theorem hamiltonian_00 (v m px py : ℝ) :
    hamiltonian v m px py 0 0 = (m : ℂ) := by
  simp [hamiltonian, sigmaX, sigmaY, sigmaZ]

@[simp] theorem hamiltonian_01 (v m px py : ℝ) :
    hamiltonian v m px py 0 1 =
      (v : ℂ) * ((px : ℂ) - Complex.I * (py : ℂ)) := by
  simp [hamiltonian, sigmaX, sigmaY, sigmaZ]
  ring

@[simp] theorem hamiltonian_10 (v m px py : ℝ) :
    hamiltonian v m px py 1 0 =
      (v : ℂ) * ((px : ℂ) + Complex.I * (py : ℂ)) := by
  simp [hamiltonian, sigmaX, sigmaY, sigmaZ]
  ring

@[simp] theorem hamiltonian_11 (v m px py : ℝ) :
    hamiltonian v m px py 1 1 = -(m : ℂ) := by
  simp [hamiltonian, sigmaX, sigmaY, sigmaZ]

@[simp] theorem velocityX_00 (v : ℝ) : velocityX v 0 0 = 0 := by
  simp [velocityX, sigmaX]

@[simp] theorem velocityX_01 (v : ℝ) : velocityX v 0 1 = (v : ℂ) := by
  simp [velocityX, sigmaX]

@[simp] theorem velocityX_10 (v : ℝ) : velocityX v 1 0 = (v : ℂ) := by
  simp [velocityX, sigmaX]

@[simp] theorem velocityX_11 (v : ℝ) : velocityX v 1 1 = 0 := by
  simp [velocityX, sigmaX]

@[simp] theorem velocityY_00 (v : ℝ) : velocityY v 0 0 = 0 := by
  simp [velocityY, sigmaY]

@[simp] theorem velocityY_01 (v : ℝ) : velocityY v 0 1 = -Complex.I * (v : ℂ) := by
  simp [velocityY, sigmaY]

@[simp] theorem velocityY_10 (v : ℝ) : velocityY v 1 0 = Complex.I * (v : ℂ) := by
  simp [velocityY, sigmaY]

@[simp] theorem velocityY_11 (v : ℝ) : velocityY v 1 1 = 0 := by
  simp [velocityY, sigmaY]

@[simp] theorem currentX_00 (e v : ℝ) : currentX e v 0 0 = 0 := by
  simp [currentX, sigmaX]

@[simp] theorem currentX_01 (e v : ℝ) : currentX e v 0 1 = ((-e * v : ℝ) : ℂ) := by
  simp [currentX, sigmaX]

@[simp] theorem currentX_10 (e v : ℝ) : currentX e v 1 0 = ((-e * v : ℝ) : ℂ) := by
  simp [currentX, sigmaX]

@[simp] theorem currentX_11 (e v : ℝ) : currentX e v 1 1 = 0 := by
  simp [currentX, sigmaX]

@[simp] theorem currentY_00 (e v : ℝ) : currentY e v 0 0 = 0 := by
  simp [currentY, sigmaY]

@[simp] theorem currentY_01 (e v : ℝ) :
    currentY e v 0 1 = -Complex.I * ((-e * v : ℝ) : ℂ) := by
  simp [currentY, sigmaY]

@[simp] theorem currentY_10 (e v : ℝ) :
    currentY e v 1 0 = Complex.I * ((-e * v : ℝ) : ℂ) := by
  simp [currentY, sigmaY]

@[simp] theorem currentY_11 (e v : ℝ) : currentY e v 1 1 = 0 := by
  simp [currentY, sigmaY]

/-- The dispersion polynomial is nonnegative. -/
theorem energySq_nonneg (v m px py : ℝ) : 0 ≤ energySq v m px py := by
  unfold energySq
  positivity

/-- `E²` recovers the dispersion polynomial. -/
theorem energy_sq (v m px py : ℝ) :
    energy v m px py ^ 2 = energySq v m px py := by
  exact Real.sq_sqrt (energySq_nonneg v m px py)

/-- The massive-Dirac Hamiltonian squares to `E² I`. -/
theorem hamiltonian_mul_self (v m px py : ℝ) :
    hamiltonian v m px py * hamiltonian v m px py =
      ((energySq v m px py : ℝ) : ℂ) • (1 : Matrix2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, hamiltonian, sigmaX, sigmaY, sigmaZ, energySq] <;> ring

@[simp] theorem bandSign_lower : bandSign .lower = -1 := rfl
@[simp] theorem bandSign_upper : bandSign .upper = 1 := rfl

@[simp] theorem bandEnergy_lower (v m px py : ℝ) :
    bandEnergy .lower v m px py = -energy v m px py := by
  simp [bandEnergy]

@[simp] theorem bandEnergy_upper (v m px py : ℝ) :
    bandEnergy .upper v m px py = energy v m px py := by
  simp [bandEnergy]

/-- The massive-Dirac `d`-vector Jacobian contributes `m v²`. -/
theorem scalarTriple_dirac (v m px py : ℝ) :
    scalarTriple (dVector v m px py) (dMomentumX v) (dMomentumY v) = m * v ^ 2 := by
  simp [scalarTriple, dVector, dMomentumX, dMomentumY]
  ring

/-- Upper-band Berry curvature `Ω₊ = -m v²/(2E³)`. -/
theorem berryCurvature_upper (v m px py : ℝ) :
    berryCurvature .upper v m px py =
      -(m * v ^ 2) / (2 * energy v m px py ^ 3) := by
  simp [berryCurvature, twoBandCurvatureFromTriple, scalarTriple_dirac]

/-- Lower-band Berry curvature `Ω₋ = +m v²/(2E³)`. -/
theorem berryCurvature_lower (v m px py : ℝ) :
    berryCurvature .lower v m px py =
      (m * v ^ 2) / (2 * energy v m px py ^ 3) := by
  simp [berryCurvature, twoBandCurvatureFromTriple, scalarTriple_dirac]

end

end AnomalousHall.MassiveDirac
