import LeanCondensedMatter.Models.MassiveDirac.Model.Kinematics
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Massive-Dirac Fermi-surface geometry

The radial band dispersion, monotonicity, metallic Fermi radius, on-shell energy, and isotropic
Fermi-surface velocity averages follow from the clean Hamiltonian and do not require a choice
of temperature or occupation law. Occupied regions and Fermi-step statements are downstream
in `Model.Occupation`.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

/-- Massive-Dirac band energy on the radial momentum coordinate used by the isotropic transport
reduction. Downstream Fermi-surface statements restrict this coordinate to the nonnegative axis. -/
def radialBandEnergy (v m : ℝ) (band : Band) (p : ℝ) : ℝ :=
  bandEnergy band v m p 0

/-- The positive massive-Dirac radial energy is injective on nonnegative momentum when `v ≠ 0`. -/
theorem energy_radial_eq_imp_eq_of_nonneg
    (v m p q : ℝ) (hv : v ≠ 0) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (henergy : energy v m p 0 = energy v m q 0) :
    p = q := by
  have hsquare := congrArg (fun x : ℝ => x ^ 2) henergy
  rw [energy_sq v m p 0, energy_sq v m q 0] at hsquare
  unfold energySq at hsquare
  norm_num at hsquare
  have hpqSq : p ^ 2 = q ^ 2 := hsquare.resolve_right hv
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hpqSq with hpq | hpq
  · exact hpq
  · nlinarith

/-- Metallic upper-band Fermi radius for the massive-Dirac dispersion,
`p_F = sqrt(ε_F² - m²) / |v|`. -/
def metallicFermiRadius (v m fermiEnergy : ℝ) : ℝ :=
  Real.sqrt (fermiEnergy ^ 2 - m ^ 2) / |v|

/-- The expression used for the metallic Fermi radius is always nonnegative. -/
theorem metallicFermiRadius_nonneg
    (v m fermiEnergy : ℝ) :
    0 ≤ metallicFermiRadius v m fermiEnergy := by
  unfold metallicFermiRadius
  exact div_nonneg (Real.sqrt_nonneg _) (abs_nonneg v)

/-- Squaring the explicit metallic Fermi radius removes the square root and absolute value whenever
the Fermi energy lies at or above the mass magnitude. -/
theorem metallicFermiRadius_sq
    (v m fermiEnergy : ℝ) (hmF : |m| ≤ fermiEnergy) :
    metallicFermiRadius v m fermiEnergy ^ 2 =
      (fermiEnergy ^ 2 - m ^ 2) / v ^ 2 := by
  unfold metallicFermiRadius
  have hplus : 0 ≤ fermiEnergy + |m| :=
    add_nonneg ((abs_nonneg m).trans hmF) (abs_nonneg m)
  have hprod : 0 ≤ (fermiEnergy - |m|) * (fermiEnergy + |m|) :=
    mul_nonneg (sub_nonneg.mpr hmF) hplus
  have hrad : 0 ≤ fermiEnergy ^ 2 - m ^ 2 := by
    rw [← sq_abs m]
    nlinarith
  rw [div_pow, Real.sq_sqrt hrad]
  simp [sq_abs]

/-- The positive Dirac energy at the metallic Fermi radius is exactly `ε_F` whenever
`|m| ≤ ε_F`. -/
theorem energy_metallicFermiRadius
    (v m fermiEnergy : ℝ) (hv : v ≠ 0) (hmF : |m| ≤ fermiEnergy) :
    energy v m (metallicFermiRadius v m fermiEnergy) 0 = fermiEnergy := by
  have hfermiNonneg : 0 ≤ fermiEnergy := (abs_nonneg m).trans hmF
  have hsq :
      energy v m (metallicFermiRadius v m fermiEnergy) 0 ^ 2 =
        fermiEnergy ^ 2 := by
    rw [energy_sq]
    unfold energySq
    norm_num
    rw [metallicFermiRadius_sq v m fermiEnergy hmF]
    field_simp [pow_ne_zero 2 hv]
    ring
  have henergyNonneg :
      0 ≤ energy v m (metallicFermiRadius v m fermiEnergy) 0 :=
    Real.sqrt_nonneg _
  nlinarith

/-- At the metallic Fermi radius, the squared radial energy derivative has the
standard massive-Dirac Fermi-surface form
`v^2 * (1 - m^2 / epsilon_F^2)`. -/
theorem radialEnergyDerivative_sq_metallicFermiRadius
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hmF : |m| ≤ fermiEnergy) (hfermi : fermiEnergy ≠ 0) :
    radialEnergyDerivative v m (metallicFermiRadius v m fermiEnergy) ^ 2 =
      v ^ 2 * (1 - m ^ 2 / fermiEnergy ^ 2) := by
  unfold radialEnergyDerivative
  rw [energy_metallicFermiRadius v m fermiEnergy hv hmF]
  rw [div_pow, mul_pow,
    metallicFermiRadius_sq v m fermiEnergy hmF]
  field_simp [hfermi, hv]

/-- In the strictly metallic regime `|m| < epsilon_F`, the squared Fermi-surface radial derivative
is strictly positive when `v ≠ 0`. -/
theorem radialEnergyDerivative_sq_metallicFermiRadius_pos
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hmF : |m| < fermiEnergy) :
    0 < radialEnergyDerivative v m (metallicFermiRadius v m fermiEnergy) ^ 2 := by
  have hfermiPos : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  rw [radialEnergyDerivative_sq_metallicFermiRadius
    v m fermiEnergy hv hmF.le hfermiNe]
  have hvSq : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_pos hfermiPos
  have hplus : 0 < fermiEnergy + |m| :=
    add_pos_of_pos_of_nonneg hfermiPos (abs_nonneg m)
  have hprod : 0 < (fermiEnergy - |m|) * (fermiEnergy + |m|) :=
    mul_pos (sub_pos.mpr hmF) hplus
  have hmSqLt : m ^ 2 < fermiEnergy ^ 2 := by
    rw [← sq_abs m]
    nlinarith
  have hratio : m ^ 2 / fermiEnergy ^ 2 < 1 := by
    exact (div_lt_one hfermiSq).2 hmSqLt
  positivity

/-- Positive radial energy is strictly increasing on the nonnegative axis when `v ≠ 0`. -/
theorem energy_radial_lt_of_lt_of_nonneg
    (v m p q : ℝ) (hv : v ≠ 0) (hp : 0 ≤ p) (hpq : p < q) :
    energy v m p 0 < energy v m q 0 := by
  have hvSq : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hpSqLt : p ^ 2 < q ^ 2 := by
    nlinarith
  have henergySqLt : energy v m p 0 ^ 2 < energy v m q 0 ^ 2 := by
    rw [energy_sq, energy_sq]
    unfold energySq
    norm_num
    nlinarith
  have hpEnergy : 0 ≤ energy v m p 0 := Real.sqrt_nonneg _
  have hqEnergy : 0 ≤ energy v m q 0 := Real.sqrt_nonneg _
  nlinarith

/-- In the metallic-or-band-edge regime `|m| ≤ ε_F`, the upper band is occupied exactly below the
explicit Fermi radius. At `ε_F = |m|`, this occupied region is empty and `p_F = 0`. -/
theorem bandEnergy_upper_lt_fermi_iff_lt_metallicFermiRadius
    (v m fermiEnergy p : ℝ) (hv : v ≠ 0)
    (hmF : |m| ≤ fermiEnergy) (hp : 0 ≤ p) :
    bandEnergy .upper v m p 0 < fermiEnergy ↔
      p < metallicFermiRadius v m fermiEnergy := by
  rw [bandEnergy_upper]
  have hfermi := energy_metallicFermiRadius v m fermiEnergy hv hmF
  constructor
  · intro henergy
    by_contra hpF
    have hpFle : metallicFermiRadius v m fermiEnergy ≤ p := le_of_not_gt hpF
    rcases hpFle.eq_or_lt with hpEq | hpLt
    · have hfermi' := hfermi
      rw [hpEq] at hfermi'
      linarith
    · have hmono := energy_radial_lt_of_lt_of_nonneg
        v m (metallicFermiRadius v m fermiEnergy) p hv
        (metallicFermiRadius_nonneg v m fermiEnergy) hpLt
      linarith
  · intro hpLt
    have hmono := energy_radial_lt_of_lt_of_nonneg
      v m p (metallicFermiRadius v m fermiEnergy) hv hp hpLt
    rw [hfermi] at hmono
    exact hmono

/-- Isotropic full-angle mean square of the `x` group-velocity component evaluated at the explicit
upper-band Fermi radius. -/
def isotropicFermiSurfaceMeanSquareVelocityX (v m fermiEnergy : ℝ) : ℝ :=
  isotropicMeanSquareRadialGroupVelocityX v m (metallicFermiRadius v m fermiEnergy)

/-- In the metallic-or-band-edge regime, the isotropic Fermi-surface factor is

`<v_x²>_FS = (v² / 2) * (1 - m² / ε_F²)`.
-/
theorem isotropicFermiSurfaceMeanSquareVelocityX_eq
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hmF : |m| ≤ fermiEnergy) (hfermi : fermiEnergy ≠ 0) :
    isotropicFermiSurfaceMeanSquareVelocityX v m fermiEnergy =
      v ^ 2 * (1 - m ^ 2 / fermiEnergy ^ 2) / 2 := by
  unfold isotropicFermiSurfaceMeanSquareVelocityX
  rw [isotropicMeanSquareRadialGroupVelocityX_eq,
    radialEnergyDerivative_sq_metallicFermiRadius v m fermiEnergy hv hmF hfermi]

/-- In the strictly metallic regime `|m| < ε_F`, the isotropic Fermi-surface `v_x²` factor is
strictly positive when `v ≠ 0`. -/
theorem isotropicFermiSurfaceMeanSquareVelocityX_pos
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hmF : |m| < fermiEnergy) :
    0 < isotropicFermiSurfaceMeanSquareVelocityX v m fermiEnergy := by
  unfold isotropicFermiSurfaceMeanSquareVelocityX
  rw [isotropicMeanSquareRadialGroupVelocityX_eq]
  exact div_pos
    (radialEnergyDerivative_sq_metallicFermiRadius_pos v m fermiEnergy hv hmF)
    (by norm_num)

end

end QuantumTheory.Models.MassiveDirac
