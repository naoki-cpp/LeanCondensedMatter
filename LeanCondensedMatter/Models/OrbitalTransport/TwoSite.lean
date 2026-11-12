import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Exact two-site, two-orbital continuity

Consider two spatial sites, each carrying the real orbitals `p_x`, `p_y`.
The basis order is `(0,x), (0,y), (1,x), (1,y)`. In units `ℏ = 1`:

* `H_cf = Δ σ_z` independently on both sites,
* `H_hop = -t` between equal orbitals on different sites,
* the internal orbital polarization is `L_z = σ_y` on either site.

The bond flux is derived from the hopping commutator, not postulated as an
independent observable. Both local Heisenberg equations contain an onsite
orbital torque. The two bond fluxes cancel because the hopping preserves the
total internal angular momentum.

This is a finite one-particle model, not a derivation of continuum
`r × p`, Wannier orbital angular momentum, or a unique bulk current density.
-/

namespace QuantumTheory.Models.OrbitalTransport.TwoSite

open scoped Matrix

/-- A complex-linear observable in the four-state two-site/two-orbital basis. -/
abbrev OrbitalMatrix := Matrix (Fin 4) (Fin 4) ℂ

/-- Onsite splitting between the two orbitals at each spatial site. -/
noncomputable def crystalField (Δ : ℝ) : OrbitalMatrix :=
  !![(Δ : ℂ), 0, 0, 0;
     0, -(Δ : ℂ), 0, 0;
     0, 0, (Δ : ℂ), 0;
     0, 0, 0, -(Δ : ℂ)]

/-- Orbital-preserving intersite hopping. -/
noncomputable def hopping (t : ℝ) : OrbitalMatrix :=
  !![0, 0, -(t : ℂ), 0;
     0, 0, 0, -(t : ℂ);
     -(t : ℂ), 0, 0, 0;
     0, -(t : ℂ), 0, 0]

/-- Hamiltonian with onsite crystal field and orbital-preserving hopping. -/
noncomputable def hamiltonian (Δ t : ℝ) : OrbitalMatrix :=
  crystalField Δ + hopping t

/-- Local `L_z` at site zero in units `ℏ = 1`. -/
def orbitalZZero : OrbitalMatrix :=
  !![0, -Complex.I, 0, 0;
     Complex.I, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Local `L_z` at site one in units `ℏ = 1`. -/
def orbitalZOne : OrbitalMatrix :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, -Complex.I;
     0, 0, Complex.I, 0]

/-- Projector onto both orbitals of spatial site zero (unit charge). -/
def siteZeroChargeProjector : OrbitalMatrix :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Crystal-field torque on a specified local orbital moment. -/
noncomputable def localTorque (Δ : ℝ) (L : OrbitalMatrix) : OrbitalMatrix :=
  Complex.I • (crystalField Δ * L - L * crystalField Δ)

/-- Negative hopping contribution to the Heisenberg evolution of a supplied one-particle
observable. It represents outgoing bond flux when the observable is site-localized;
antisymmetry is not claimed for arbitrary observables. -/
noncomputable def hoppingOutflow (t : ℝ) (L : OrbitalMatrix) : OrbitalMatrix :=
  -Complex.I • (hopping t * L - L * hopping t)

/-- Outgoing orbital bond flux from site zero to site one. -/
noncomputable def bondFluxZeroToOne (t : ℝ) : OrbitalMatrix :=
  hoppingOutflow t orbitalZZero

/-- Outgoing orbital bond flux from site one to site zero. -/
noncomputable def bondFluxOneToZero (t : ℝ) : OrbitalMatrix :=
  hoppingOutflow t orbitalZOne

/-- Charge-bond outflow derived from the same hopping Hamiltonian as orbital flow. -/
noncomputable def siteZeroChargeBondFlux (t : ℝ) : OrbitalMatrix :=
  hoppingOutflow t siteZeroChargeProjector

/-- The hopping does not change the total internal orbital moment. -/
theorem hopping_commutes_totalOrbital (t : ℝ) :
    hopping t * (orbitalZZero + orbitalZOne) =
      (orbitalZZero + orbitalZOne) * hopping t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hopping, orbitalZZero, orbitalZOne, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

/-- The two oriented bond fluxes are antisymmetric. -/
theorem bondFluxOneToZero_eq_neg (t : ℝ) :
    bondFluxOneToZero t = -bondFluxZeroToOne t := by
  have hsum :
      (hopping t * orbitalZZero - orbitalZZero * hopping t) +
        (hopping t * orbitalZOne - orbitalZOne * hopping t) = 0 := by
    calc
      _ = hopping t * (orbitalZZero + orbitalZOne) -
            (orbitalZZero + orbitalZOne) * hopping t := by
              rw [mul_add, add_mul]
              abel
      _ = 0 := sub_eq_zero.mpr (hopping_commutes_totalOrbital t)
  have hcomm :
      hopping t * orbitalZOne - orbitalZOne * hopping t =
        -(hopping t * orbitalZZero - orbitalZZero * hopping t) :=
    eq_neg_of_add_eq_zero_right hsum
  unfold bondFluxOneToZero bondFluxZeroToOne hoppingOutflow
  rw [hcomm]
  simp only [smul_neg]

/-- Site-zero local orbital balance: derivative + outgoing flux = local torque. -/
theorem continuity_zero (Δ t : ℝ) :
    Complex.I • (hamiltonian Δ t * orbitalZZero -
        orbitalZZero * hamiltonian Δ t) +
      bondFluxZeroToOne t = localTorque Δ orbitalZZero := by
  unfold hamiltonian bondFluxZeroToOne hoppingOutflow localTorque
  simp only [add_mul, mul_add]
  module

/-- Site-one local orbital balance: derivative + outgoing flux = local torque. -/
theorem continuity_one (Δ t : ℝ) :
    Complex.I • (hamiltonian Δ t * orbitalZOne -
        orbitalZOne * hamiltonian Δ t) +
      bondFluxOneToZero t = localTorque Δ orbitalZOne := by
  unfold hamiltonian bondFluxOneToZero hoppingOutflow localTorque
  simp only [add_mul, mul_add]
  module

/-- Explicit crystal-field torque on site zero, with no spin-orbit coupling. -/
theorem localTorque_zero_eq (Δ : ℝ) :
    localTorque Δ orbitalZZero =
      !![0, 2 * (Δ : ℂ), 0, 0;
         2 * (Δ : ℂ), 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [localTorque, crystalField, orbitalZZero] <;> ring_nf <;> simp

/-- In particular the site-zero torque is nonzero for nonzero splitting. -/
theorem localTorque_zero_ne_zero (Δ : ℝ) (hΔ : Δ ≠ 0) :
    localTorque Δ orbitalZZero ≠ 0 := by
  intro h
  rw [localTorque_zero_eq] at h
  have h01 := congrArg (fun M : OrbitalMatrix => M 0 1) h
  have hc : (Δ : ℂ) = 0 := by
    have htwo : (2 : ℂ) * (Δ : ℂ) = 0 := by simpa using h01
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact hΔ (Complex.ofReal_inj.mp hc)

/-- Total orbital angular momentum changes only through the crystal-field
torques; the bond flux cancels between the two sites. -/
theorem totalOrbitalEvolution (Δ t : ℝ) :
    Complex.I • (hamiltonian Δ t * (orbitalZZero + orbitalZOne) -
      (orbitalZZero + orbitalZOne) * hamiltonian Δ t) =
        localTorque Δ orbitalZZero + localTorque Δ orbitalZOne := by
  unfold hamiltonian localTorque
  rw [add_mul, mul_add, hopping_commutes_totalOrbital t]
  simp only [mul_add, add_mul, smul_add, smul_sub]
  module

end QuantumTheory.Models.OrbitalTransport.TwoSite
