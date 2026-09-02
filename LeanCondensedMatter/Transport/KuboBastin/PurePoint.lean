import LeanCondensedMatter.QuantumTheory.LinearResponse.PurePointFrequencyDomain
import LeanCondensedMatter.Transport.Resolvent.Spectral

set_option linter.style.header false

/-!
# Pure-point Kubo–Bastin spectral bridge

This module owns the statistics-independent Kubo–Bastin algebra for a supplied pure-point energy
basis. The spectral index type is not assumed finite here:

```text
one pure-point Lehmann transition
  -> retarded-resolvent spectral transition.
```

Finite sums of transitions are downstream in `KuboBastin.Finite`. Genuine ordinary
finite-dimensional trace realizations belong to the canonical static Bastin/Středa layer under
`Transport.Streda`. Fermionic Fock spaces, lattice currents, Peierls contacts, and conductivity
normalization are downstream specializations.

No zero-frequency, zero-broadening, disorder, trace-per-unit-volume, or thermodynamic-limit
statement is introduced here.
-/

namespace QuantumTheory
namespace Transport

open LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Energy argument of the retarded resolvent associated with a transition whose first state has
energy `Eₘ`. -/
def kuboBastinRetardedEnergy (hbar omega energy : ℝ) : ℝ :=
  energy + hbar * omega

/-- Energy broadening matching the adiabatic switching rate. -/
def kuboBastinEnergyBroadening (hbar eta : ℝ) : ℝ :=
  hbar * eta

/-- Positive `ℏ` and positive switching rate give a positive resolvent energy broadening. -/
theorem kuboBastinEnergyBroadening_pos
    (hbar eta : ℝ) (hhbar : 0 < hbar) (heta : 0 < eta) :
    0 < kuboBastinEnergyBroadening hbar eta := by
  exact mul_pos hhbar heta

/-- The time-rate Lehmann denominator is the retarded energy denominator scaled by `-i/ℏ`. -/
theorem lehmannDenominator_eq_retardedSpectralShift
    (hbar omega eta energyₘ energyₙ : ℝ) (hhbar : hbar ≠ 0) :
    lehmannDenominator hbar omega eta (energyₘ - energyₙ) =
      (-(Complex.I) / (hbar : ℂ)) *
        (retardedSpectralParameter
            (kuboBastinRetardedEnergy hbar omega energyₘ)
            (kuboBastinEnergyBroadening hbar eta) -
          (energyₙ : ℂ)) := by
  apply Complex.ext
  · simp [lehmannDenominator, retardedSpectralParameter,
      kuboBastinRetardedEnergy, kuboBastinEnergyBroadening]
    field_simp [hhbar]
  · simp [lehmannDenominator, retardedSpectralParameter,
      kuboBastinRetardedEnergy, kuboBastinEnergyBroadening]
    field_simp [hhbar]
    ring

variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

/-- One pure-point Kubo–Bastin transition for supplied measured and source vertices. -/
noncomputable def purePointKuboBastinSpectralVertexTerm
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) : ℂ :=
  -(((data.probability mn.1 - data.probability mn.2 : ℝ) : ℂ)) *
    inner ℂ (data.basis mn.1) (measured (data.basis mn.2)) *
    inner ℂ (data.basis mn.2) (source (data.basis mn.1)) *
    inner ℂ (data.basis mn.2)
      (retardedResolvent system.hamiltonian.1
        (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
        (kuboBastinEnergyBroadening system.hbar eta)
        (data.basis mn.2))

/-- At positive switching rate, one pure-point Lehmann transition equals its retarded-resolvent
Kubo–Bastin form. -/
theorem purePointLehmannVertexTerm_eq_bastinSpectral
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (heta : 0 < eta) (mn : ι × ι) :
    lehmannTerm system.hbar omega eta
        (data.energy mn.1 - data.energy mn.2)
        (purePointTransitionWeight system data measured source mn) =
      purePointKuboBastinSpectralVertexTerm
        system data measured source omega eta mn := by
  have hhbar : system.hbar ≠ 0 := ne_of_gt system.hbar_pos
  have hhbarComplex : (system.hbar : ℂ) ≠ 0 := by
    exact_mod_cast hhbar
  have hregulator : kuboBastinEnergyBroadening system.hbar eta ≠ 0 :=
    ne_of_gt (kuboBastinEnergyBroadening_pos system.hbar eta system.hbar_pos heta)
  have hshift :
      retardedSpectralParameter
            (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
            (kuboBastinEnergyBroadening system.hbar eta) -
          (data.energy mn.2 : ℂ) ≠ 0 := by
    simpa only [retardedSpectralParameter] using
      spectralParameterOfRegulator_sub_real_ne_zero
        (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
        (kuboBastinEnergyBroadening system.hbar eta) (data.energy mn.2) hregulator
  have hres :
      retardedResolvent system.hamiltonian.1
          (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
          (kuboBastinEnergyBroadening system.hbar eta)
          (data.basis mn.2) =
        (retardedSpectralParameter
            (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
            (kuboBastinEnergyBroadening system.hbar eta) -
          (data.energy mn.2 : ℂ))⁻¹ • data.basis mn.2 := by
    simpa only [retardedResolvent, retardedSpectralParameter] using
      resolvent_spectralParameterOfRegulator_apply_eigenvector
        system.hamiltonian.1 system.hamiltonian.2
        (data.hamiltonian_apply_basis mn.2)
        (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
        (kuboBastinEnergyBroadening system.hbar eta) hregulator
  unfold lehmannTerm
  rw [lehmannDenominator_eq_retardedSpectralShift
    system.hbar omega eta (data.energy mn.1) (data.energy mn.2) hhbar]
  unfold purePointKuboBastinSpectralVertexTerm
  rw [hres, inner_smul_right]
  simp only [inner_self_eq_norm_sq_to_K, data.basis.orthonormal.norm_eq_one,
    norm_one, one_pow, one_smul]
  unfold purePointTransitionWeight
  field_simp [hhbar, hhbarComplex, hshift]

end
end Transport
end QuantumTheory
