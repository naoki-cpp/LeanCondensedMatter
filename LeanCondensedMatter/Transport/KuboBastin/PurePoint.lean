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

/-- Nonzero `ℏ` and nonzero switching rate give a nonzero resolvent energy broadening. -/
theorem kuboBastinEnergyBroadening_ne_zero
    (hbar eta : ℝ) (hhbar : hbar ≠ 0) (heta : eta ≠ 0) :
    kuboBastinEnergyBroadening hbar eta ≠ 0 := by
  exact mul_ne_zero hhbar heta

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

/-- The retarded spectral shift is nonzero whenever `ℏ` and the switching rate are nonzero. -/
theorem retardedSpectralShift_ne_zero
    (hbar omega eta energyₘ energyₙ : ℝ)
    (hhbar : hbar ≠ 0) (heta : eta ≠ 0) :
    retardedSpectralParameter
          (kuboBastinRetardedEnergy hbar omega energyₘ)
          (kuboBastinEnergyBroadening hbar eta) -
        (energyₙ : ℂ) ≠ 0 := by
  simpa only [spectralParameter_retarded] using
    spectralParameter_sub_real_ne_zero .retarded
      (kuboBastinRetardedEnergy hbar omega energyₘ)
      (kuboBastinEnergyBroadening hbar eta) energyₙ
      (kuboBastinEnergyBroadening_ne_zero hbar eta hhbar heta)

variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

/-- The diagonal matrix element of the retarded resolvent is its scalar spectral denominator. -/
theorem inner_purePointBasis_retardedResolvent
    (omega eta : ℝ) (heta : 0 < eta) (m n : ι) :
    inner ℂ (data.basis n)
        (retardedResolvent system.hamiltonian.1
          (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
          (kuboBastinEnergyBroadening system.hbar eta)
          (data.basis n)) =
      (retardedSpectralParameter
          (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
          (kuboBastinEnergyBroadening system.hbar eta) -
        (data.energy n : ℂ))⁻¹ := by
  have hres :
      retardedResolvent system.hamiltonian.1
          (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
          (kuboBastinEnergyBroadening system.hbar eta)
          (data.basis n) =
        (retardedSpectralParameter
            (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
            (kuboBastinEnergyBroadening system.hbar eta) -
          (data.energy n : ℂ))⁻¹ • data.basis n := by
    simpa only [retardedResolvent, retardedSpectralParameter] using
      resolvent_spectralParameterOfRegulator_apply_eigenvector
        system.hamiltonian.1 system.hamiltonian.2
        (data.hamiltonian_apply_basis n)
        (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
        (kuboBastinEnergyBroadening system.hbar eta)
        (ne_of_gt (kuboBastinEnergyBroadening_pos
          system.hbar eta system.hbar_pos heta))
  rw [hres]
  rw [inner_smul_right]
  simp [inner_self_eq_norm_sq_to_K, data.basis.orthonormal.norm_eq_one]

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
  have hshift := retardedSpectralShift_ne_zero system.hbar omega eta
    (data.energy mn.1) (data.energy mn.2) hhbar heta.ne'
  unfold lehmannTerm
  rw [lehmannDenominator_eq_retardedSpectralShift
    system.hbar omega eta (data.energy mn.1) (data.energy mn.2) hhbar]
  unfold purePointKuboBastinSpectralVertexTerm
  rw [inner_purePointBasis_retardedResolvent system data omega eta heta mn.1 mn.2]
  unfold purePointTransitionWeight
  field_simp [hhbar, hhbarComplex, hshift]

end
end Transport
end QuantumTheory
