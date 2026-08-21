import LeanCondensedMatter.QuantumTheory.DensityOperator.Finite
import LeanCondensedMatter.QuantumTheory.LinearResponse.PurePointFrequencyDomain
import LeanCondensedMatter.QuantumTheory.LinearResponse.ResponseChannel
import LeanCondensedMatter.Transport.Resolvent

set_option linter.style.header false

/-!
# Generic finite pure-point Kubo–Bastin response

This module owns the statistics-independent finite Kubo–Bastin bridge.  It is generic in the
Hilbert-space carrier and in the measured/source vertices:

```text
pure-point Lehmann response
  -> retarded-resolvent spectral response
  -> ordinary finite-dimensional trace response
  -> ResponseChannel packaging.
```

The spectral identities only require a complete complex Hilbert space.  Finite dimensionality is
introduced only where the ordinary `LinearMap.trace` is used.  Fermionic Fock spaces, lattice
currents, Peierls contacts, and conductivity normalization are downstream specializations.

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

/-- The retarded spectral shift is nonzero at positive switching rate. -/
theorem retardedSpectralShift_ne_zero
    (hbar omega eta energyₘ energyₙ : ℝ)
    (hhbar : 0 < hbar) (heta : 0 < eta) :
    retardedSpectralParameter
          (kuboBastinRetardedEnergy hbar omega energyₘ)
          (kuboBastinEnergyBroadening hbar eta) -
        (energyₙ : ℂ) ≠ 0 := by
  intro hzero
  have him : hbar * eta = 0 := by
    have himZero := congrArg Complex.im hzero
    simpa [retardedSpectralParameter, kuboBastinEnergyBroadening] using himZero
  exact (mul_ne_zero (ne_of_gt hhbar) (ne_of_gt heta)) him

variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

/-- The retarded resolvent acts diagonally on any supplied pure-point energy eigenbasis. -/
theorem retardedResolvent_apply_purePointBasis
    (omega eta : ℝ) (heta : 0 < eta) (m n : ι) :
    retardedResolvent system.hamiltonian.1
        (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
        (kuboBastinEnergyBroadening system.hbar eta)
        (data.basis n) =
      (retardedSpectralParameter
          (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
          (kuboBastinEnergyBroadening system.hbar eta) -
        (data.energy n : ℂ))⁻¹ • data.basis n := by
  let z := retardedSpectralParameter
    (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
    (kuboBastinEnergyBroadening system.hbar eta)
  let S : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) z - system.hamiltonian.1
  let G := retardedResolvent system.hamiltonian.1
    (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
    (kuboBastinEnergyBroadening system.hbar eta)
  have hbroadening :
      0 < kuboBastinEnergyBroadening system.hbar eta :=
    kuboBastinEnergyBroadening_pos system.hbar eta system.hbar_pos heta
  have hSG : S * G = 1 := by
    simpa [S, G, z] using
      (retardedShift_mul_resolvent system.hamiltonian.1
        system.hamiltonian.2
        (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
        (kuboBastinEnergyBroadening system.hbar eta) hbroadening)
  have hGS : G * S = 1 := by
    simpa [S, G, z] using
      (resolvent_mul_retardedShift system.hamiltonian.1
        system.hamiltonian.2
        (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
        (kuboBastinEnergyBroadening system.hbar eta) hbroadening)
  have hshift : z - (data.energy n : ℂ) ≠ 0 := by
    simpa [z] using
      (retardedSpectralShift_ne_zero system.hbar omega eta
        (data.energy m) (data.energy n) system.hbar_pos heta)
  have hS_basis : S (data.basis n) =
      (z - (data.energy n : ℂ)) • data.basis n := by
    simp [S, data.hamiltonian_apply_basis n, sub_smul]
  have hS_injective : Function.Injective S := by
    intro x y hxy
    calc
      x = (G * S) x := by rw [hGS]; simp
      _ = G (S x) := rfl
      _ = G (S y) := congrArg G hxy
      _ = (G * S) y := rfl
      _ = y := by rw [hGS]; simp
  apply hS_injective
  calc
    S (G (data.basis n)) = data.basis n := by
      change (S * G) (data.basis n) = data.basis n
      rw [hSG]
      simp
    _ = S ((z - (data.energy n : ℂ))⁻¹ • data.basis n) := by
      rw [map_smul, hS_basis]
      rw [← mul_smul]
      simp [hshift]

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
  rw [retardedResolvent_apply_purePointBasis system data omega eta heta m n]
  rw [inner_smul_right]
  simp [inner_self_eq_norm_sq_to_K, data.basis.orthonormal.norm_eq_one]

/-- One finite Kubo–Bastin transition for supplied measured and source vertices. -/
noncomputable def finiteKuboBastinSpectralVertexTerm
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

/-- At positive switching rate, a generic finite Lehmann transition equals its retarded-resolvent
Kubo–Bastin form. -/
theorem finiteLehmannVertexTerm_eq_bastinSpectral
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (heta : 0 < eta) (mn : ι × ι) :
    lehmannTerm system.hbar omega eta
        (data.energy mn.1 - data.energy mn.2)
        (purePointTransitionWeight system data measured source mn) =
      finiteKuboBastinSpectralVertexTerm
        system data measured source omega eta mn := by
  have hhbar : system.hbar ≠ 0 := ne_of_gt system.hbar_pos
  have hhbarComplex : (system.hbar : ℂ) ≠ 0 := by
    exact_mod_cast hhbar
  have hshift := retardedSpectralShift_ne_zero system.hbar omega eta
    (data.energy mn.1) (data.energy mn.2) system.hbar_pos heta
  unfold lehmannTerm
  rw [lehmannDenominator_eq_retardedSpectralShift
    system.hbar omega eta (data.energy mn.1) (data.energy mn.2) hhbar]
  unfold finiteKuboBastinSpectralVertexTerm
  rw [inner_purePointBasis_retardedResolvent system data omega eta heta mn.1 mn.2]
  unfold purePointTransitionWeight
  field_simp [hhbar, hhbarComplex, hshift]

variable [Fintype ι]

/-- Finite pure-point Kubo–Bastin response coefficient for supplied measured/source vertices and an
explicit first-order observable variation. -/
noncomputable def finiteKuboBastinSpectralVertexResponse
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) : ℂ :=
  (∑ mn : ι × ι,
      finiteKuboBastinSpectralVertexTerm
        system data measured source omega eta mn) +
    purePointNormalizedExpectation system data observableVariation

/-- The generic fixed-positive-rate frequency-domain susceptibility plus the explicit
observable-variation term is exactly the finite Kubo–Bastin spectral response. -/
theorem adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_bastinSpectral
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          measured source omega eta heta +
        purePointNormalizedExpectation system data observableVariation =
      finiteKuboBastinSpectralVertexResponse
        system data measured source observableVariation omega eta := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate_purePoint_eq_finite_sum
    system data measured source omega eta heta]
  unfold finiteKuboBastinSpectralVertexResponse
  congr 1
  apply Finset.sum_congr rfl
  intro mn _
  exact finiteLehmannVertexTerm_eq_bastinSpectral
    system data measured source omega eta heta mn

variable [FiniteDimensional ℂ H]

/-- Ordinary finite-dimensional trace carrier for the generic measured/source Kubo–Bastin
response. -/
noncomputable def finiteKuboBastinVertexTraceCarrier
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) : H →ₗ[ℂ] H :=
  (∑ mn : ι × ι,
      finiteKuboBastinSpectralVertexTerm
        system data measured source omega eta mn) •
    ((purePointDensityOperator system data).op : H →ₗ[ℂ] H)

/-- Expanding the generic ordinary trace carrier gives the finite retarded-resolvent spectral sum. -/
theorem linearMap_trace_finiteKuboBastinVertexTraceCarrier
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) :
    LinearMap.trace ℂ H
        (finiteKuboBastinVertexTraceCarrier
          system data measured source omega eta) =
      ∑ mn : ι × ι,
        finiteKuboBastinSpectralVertexTerm
          system data measured source omega eta mn := by
  unfold finiteKuboBastinVertexTraceCarrier
  rw [map_smul]
  rw [DensityOperator.linearMap_trace_eq_one]
  simp

/-- Generic ordinary finite-dimensional Kubo–Bastin response with the observable variation kept as
an explicit expectation value. -/
noncomputable def finiteDimensionalKuboBastinVertexResponse
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) : ℂ :=
  LinearMap.trace ℂ H
      (finiteKuboBastinVertexTraceCarrier
        system data measured source omega eta) +
    purePointNormalizedExpectation system data observableVariation

/-- The generic ordinary-trace response is exactly its finite spectral form. -/
theorem finiteDimensionalKuboBastinVertexResponse_eq_spectral
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) :
    finiteDimensionalKuboBastinVertexResponse
        system data measured source observableVariation omega eta =
      finiteKuboBastinSpectralVertexResponse
        system data measured source observableVariation omega eta := by
  unfold finiteDimensionalKuboBastinVertexResponse
    finiteKuboBastinSpectralVertexResponse
  rw [linearMap_trace_finiteKuboBastinVertexTraceCarrier]

/-- The generic fixed-positive-rate response plus observable variation equals the ordinary
finite-dimensional Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_finiteDimensionalKuboBastin
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          measured source omega eta heta +
        purePointNormalizedExpectation system data observableVariation =
      finiteDimensionalKuboBastinVertexResponse
        system data measured source observableVariation omega eta := by
  rw [adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_bastinSpectral
    system data measured source observableVariation omega eta heta]
  exact (finiteDimensionalKuboBastinVertexResponse_eq_spectral
    system data measured source observableVariation omega eta).symm

/-- The spectral Kubo–Bastin response attached directly to a neutral `ResponseChannel`. -/
noncomputable def finiteKuboBastinSpectralChannelResponse
    (channel : ResponseChannel H)
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralVertexResponse system data
    channel.measured channel.source channel.observableVariation omega eta

/-- The ordinary finite-dimensional Kubo–Bastin response attached directly to a neutral
`ResponseChannel`. -/
noncomputable def finiteDimensionalKuboBastinChannelResponse
    (channel : ResponseChannel H)
    (omega eta : ℝ) : ℂ :=
  finiteDimensionalKuboBastinVertexResponse system data
    channel.measured channel.source channel.observableVariation omega eta

/-- At positive switching rate, the frequency-domain response carried by a `ResponseChannel` is
exactly its finite Kubo–Bastin spectral response. -/
theorem adiabaticFrequencyDomainResponseChannel_eq_bastinSpectral
    (channel : ResponseChannel H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          channel.measured channel.source omega eta heta +
        purePointNormalizedExpectation system data channel.observableVariation =
      finiteKuboBastinSpectralChannelResponse system data channel omega eta := by
  simpa [finiteKuboBastinSpectralChannelResponse] using
    adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_bastinSpectral
      system data channel.measured channel.source channel.observableVariation omega eta heta

/-- At positive switching rate, the frequency-domain response carried by a `ResponseChannel` is
exactly its ordinary finite-dimensional Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainResponseChannel_eq_finiteDimensionalKuboBastin
    (channel : ResponseChannel H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          channel.measured channel.source omega eta heta +
        purePointNormalizedExpectation system data channel.observableVariation =
      finiteDimensionalKuboBastinChannelResponse system data channel omega eta := by
  simpa [finiteDimensionalKuboBastinChannelResponse] using
    adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_finiteDimensionalKuboBastin
      system data channel.measured channel.source channel.observableVariation omega eta heta

end
end Transport
end QuantumTheory
