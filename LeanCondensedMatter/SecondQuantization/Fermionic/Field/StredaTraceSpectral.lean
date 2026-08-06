import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StredaResolventSpectral
import LeanCondensedMatter.Transport.StredaTraceKernel

set_option linter.style.header false

/-!
# Pure-point spectral expansion of the canonical Středa trace

The canonical static Bastin integrand is an ordinary finite-dimensional trace of a product of
currents and retarded/advanced resolvents. This module expands that trace in a supplied finite
pure-point Hamiltonian basis.

The expansion keeps the real integration energy and positive broadening explicit. It is a property
of the canonical traced integrand only: no occupation integration, Peierls contact cancellation,
electric-field normalization, zero-broadening limit, or equality with the static conductivity
response is claimed here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open scoped BigOperators
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι] [FiniteDimensional ℂ H]

variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

/-- Retarded scalar resolvent factor on the `n`th energy eigenvector. -/
noncomputable def stredaRetardedSpectralFactor
    (energy broadening : ℝ) (n : ι) : ℂ :=
  (retardedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹

/-- Advanced scalar resolvent factor on the `n`th energy eigenvector. -/
noncomputable def stredaAdvancedSpectralFactor
    (energy broadening : ℝ) (n : ι) : ℂ :=
  (advancedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹

/-- Ordinary finite-dimensional trace written as the diagonal sum in the supplied pure-point
basis. -/
theorem finiteDimensionalOperatorTrace_eq_sum_inner_purePointBasis
    (operator : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (H := H) operator =
      ∑ m : ι, inner ℂ (data.basis m) (operator (data.basis m)) := by
  rw [finiteDimensionalOperatorTrace_apply]
  rw [LinearMap.trace_eq_sum_inner
    (operator : H →ₗ[ℂ] H) data.basis.toOrthonormalBasis]
  simp

/-- Matrix element of `left * diagonal * right` when the middle operator is diagonal in the
supplied pure-point basis. -/
theorem inner_purePointBasis_mul_diagonal_mul
    (left diagonal right : H →L[ℂ] H) (diagonalFactor : ι → ℂ)
    (hdiagonal : ∀ n, diagonal (data.basis n) = diagonalFactor n • data.basis n)
    (m : ι) :
    inner ℂ (data.basis m) ((left * diagonal * right) (data.basis m)) =
      ∑ n : ι,
        diagonalFactor n *
          inner ℂ (data.basis m) (left (data.basis n)) *
          inner ℂ (data.basis n) (right (data.basis m)) := by
  change inner ℂ (data.basis m)
    (left (diagonal (right (data.basis m)))) = _
  have hrepr := data.basis.toOrthonormalBasis.sum_repr' (right (data.basis m))
  simp only [HilbertBasis.coe_toOrthonormalBasis] at hrepr
  rw [← hrepr]
  simp_rw [map_sum, map_smul, hdiagonal, smul_smul, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Matrix element of `left * middle * right * terminal` when both inserted operators are diagonal
in the supplied pure-point basis. -/
theorem inner_purePointBasis_mul_diagonal_mul_mul_diagonal
    (left middle right terminal : H →L[ℂ] H)
    (middleFactor terminalFactor : ι → ℂ)
    (hmiddle : ∀ n, middle (data.basis n) = middleFactor n • data.basis n)
    (hterminal : ∀ n, terminal (data.basis n) = terminalFactor n • data.basis n)
    (m : ι) :
    inner ℂ (data.basis m)
        ((left * middle * right * terminal) (data.basis m)) =
      terminalFactor m *
        ∑ n : ι,
          middleFactor n *
            inner ℂ (data.basis m) (left (data.basis n)) *
            inner ℂ (data.basis n) (right (data.basis m)) := by
  change inner ℂ (data.basis m)
    (left (middle (right (terminal (data.basis m))))) = _
  rw [hterminal]
  simp only [map_smul, inner_smul_right]
  rw [inner_purePointBasis_mul_diagonal_mul
    system data left middle right middleFactor hmiddle m]
  ring

/-- Nested finite pure-point sum for the canonical static Bastin trace integrand. -/
noncomputable def regularizedBastinSpectralTraceSum
    (current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : ℂ :=
  ∑ m : ι,
    (stredaRetardedSpectralFactor data energy broadening m -
      stredaAdvancedSpectralFactor data energy broadening m) *
      ((∑ n : ι,
          (stredaRetardedSpectralFactor data energy broadening n) ^ 2 *
            inner ℂ (data.basis m) (current₁ (data.basis n)) *
            inner ℂ (data.basis n) (current₂ (data.basis m))) -
        ∑ n : ι,
          (stredaAdvancedSpectralFactor data energy broadening n) ^ 2 *
            inner ℂ (data.basis m) (current₂ (data.basis n)) *
            inner ℂ (data.basis n) (current₁ (data.basis m)))

/-- The canonical Bastin operator integrand in a form with all noncommutative signs expanded. -/
theorem regularizedBastinOperatorIntegrand_eq_expanded
    (current₁ current₂ : H →L[ℂ] H) (energy broadening : ℝ) :
    regularizedBastinOperatorIntegrand
        system.hamiltonian.1 current₁ current₂ energy broadening =
      current₁ * (retardedResolvent system.hamiltonian.1 energy broadening) ^ 2 * current₂ *
          retardedAdvancedResolventDifference system.hamiltonian.1 energy broadening -
        current₂ * (advancedResolvent system.hamiltonian.1 energy broadening) ^ 2 * current₁ *
          retardedAdvancedResolventDifference system.hamiltonian.1 energy broadening := by
  unfold regularizedBastinOperatorIntegrand
  noncomm_ring

/-- Finite pure-point spectral expansion of the canonical ordinary-trace Bastin integrand. -/
theorem regularizedBastinTraceIntegrand_eq_spectral_sum
    (current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    regularizedBastinTraceIntegrand
        system.hamiltonian.1 current₁ current₂ energy broadening =
      regularizedBastinSpectralTraceSum data current₁ current₂ energy broadening := by
  rw [finiteDimensionalOperatorTrace_eq_sum_inner_purePointBasis
    system data
    (regularizedBastinOperatorIntegrand
      system.hamiltonian.1 current₁ current₂ energy broadening)]
  unfold regularizedBastinSpectralTraceSum
  apply Finset.sum_congr rfl
  intro m _
  rw [regularizedBastinOperatorIntegrand_eq_expanded
    system current₁ current₂ energy broadening]
  rw [ContinuousLinearMap.sub_apply, inner_sub_right]
  have hretardedMiddle : ∀ n : ι,
      ((retardedResolvent system.hamiltonian.1 energy broadening) ^ 2) (data.basis n) =
        (stredaRetardedSpectralFactor data energy broadening n) ^ 2 • data.basis n := by
    intro n
    exact retardedResolvent_sq_apply_purePointBasis_at_energy
      system data energy broadening hbroadening n
  have hadvancedMiddle : ∀ n : ι,
      ((advancedResolvent system.hamiltonian.1 energy broadening) ^ 2) (data.basis n) =
        (stredaAdvancedSpectralFactor data energy broadening n) ^ 2 • data.basis n := by
    intro n
    exact advancedResolvent_sq_apply_purePointBasis_at_energy
      system data energy broadening hbroadening n
  have hterminal : ∀ n : ι,
      retardedAdvancedResolventDifference system.hamiltonian.1 energy broadening
          (data.basis n) =
        (stredaRetardedSpectralFactor data energy broadening n -
          stredaAdvancedSpectralFactor data energy broadening n) • data.basis n := by
    intro n
    unfold retardedAdvancedResolventDifference
    rw [ContinuousLinearMap.sub_apply]
    rw [retardedResolvent_apply_purePointBasis_at_energy
      system data energy broadening hbroadening n]
    rw [advancedResolvent_apply_purePointBasis_at_energy
      system data energy broadening hbroadening n]
    rw [sub_smul]
    rfl
  rw [inner_purePointBasis_mul_diagonal_mul_mul_diagonal
    system data current₁
      ((retardedResolvent system.hamiltonian.1 energy broadening) ^ 2)
      current₂
      (retardedAdvancedResolventDifference system.hamiltonian.1 energy broadening)
      (fun n => (stredaRetardedSpectralFactor data energy broadening n) ^ 2)
      (fun n => stredaRetardedSpectralFactor data energy broadening n -
        stredaAdvancedSpectralFactor data energy broadening n)
      hretardedMiddle hterminal m]
  rw [inner_purePointBasis_mul_diagonal_mul_mul_diagonal
    system data current₂
      ((advancedResolvent system.hamiltonian.1 energy broadening) ^ 2)
      current₁
      (retardedAdvancedResolventDifference system.hamiltonian.1 energy broadening)
      (fun n => (stredaAdvancedSpectralFactor data energy broadening n) ^ 2)
      (fun n => stredaRetardedSpectralFactor data energy broadening n -
        stredaAdvancedSpectralFactor data energy broadening n)
      hadvancedMiddle hterminal m]
  ring

end
end Field
end Fermionic
end SecondQuantization
