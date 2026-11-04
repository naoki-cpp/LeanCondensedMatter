import LeanCondensedMatter.Transport.FiniteConductivityTable.Reciprocity
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Operator time reversal and finite-time Kubo conductivity

Hamiltonian covariance and preservation of operator exponentials give
the reversal law for the Schrödinger propagators. Together with
stationarity of the positive density state, this proves reciprocity of
the current-current Kubo kernel. The contact contribution is also
derived from its operator covariance and Hermiticity.

Unlike exact eigenvector pairing, these operator hypotheses permit a
Kramers antiunitary with square minus identity on state vectors.
The finite-time transform is kept separate from the infinite-time,
zero-switching, DC, and thermodynamic limits.
-/

namespace QuantumTheory.Transport

open QuantumTheory.LinearResponse
open ContinuousLinearMap

noncomputable section

namespace KuboTimeReversalData

variable {M d H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [FiniteDimensional ℂ H]
variable (data : KuboTimeReversalData M d H)

/-- Complex conjugation of the Schrödinger generator reverses its sign. -/
theorem transform_schrodingerGenerator (m : M) :
    data.transform (schrodingerGenerator (data.system m)) =
      -(schrodingerGenerator (data.system (data.reverse m))) := by
  simp only [schrodingerGenerator, data.transform_smul,
    data.hamiltonian_reverse, data.system_hbar]
  simp

/-- Hamiltonian covariance induces negative-time covariance of the
free Schrödinger propagator. -/
theorem transform_freePropagator (m : M) (t : ℝ) :
    data.transform (freePropagator (data.system m) t) =
      freePropagator (data.system (data.reverse m)) (-t) := by
  rw [freePropagator_eq_exp, freePropagator_eq_exp, data.transform_exp,
    data.transform_smul, data.transform_schrodingerGenerator m]
  simp

/-- Antiunitarity reverses the time argument of Heisenberg evolution. -/
theorem transform_heisenbergEvolution (m : M) (t : ℝ)
    (A : H →L[ℂ] H) :
    data.transform
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t A) =
      heisenbergEvolution
        (freePropagatorGroup (data.system (data.reverse m))) (-t)
          (data.transform A) := by
  rw [heisenbergEvolution_freePropagatorGroup_apply,
    heisenbergEvolution_freePropagatorGroup_apply,
    data.transform_mul, data.transform_mul,
    data.transform_freePropagator m (-t),
    data.transform_freePropagator m t]
  simp

/-- A density operator commuting with the Hamiltonian gives a stationary
finite-trace expectation, without imposing spectral-basis constraints. -/
theorem expectation_stationary (m : M) (t : ℝ) (A : H →L[ℂ] H) :
    data.expectation m
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t A) =
      data.expectation m A := by
  let sys := data.system m
  let ρ := (data.density m).op
  let U := freePropagator sys
  have hcomm : Commute (U t) ρ :=
    commute_freePropagator_of_commute_hamiltonian sys ρ
      (data.density_stationary m) t
  have hunit : U t * U (-t) = 1 := by
    dsimp [U]
    rw [← freePropagator_add, add_neg_cancel, freePropagator_zero]
  change finiteDimensionalOperatorTrace
      (ρ * heisenbergEvolution (freePropagatorGroup sys) t A) =
        finiteDimensionalOperatorTrace (ρ * A)
  rw [heisenbergEvolution_freePropagatorGroup_apply]
  calc
    finiteDimensionalOperatorTrace (ρ * (U (-t) * A * U t)) =
        finiteDimensionalOperatorTrace ((ρ * U (-t) * A) * U t) := by
      simp only [mul_assoc]
    _ = finiteDimensionalOperatorTrace (U t * (ρ * U (-t) * A)) :=
      finiteDimensionalOperatorTrace_mul_comm _ _
    _ = finiteDimensionalOperatorTrace (ρ * A) := by
      rw [show U t * (ρ * U (-t) * A) = ρ * A by
        calc
          U t * (ρ * U (-t) * A) =
              (U t * ρ) * U (-t) * A := by simp only [mul_assoc]
          _ = (ρ * U t) * U (-t) * A := by rw [hcomm.eq]
          _ = ρ * A := by rw [mul_assoc, hunit, mul_one]]

/-- Taking the adjoint of a Heisenberg-evolved Hermitian observable does
not change that observable. -/
private theorem star_evolved_of_selfAdjoint
    (sys : BoundedFreeSystem H) (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (t : ℝ) :
    star (heisenbergEvolution (freePropagatorGroup sys) t A) =
      heisenbergEvolution (freePropagatorGroup sys) t A := by
  rw [← map_star, ContinuousLinearMap.star_eq_adjoint, hA.adjoint_eq]

/-- Finite-trace expectation is complex-linear in the observable. -/
private theorem expectation_sub (m : M)
    (A B : H →L[ℂ] H) :
    data.expectation m (A - B) =
      data.expectation m A - data.expectation m B := by
  simp [expectation, mul_sub]

/-- Time reversal exchanges the measured and source slots of a two-point
equilibrium correlation, including the reversal of the time argument
and its cancellation by stationarity. -/
theorem correlation_reverse_of_odd (m : M) (t : ℝ)
    (A B A' B' : H →L[ℂ] H)
    (hA : IsSelfAdjoint A')
    (hB : IsSelfAdjoint B')
    (hTA : data.transform A = -A')
    (hTB : data.transform B = -B') :
    data.expectation m
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B) =
      data.expectation (data.reverse m)
        (heisenbergEvolution
          (freePropagatorGroup (data.system (data.reverse m))) t B' * A') := by
  let U := freePropagatorGroup (data.system (data.reverse m))
  have hprod :
      data.transform
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B) =
      heisenbergEvolution U (-t) A' * B' := by
    rw [data.transform_mul, data.transform_heisenbergEvolution, hTA, hTB]
    simp [U]
  have hAstar : star (heisenbergEvolution U (-t) A') =
      heisenbergEvolution U (-t) A' :=
    data.star_evolved_of_selfAdjoint _ A' hA (-t)
  have hBstar : star B' = B' := by
    rw [ContinuousLinearMap.star_eq_adjoint, hB.adjoint_eq]
  have hstar :
      star (data.expectation (data.reverse m)
          (heisenbergEvolution U (-t) A' * B')) =
        data.expectation (data.reverse m)
          (B' * heisenbergEvolution U (-t) A') := by
    rw [← data.expectation_star, star_mul, hBstar, hAstar]
  have hshift :
      data.expectation (data.reverse m)
          (B' * heisenbergEvolution U (-t) A') =
        data.expectation (data.reverse m)
          (heisenbergEvolution U t B' * A') := by
    rw [← data.expectation_stationary (data.reverse m) t
      (B' * heisenbergEvolution U (-t) A')]
    rw [map_mul, heisenbergEvolution_heisenbergEvolution]
    simp
  calc
    data.expectation m
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B) =
      star (data.expectation (data.reverse m)
        (data.transform
          (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B))) := by
      simpa using (congrArg star
        (data.expectation_reverse m
          (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B))).symm
    _ = star (data.expectation (data.reverse m)
        (heisenbergEvolution U (-t) A' * B')) := by rw [hprod]
    _ = data.expectation (data.reverse m)
        (B' * heisenbergEvolution U (-t) A') := hstar
    _ = data.expectation (data.reverse m)
        (heisenbergEvolution U t B' * A') := hshift

/-- The current-current commutator is reciprocal under simultaneous
reversal of the magnetic controls and exchange of current directions. -/
theorem current_commutator_reverse (m : M) (i j : d) (t : ℝ) :
    data.expectation m
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t
          (data.current m i) * data.current m j -
          data.current m j *
            heisenbergEvolution (freePropagatorGroup (data.system m)) t
              (data.current m i)) =
      data.expectation (data.reverse m)
        (heisenbergEvolution
            (freePropagatorGroup (data.system (data.reverse m))) t
              (data.current (data.reverse m) j) *
                data.current (data.reverse m) i -
          data.current (data.reverse m) i *
            heisenbergEvolution
              (freePropagatorGroup (data.system (data.reverse m))) t
                (data.current (data.reverse m) j)) := by
  let A := data.current m i
  let B := data.current m j
  let Ap := data.current (data.reverse m) i
  let Bp := data.current (data.reverse m) j
  let U := freePropagatorGroup (data.system m)
  let Up := freePropagatorGroup (data.system (data.reverse m))
  have hfirst :
      data.expectation m (heisenbergEvolution U t A * B) =
        data.expectation (data.reverse m)
          (heisenbergEvolution Up t Bp * Ap) :=
    data.correlation_reverse_of_odd m t A B Ap Bp
      (data.current_selfAdjoint (data.reverse m) i)
      (data.current_selfAdjoint (data.reverse m) j)
      (data.current_reverse m i) (data.current_reverse m j)
  have hBst : star B = B := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      (data.current_selfAdjoint m j).adjoint_eq]
  have hApst : star Ap = Ap := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      (data.current_selfAdjoint (data.reverse m) i).adjoint_eq]
  have hsecond :
      data.expectation m (B * heisenbergEvolution U t A) =
        data.expectation (data.reverse m)
          (Ap * heisenbergEvolution Up t Bp) := by
    calc
      _ = star (data.expectation m
          (heisenbergEvolution U t A * B)) := by
        rw [← data.expectation_star, star_mul, hBst]
        rw [data.star_evolved_of_selfAdjoint
          (data.system m) A (data.current_selfAdjoint m i) t]
      _ = star (data.expectation (data.reverse m)
          (heisenbergEvolution Up t Bp * Ap)) := by rw [hfirst]
      _ = data.expectation (data.reverse m)
          (Ap * heisenbergEvolution Up t Bp) := by
        rw [← data.expectation_star, star_mul, hApst]
        rw [data.star_evolved_of_selfAdjoint
          (data.system (data.reverse m)) Bp
          (data.current_selfAdjoint (data.reverse m) j) t]
  rw [data.expectation_sub, data.expectation_sub, hfirst, hsecond]

/-- The physical contact response is reciprocal as a consequence of
operator covariance and Hermiticity, not a scalar reciprocity axiom. -/
theorem contact_expectation_reverse (m : M) (i j : d) :
    data.expectation m (data.contact m i j) =
      data.expectation (data.reverse m)
        (data.contact (data.reverse m) j i) := by
  have hself : star (data.contact m i j) = data.contact m i j := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      (data.contact_selfAdjoint m i j).adjoint_eq]
  calc
    data.expectation m (data.contact m i j) =
        star (data.expectation m (data.contact m i j)) := by
      rw [← data.expectation_star, hself]
    _ = data.expectation (data.reverse m)
          (data.transform (data.contact m i j)) :=
      (data.expectation_reverse m _).symm
    _ = data.expectation (data.reverse m)
          (data.contact (data.reverse m) j i) := by
      rw [data.contact_reverse m i j]

/-- Finite-time retarded current-current Kubo kernel. -/
noncomputable def currentKuboKernel (m : M) (i j : d) (t : ℝ) : ℂ :=
  (Complex.I / (data.system m).hbar) *
    data.expectation m
      (heisenbergEvolution (freePropagatorGroup (data.system m)) t
        (data.current m i) * data.current m j -
       data.current m j *
        heisenbergEvolution (freePropagatorGroup (data.system m)) t
          (data.current m i))

theorem currentKuboKernel_reverse (m : M) (i j : d) (t : ℝ) :
    data.currentKuboKernel m i j t =
      data.currentKuboKernel (data.reverse m) j i t := by
  unfold currentKuboKernel
  rw [data.system_hbar m, data.system_hbar (data.reverse m),
    data.current_commutator_reverse m i j t]

/-- A finite-time exponentially switched transform of the Kubo kernel.
This is not an infinite-time or DC limit. -/
noncomputable def integratedCurrentKuboKernel
    (m : M) (i j : d) (omega eta duration : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..duration,
    Complex.exp ((-(eta : ℂ) + Complex.I * (omega : ℂ)) * (t : ℂ)) *
      data.currentKuboKernel m i j t

theorem integratedCurrentKuboKernel_reverse
    (m : M) (i j : d) (omega eta duration : ℝ) :
    data.integratedCurrentKuboKernel m i j omega eta duration =
      data.integratedCurrentKuboKernel (data.reverse m) j i omega eta duration := by
  unfold integratedCurrentKuboKernel
  apply intervalIntegral.integral_congr
  intro t ht
  rw [data.currentKuboKernel_reverse m i j t]

/-- Conductivity evaluated from the finite-time Kubo kernel and its
microscopic contact operator, using the canonical electric-field factor. -/
noncomputable def conductivityComponent
    (volume : PositiveVolume) (omega eta duration : ℝ)
    (m : M) (i j : d) : ℂ :=
  (data.integratedCurrentKuboKernel m i j omega eta duration +
      data.expectation m (data.contact m i j)) *
    finiteVolumeConductivityNormalization volume omega eta

/-- Finite-time conductivity tensor constructed entirely from microscopic
density, Hamiltonian, current, and contact covariance hypotheses. -/
noncomputable def conductivityFamily
    (volume : PositiveVolume) (omega eta duration : ℝ) :
    M → ConductivityTensor d :=
  fun m => { component := data.conductivityComponent volume omega eta duration m }

/-- Onsager–Casimir reciprocity is proved without an eigenbasis pairing
assumption or a postulated equality of conductivity components. -/
theorem conductivityFamily_isOnsagerReciprocal
    (volume : PositiveVolume) (omega eta duration : ℝ) :
    ConductivityTensor.IsOnsagerReciprocal
      (data.conductivityFamily volume omega eta duration) data.reverse := by
  intro m i j
  change data.conductivityComponent volume omega eta duration m i j =
    data.conductivityComponent volume omega eta duration (data.reverse m) j i
  unfold conductivityComponent
  rw [data.integratedCurrentKuboKernel_reverse m i j omega eta duration,
    data.contact_expectation_reverse m i j]

end KuboTimeReversalData

end
end QuantumTheory.Transport
