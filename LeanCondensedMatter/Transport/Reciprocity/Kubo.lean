import LeanCondensedMatter.Transport.Reciprocity.Data
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.FiniteTime
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SpecialFunctions.Exponential

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

/-- Self-adjointness is preserved by free Heisenberg evolution. -/
private theorem star_evolved_of_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (sys : BoundedFreeSystem H) (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (t : ℝ) :
    star (heisenbergEvolution (freePropagatorGroup sys) t A) =
      heisenbergEvolution (freePropagatorGroup sys) t A := by
  rw [← map_star, ContinuousLinearMap.star_eq_adjoint, hA.adjoint_eq]

variable {M d H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [FiniteDimensional ℂ H]
variable (data : KuboTimeReversalData M d H)

/-- Complex conjugation of the Schrödinger generator reverses its sign. -/
theorem transform_schrodingerGenerator (m : M) :
    data.timeReversal.conjugateOperator (schrodingerGenerator (data.system m)) =
      -(schrodingerGenerator (data.system (data.reverse m))) := by
  simp only [schrodingerGenerator, data.timeReversal.conjugateOperator_smul,
    data.hamiltonian_reverse, data.system_hbar]
  have hcoeff :
      (starRingEnd ℂ) (-(Complex.I / (data.hbar : ℂ))) =
        Complex.I / (data.hbar : ℂ) := by
    change star (-(Complex.I / (data.hbar : ℂ))) =
      Complex.I / (data.hbar : ℂ)
    rw [star_neg, star_div₀]
    simp only [RCLike.star_def, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hcoeff]

/-- Hamiltonian covariance induces negative-time covariance of the
free Schrödinger propagator. -/
theorem transform_freePropagator (m : M) (t : ℝ) :
    data.timeReversal.conjugateOperator (freePropagator (data.system m) t) =
      freePropagator (data.system (data.reverse m)) (-t) := by
  rw [freePropagator_eq_exp, freePropagator_eq_exp, data.timeReversal.conjugateOperator_exp,
    data.timeReversal.conjugateOperator_smul, data.transform_schrodingerGenerator m]
  simp

/-- Antiunitarity reverses the time argument of Heisenberg evolution. -/
theorem transform_heisenbergEvolution (m : M) (t : ℝ)
    (A : H →L[ℂ] H) :
    data.timeReversal.conjugateOperator
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t A) =
      heisenbergEvolution
        (freePropagatorGroup (data.system (data.reverse m))) (-t)
          (data.timeReversal.conjugateOperator A) := by
  rw [heisenbergEvolution_freePropagatorGroup_apply,
    heisenbergEvolution_freePropagatorGroup_apply,
    data.timeReversal.conjugateOperator_mul, data.timeReversal.conjugateOperator_mul,
    data.transform_freePropagator m (-t),
    data.transform_freePropagator m t]

/-- Time reversal exchanges the measured and source slots of a two-point
equilibrium correlation, including the reversal of the time argument
and its cancellation by stationarity. -/
theorem correlation_reverse_of_odd (m : M) (t : ℝ)
    (A B A' B' : H →L[ℂ] H)
    (hA : IsSelfAdjoint A')
    (hB : IsSelfAdjoint B')
    (hTA : data.timeReversal.conjugateOperator A = -A')
    (hTB : data.timeReversal.conjugateOperator B = -B') :
    (data.density m).expectation
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B) =
      (data.density (data.reverse m)).expectation
        (heisenbergEvolution
          (freePropagatorGroup (data.system (data.reverse m))) t B' * A') := by
  let U := freePropagatorGroup (data.system (data.reverse m))
  have hprod :
      data.timeReversal.conjugateOperator
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B) =
      heisenbergEvolution U (-t) A' * B' := by
    rw [data.timeReversal.conjugateOperator_mul, data.transform_heisenbergEvolution, hTA, hTB]
    simp [U]
  have hAstar : star (heisenbergEvolution U (-t) A') =
      heisenbergEvolution U (-t) A' :=
    star_evolved_of_selfAdjoint _ A' hA (-t)
  have hBstar : star B' = B' := by
    rw [ContinuousLinearMap.star_eq_adjoint, hB.adjoint_eq]
  have hstar :
      star ((data.density (data.reverse m)).expectation
          (heisenbergEvolution U (-t) A' * B')) =
        (data.density (data.reverse m)).expectation
          (B' * heisenbergEvolution U (-t) A') := by
    rw [← (data.density (data.reverse m)).expectation_star, star_mul, hBstar, hAstar]
  have hshift :
      (data.density (data.reverse m)).expectation
          (B' * heisenbergEvolution U (-t) A') =
        (data.density (data.reverse m)).expectation
          (heisenbergEvolution U t B' * A') := by
    have hstationary :
        IsStationary U (data.density (data.reverse m)).toNormalizedExpectation :=
      isStationary_toNormalizedExpectation_of_commute_hamiltonian
        (data.system (data.reverse m)) (data.density (data.reverse m))
        (data.density_stationary (data.reverse m))
    have h := hstationary t (B' * heisenbergEvolution U (-t) A')
    change (data.density (data.reverse m)).expectation
        (heisenbergEvolution U t (B' * heisenbergEvolution U (-t) A')) =
      (data.density (data.reverse m)).expectation
        (B' * heisenbergEvolution U (-t) A') at h
    rw [← h]
    rw [map_mul, heisenbergEvolution_heisenbergEvolution]
    simp [U]
  calc
    (data.density m).expectation
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B) =
      star ((data.density (data.reverse m)).expectation
        (data.timeReversal.conjugateOperator
          (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B))) := by
      simpa using (congrArg star
        (data.expectation_reverse m
          (heisenbergEvolution (freePropagatorGroup (data.system m)) t A * B))).symm
    _ = star ((data.density (data.reverse m)).expectation
        (heisenbergEvolution U (-t) A' * B')) := by rw [hprod]
    _ = (data.density (data.reverse m)).expectation
        (B' * heisenbergEvolution U (-t) A') := hstar
    _ = (data.density (data.reverse m)).expectation
        (heisenbergEvolution U t B' * A') := hshift

/-- The current-current commutator is reciprocal under simultaneous
reversal of the magnetic controls and exchange of current directions. -/
theorem current_commutator_reverse (m : M) (i j : d) (t : ℝ) :
    (data.density m).expectation
        (heisenbergEvolution (freePropagatorGroup (data.system m)) t
          ((data.current m i).1) * (data.current m j).1 -
          (data.current m j).1 *
            heisenbergEvolution (freePropagatorGroup (data.system m)) t
              ((data.current m i).1)) =
      (data.density (data.reverse m)).expectation
        (heisenbergEvolution
            (freePropagatorGroup (data.system (data.reverse m))) t
              ((data.current (data.reverse m) j).1) *
                (data.current (data.reverse m) i).1 -
          (data.current (data.reverse m) i).1 *
            heisenbergEvolution
              (freePropagatorGroup (data.system (data.reverse m))) t
                ((data.current (data.reverse m) j).1)) := by
  let A := (data.current m i).1
  let B := (data.current m j).1
  let Ap := (data.current (data.reverse m) i).1
  let Bp := (data.current (data.reverse m) j).1
  let U := freePropagatorGroup (data.system m)
  let Up := freePropagatorGroup (data.system (data.reverse m))
  have hfirst :
      (data.density m).expectation (heisenbergEvolution U t A * B) =
        (data.density (data.reverse m)).expectation
          (heisenbergEvolution Up t Bp * Ap) :=
    data.correlation_reverse_of_odd m t A B Ap Bp
      ((data.current (data.reverse m) i).2)
      ((data.current (data.reverse m) j).2)
      (data.current_reverse m i) (data.current_reverse m j)
  have hBst : star B = B := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ((data.current m j).2).adjoint_eq]
  have hApst : star Ap = Ap := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ((data.current (data.reverse m) i).2).adjoint_eq]
  have hsecond :
      (data.density m).expectation (B * heisenbergEvolution U t A) =
        (data.density (data.reverse m)).expectation
          (Ap * heisenbergEvolution Up t Bp) := by
    calc
      _ = star ((data.density m).expectation
          (heisenbergEvolution U t A * B)) := by
        rw [← (data.density m).expectation_star, star_mul, hBst]
        rw [star_evolved_of_selfAdjoint
          (data.system m) A ((data.current m i).2) t]
      _ = star ((data.density (data.reverse m)).expectation
          (heisenbergEvolution Up t Bp * Ap)) := by rw [hfirst]
      _ = (data.density (data.reverse m)).expectation
          (Ap * heisenbergEvolution Up t Bp) := by
        rw [← (data.density (data.reverse m)).expectation_star, star_mul, hApst]
        rw [star_evolved_of_selfAdjoint
          (data.system (data.reverse m)) Bp
          ((data.current (data.reverse m) j).2) t]
  rw [map_sub, map_sub, hfirst, hsecond]

/-- The physical contact response is reciprocal as a consequence of
operator covariance and Hermiticity, not a scalar reciprocity axiom. -/
theorem contact_expectation_reverse (m : M) (i j : d) :
    (data.density m).expectation ((data.contact m i j).1) =
      (data.density (data.reverse m)).expectation
        ((data.contact (data.reverse m) j i).1) := by
  have hself : star ((data.contact m i j).1) = (data.contact m i j).1 := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ((data.contact m i j).2).adjoint_eq]
  calc
    (data.density m).expectation ((data.contact m i j).1) =
        star ((data.density m).expectation ((data.contact m i j).1)) := by
      rw [← (data.density m).expectation_star, hself]
    _ = (data.density (data.reverse m)).expectation
          (data.timeReversal.conjugateOperator ((data.contact m i j).1)) :=
      (data.expectation_reverse m _).symm
    _ = (data.density (data.reverse m)).expectation
          ((data.contact (data.reverse m) j i).1) := by
      rw [data.contact_reverse m i j]

/-- Onsager–Casimir reciprocity of the canonical Kubo commutator
susceptibility, without defining another current-specific response kernel. -/
theorem commutatorSusceptibility_reverse (m : M) (i j : d) (t : ℝ) :
    commutatorSusceptibility
      (freePropagatorGroup (data.system m)) (data.system m).hbar
      (data.density m).toNormalizedExpectation
      ((data.current m i).1) ((data.current m j).1) t 0 =
    commutatorSusceptibility
      (freePropagatorGroup (data.system (data.reverse m)))
      (data.system (data.reverse m)).hbar
      (data.density (data.reverse m)).toNormalizedExpectation
      ((data.current (data.reverse m) j).1)
      ((data.current (data.reverse m) i).1) t 0 := by
  simp only [commutatorSusceptibility, heisenbergEvolution_zero,
    LieRing.of_associative_ring_bracket, DensityOperator.toNormalizedExpectation_apply]
  rw [data.system_hbar m, data.system_hbar (data.reverse m),
    data.current_commutator_reverse m i j t]

/-- Finite-time conductivity constructed from the existing Kubo susceptibility
and finite-time adiabatic transform, with the physical contact correction. -/
noncomputable def conductivityFamily
    (volume : PositiveVolume) (omega eta duration : ℝ) :
    M → ConductivityTensor d :=
  fun m =>
    { component := fun i j =>
        (finiteTimeAdiabaticTransform
          (fun t => commutatorSusceptibility
            (freePropagatorGroup (data.system m)) (data.system m).hbar
            (data.density m).toNormalizedExpectation
            ((data.current m i).1) ((data.current m j).1) t 0)
          omega eta duration +
          (data.density m).expectation ((data.contact m i j).1)) *
        finiteVolumeConductivityNormalization volume omega eta }

/-- Onsager–Casimir reciprocity is proved without an eigenbasis pairing
assumption or a postulated equality of conductivity components. -/
theorem conductivityFamily_isOnsagerReciprocal
    (volume : PositiveVolume) (omega eta duration : ℝ) :
    ConductivityTensor.IsOnsagerReciprocal
      (data.conductivityFamily volume omega eta duration) data.reverse := by
  intro m i j
  have hkernel :
      (fun t : ℝ => commutatorSusceptibility
          (freePropagatorGroup (data.system m)) (data.system m).hbar
          (data.density m).toNormalizedExpectation
          ((data.current m i).1) ((data.current m j).1) t 0) =
      (fun t : ℝ => commutatorSusceptibility
          (freePropagatorGroup (data.system (data.reverse m)))
          (data.system (data.reverse m)).hbar
          (data.density (data.reverse m)).toNormalizedExpectation
          ((data.current (data.reverse m) j).1)
          ((data.current (data.reverse m) i).1) t 0) := by
    funext t
    exact data.commutatorSusceptibility_reverse m i j t
  change
    (finiteTimeAdiabaticTransform
      (fun t => commutatorSusceptibility
        (freePropagatorGroup (data.system m)) (data.system m).hbar
        (data.density m).toNormalizedExpectation
        ((data.current m i).1) ((data.current m j).1) t 0) omega eta duration +
      (data.density m).expectation ((data.contact m i j).1)) *
      finiteVolumeConductivityNormalization volume omega eta =
    (finiteTimeAdiabaticTransform
      (fun t => commutatorSusceptibility
        (freePropagatorGroup (data.system (data.reverse m)))
        (data.system (data.reverse m)).hbar
        (data.density (data.reverse m)).toNormalizedExpectation
        ((data.current (data.reverse m) j).1)
        ((data.current (data.reverse m) i).1) t 0) omega eta duration +
      (data.density (data.reverse m)).expectation
        ((data.contact (data.reverse m) j i).1)) *
      finiteVolumeConductivityNormalization volume omega eta
  rw [hkernel, data.contact_expectation_reverse m i j]

end KuboTimeReversalData

end
end QuantumTheory.Transport
