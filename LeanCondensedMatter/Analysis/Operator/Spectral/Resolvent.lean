module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

public section

set_option linter.style.header false

/-!
# Generic spectral facts for bounded resolvents

This module owns representation-independent facts about the resolvent of a bounded complex operator.
It contains no retarded/advanced convention, broadening parameter, transport observable, or concrete
Hamiltonian model.
-/

namespace QuantumTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonreal scalar cannot belong to the spectrum of a self-adjoint bounded operator. -/
theorem not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
    (operator : H →L[ℂ] H) (hself : IsSelfAdjoint operator)
    (z : ℂ) (hz : z.im ≠ 0) :
    z ∉ spectrum ℂ operator := by
  intro hmem
  exact hz (IsSelfAdjoint.im_eq_zero_of_mem_spectrum
    (A := H →L[ℂ] H) hself hmem)

omit [CompleteSpace H] in
/-- Outside the spectrum, the shifted operator multiplied by the resolvent is the identity. -/
theorem spectralShift_mul_resolvent_of_not_mem
    (operator : H →L[ℂ] H) (z : ℂ) (hz : z ∉ spectrum ℂ operator) :
    (algebraMap ℂ (H →L[ℂ] H) z - operator) * resolvent operator z = 1 := by
  have hres : z ∈ resolventSet ℂ operator := spectrum.notMem_iff.mp hz
  rw [spectrum.resolvent_eq hres]
  exact hres.mul_val_inv

omit [CompleteSpace H] in
/-- Outside the spectrum, the resolvent multiplied by the shifted operator is the identity. -/
theorem resolvent_mul_spectralShift_of_not_mem
    (operator : H →L[ℂ] H) (z : ℂ) (hz : z ∉ spectrum ℂ operator) :
    resolvent operator z * (algebraMap ℂ (H →L[ℂ] H) z - operator) = 1 := by
  have hres : z ∈ resolventSet ℂ operator := spectrum.notMem_iff.mp hz
  rw [spectrum.resolvent_eq hres]
  exact hres.val_inv_mul

omit [CompleteSpace H] in
/-- Outside the spectrum, any right inverse of the spectral shift equals the canonical resolvent. -/
theorem resolvent_eq_of_spectralShift_mul_eq_one_of_not_mem
    (operator candidate : H →L[ℂ] H) (z : ℂ)
    (hz : z ∉ spectrum ℂ operator)
    (hleft : (algebraMap ℂ (H →L[ℂ] H) z - operator) * candidate = 1) :
    resolvent operator z = candidate := by
  have hright := resolvent_mul_spectralShift_of_not_mem operator z hz
  calc
    resolvent operator z = resolvent operator z * 1 := by simp
    _ = resolvent operator z *
        ((algebraMap ℂ (H →L[ℂ] H) z - operator) * candidate) := by rw [hleft]
    _ = (resolvent operator z *
        (algebraMap ℂ (H →L[ℂ] H) z - operator)) * candidate := by rw [mul_assoc]
    _ = candidate := by rw [hright, one_mul]

/-- A finite family of diagonal action identities gives a right inverse when the
corresponding projectors resolve the identity and all eigenvalues are nonzero. -/
theorem mul_sum_inv_smul_eq_one_of_diagonal_action
    {A ι : Type*} [Semiring A] [Algebra ℂ A] [Fintype ι]
    (S : A) (P : ι → A) (d : ι → ℂ)
    (hcomplete : ∑ i, P i = 1)
    (haction : ∀ i, S * P i = d i • P i)
    (hne : ∀ i, d i ≠ 0) :
    S * (∑ i, (d i)⁻¹ • P i) = 1 := by
  calc
    S * (∑ i, (d i)⁻¹ • P i) = ∑ i, P i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_smul_comm, haction i, smul_smul]
      simp [hne i]
    _ = 1 := hcomplete

/-- Squaring a finite linear combination of orthogonal idempotents squares its coefficients. -/
theorem sum_smul_sq_of_orthogonalIdempotents
    {A ι : Type*} [Semiring A] [Algebra ℂ A] [Fintype ι]
    (P : ι → A) (hP : OrthogonalIdempotents P) (c : ι → ℂ) :
    (∑ i, c i • P i) ^ 2 = ∑ i, c i ^ 2 • P i := by
  classical
  simp [pow_two, Finset.sum_mul, Finset.mul_sum, smul_smul, hP.mul_eq]

omit [CompleteSpace H] in
/-- A finite resolution of the identity by eigenoperators gives the canonical resolvent.
Orthogonality is not needed: completeness and the diagonal action suffice. -/
theorem resolvent_eq_sum_inv_smul_of_diagonal_action
    {ι : Type*} [Fintype ι]
    (operator : H →L[ℂ] H) (P : ι → H →L[ℂ] H) (eigenvalue : ι → ℂ)
    (hcomplete : ∑ i, P i = 1)
    (haction : ∀ i, operator * P i = eigenvalue i • P i)
    (z : ℂ) (hz : z ∉ spectrum ℂ operator)
    (hne : ∀ i, z - eigenvalue i ≠ 0) :
    resolvent operator z = ∑ i, (z - eigenvalue i)⁻¹ • P i := by
  apply resolvent_eq_of_spectralShift_mul_eq_one_of_not_mem operator _ z hz
  apply mul_sum_inv_smul_eq_one_of_diagonal_action
      (algebraMap ℂ (H →L[ℂ] H) z - operator) P
      (fun i => z - eigenvalue i) hcomplete
  · intro i
    rw [sub_mul, haction i]
    simp [Algebra.algebraMap_eq_smul_one, sub_smul]
  · exact hne

omit [CompleteSpace H] in
/-- A resolvent acts on an eigenvector by the scalar resolvent factor. No self-adjointness is needed;
only exclusion of the spectral parameter from the spectrum and the corresponding nonzero scalar
shift. -/
theorem resolvent_apply_eigenvector
    (operator : H →L[ℂ] H) (z eigenvalue : ℂ) {v : H}
    (hz : z ∉ spectrum ℂ operator) (hshift : z - eigenvalue ≠ 0)
    (hv : operator v = eigenvalue • v) :
    resolvent operator z v = (z - eigenvalue)⁻¹ • v := by
  let S : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - operator
  let G : H →L[ℂ] H := resolvent operator z
  have hGS : G * S = 1 := by
    simpa [S, G] using resolvent_mul_spectralShift_of_not_mem operator z hz
  have hS_v : S v = (z - eigenvalue) • v := by
    change z • v - operator v = _
    rw [hv]
    exact (sub_smul z eigenvalue v).symm
  have hscalar : (z - eigenvalue) • G v = v := by
    calc
      (z - eigenvalue) • G v = G ((z - eigenvalue) • v) :=
        (map_smul G (z - eigenvalue) v).symm
      _ = G (S v) := congrArg G hS_v.symm
      _ = (G * S) v := rfl
      _ = v := by rw [hGS]; simp
  calc
    G v = (z - eigenvalue)⁻¹ • ((z - eigenvalue) • G v) := by
      rw [smul_smul, inv_mul_cancel₀ hshift, one_smul]
    _ = (z - eigenvalue)⁻¹ • v := by rw [hscalar]

end

end QuantumTheory
