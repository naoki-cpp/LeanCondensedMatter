import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

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
  have hSG : S * G = 1 := by
    simpa [S, G] using spectralShift_mul_resolvent_of_not_mem operator z hz
  have hGS : G * S = 1 := by
    simpa [S, G] using resolvent_mul_spectralShift_of_not_mem operator z hz
  have hS_v : S v = (z - eigenvalue) • v := by
    change z • v - operator v = _
    rw [hv]
    exact (sub_smul z eigenvalue v).symm
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
    S (G v) = v := by
      change (S * G) v = v
      rw [hSG]
      simp
    _ = S ((z - eigenvalue)⁻¹ • v) := by
      rw [map_smul, hS_v, ← mul_smul]
      simp [hshift]

end

end QuantumTheory
