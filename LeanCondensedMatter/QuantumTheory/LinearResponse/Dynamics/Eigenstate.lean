import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Free
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option linter.style.header false

/-! # Free evolution of individual energy eigenvectors

The free phase and matrix-element law require only the two eigenvector equations,
not a complete eigenbasis or a probability distribution over it.
-/
namespace QuantumTheory.LinearResponse
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- A real-energy eigenvector acquires its Schrödinger phase under free evolution. -/
theorem freePropagator_apply_of_eigenvector (vector : H) (energy : ℝ)
    (heigen : system.hamiltonian.1 vector = (energy : ℂ) • vector) (t : ℝ) :
    freePropagator system t vector =
      Complex.exp (-(Complex.I * (((t * energy) / system.hbar : ℝ) : ℂ))) • vector := by
  let T : H →L[ℂ] H := (t : ℂ) • schrodingerGenerator system
  let c : ℂ := -(Complex.I * (((t * energy) / system.hbar : ℝ) : ℂ))
  let v : H := vector
  have hT : T v = c • v := by
    dsimp [T, c, v]
    rw [schrodingerGenerator]
    simp only [smul_apply, heigen, smul_smul]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t
      ((-(Complex.I / (system.hbar : ℂ)) * (energy : ℂ)) • vector)]
    rw [smul_smul]
    apply congrArg (fun z : ℂ => z • vector)
    push_cast
    simp only [div_eq_mul_inv, neg_mul, mul_neg]
    apply congrArg (fun z : ℂ => -z)
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hpow (n : ℕ) : (T ^ n) v = c ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        simp only [mul_apply_eq_comp, ih, map_smul, hT, smul_smul]
        congr 1
        ring
  have hop :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T).mapL
      (ContinuousLinearMap.apply ℂ H v)
  have hop' : HasSum
      (fun n : ℕ => (((n.factorial : ℂ)⁻¹ * c ^ n) • v))
      (freePropagator system t v) := by
    rw [freePropagator_eq_exp]
    convert hop using 1
    · ext n
      simp only [ContinuousLinearMap.apply_apply, smul_apply]
      rw [hpow]
      simp [c, v, smul_smul]
    · rfl
  have hscalar :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).mapL
      (ContinuousLinearMap.toSpanSingleton ℂ v)
  have hscalar' : HasSum
      (fun n : ℕ => (((n.factorial : ℂ)⁻¹ * c ^ n) • v))
      (Complex.exp (-(Complex.I * (((t * energy) / system.hbar : ℝ) : ℂ))) • v) := by
    convert hscalar using 1
    · ext n
      simp
    · simp [Complex.exp_eq_exp_ℂ, c, v]
  exact hop'.unique hscalar'

/-- A Heisenberg matrix element between two real-energy eigenvectors has their relative phase. -/
theorem inner_heisenbergEvolution_of_eigenvectors
    (initial final : H) (energyInitial energyFinal : ℝ)
    (hinitial : system.hamiltonian.1 initial = (energyInitial : ℂ) • initial)
    (hfinal : system.hamiltonian.1 final = (energyFinal : ℂ) • final)
    (A : H →L[ℂ] H) (t : ℝ) :
    inner ℂ final (heisenbergEvolution (freePropagatorGroup system) t A initial) =
      Complex.exp (Complex.I * ((((energyFinal - energyInitial) * t) /
        system.hbar : ℝ) : ℂ)) * inner ℂ final (A initial) := by
  rw [heisenbergEvolution_freePropagatorGroup_apply]
  simp only [mul_apply_eq_comp]
  rw [freePropagator_apply_of_eigenvector system initial energyInitial hinitial t,
    map_smul, ← star_freePropagator system t, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,
    freePropagator_apply_of_eigenvector system final energyFinal hfinal t]
  simp only [inner_smul_left, inner_smul_right]
  have hphase :
      star (Complex.exp (-(Complex.I * (((t * energyFinal) / system.hbar : ℝ) : ℂ)))) *
        Complex.exp (-(Complex.I * (((t * energyInitial) / system.hbar : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((((energyFinal - energyInitial) * t) /
        system.hbar : ℝ) : ℂ)) := by
    simp only [Complex.exp_eq_exp_ℂ]
    rw [NormedSpace.star_exp, ← NormedSpace.exp_add]
    congr 1
    simp
    ring
  calc
    _ = (star (Complex.exp (-(Complex.I * (((t * energyFinal) / system.hbar : ℝ) : ℂ)))) *
        Complex.exp (-(Complex.I * (((t * energyInitial) / system.hbar : ℝ) : ℂ)))) *
        inner ℂ final (A initial) := by ring
    _ = _ := by rw [hphase]

end
end QuantumTheory.LinearResponse
