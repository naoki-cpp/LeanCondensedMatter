import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.NoncommRing

set_option linter.style.header false

/-! # Exponential conjugation and commutator intertwining

A continuous linear map intertwining commutators with two fixed generators also intertwines
their exponential conjugations. Multiplicativity of the map is not required.
-/

open NormedSpace
open scoped Topology

noncomputable section

variable {A B : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

/-- Exponential conjugation solves the commutator evolution equation. -/
theorem hasDerivAt_exp_conjugate (a b : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • a) * b * exp (-(s • a)))
      (a * (exp (t • a) * b * exp (-(t • a))) -
        (exp (t • a) * b * exp (-(t • a))) * a) t := by
  have hc : Commute a (exp (-(t • a))) := by
    apply Commute.exp_right
    change a * (-(t • a)) = (-(t • a)) * a
    simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
  have h := ((hasDerivAt_exp_smul_const' a t).mul_const b).mul
    (hasDerivAt_exp_smul_const' (-a) t)
  simp only [smul_neg] at h
  convert h using 1
  rw [neg_mul, hc.eq]
  noncomm_ring

/-- Intertwining commutators with fixed generators implies intertwining their exponential
conjugations. This applies to continuous realizations of Lie algebra homomorphisms. -/
theorem ContinuousLinearMap.map_exp_conjugate_of_commutator
    (F : A →L[ℝ] B) (a : A) (c : B)
    (hF : ∀ x, F (a * x - x * a) = c * F x - F x * c)
    (b : A) (t : ℝ) :
    F (exp (t • a) * b * exp (-(t • a))) =
      exp (t • c) * F b * exp (-(t • c)) := by
  let X (s : ℝ) := exp (s • a) * b * exp (-(s • a))
  let g (s : ℝ) := exp (s • (-c)) * F (X s) * exp (s • c)
  have hg (s : ℝ) : HasDerivAt g 0 s := by
    have hX := F.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_exp_conjugate a b s)
    have hc : Commute c (exp (s • (-c))) := by
      apply Commute.exp_right
      change c * (s • (-c)) = (s • (-c)) * c
      simp only [smul_neg, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
    have h := ((hasDerivAt_exp_smul_const' (-c) s).mul hX).mul
      (hasDerivAt_exp_smul_const' c s)
    have hzero :
        (((-c) * exp (s • (-c))) * F (X s) +
            exp (s • (-c)) * (c * F (X s) - F (X s) * c)) * exp (s • c) +
          (exp (s • (-c)) * F (X s)) * (c * exp (s • c)) = 0 := by
      rw [neg_mul, hc.eq]
      noncomm_ring
    simp only [Function.comp_def, hF] at h
    exact h.congr_deriv hzero
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  have heq : exp (-(t • c)) * F (X t) * exp (t • c) = F b := by
    simpa [g, X, smul_neg] using hconst
  have hunit (z : B) : exp z * exp (-z) = 1 := by
    letI : NormedAlgebra ℚ B := .restrictScalars ℚ ℝ B
    have hz : Commute z (-z) := by
      change z * (-z) = (-z) * z
      simp only [mul_neg, neg_mul]
    rw [← exp_add_of_commute hz, add_neg_cancel, exp_zero]
  change F (X t) = _
  calc
    F (X t) = (exp (t • c) * exp (-(t • c))) * F (X t) *
        (exp (t • c) * exp (-(t • c))) := by simp only [hunit, one_mul, mul_one]
    _ = exp (t • c) * (exp (-(t • c)) * F (X t) * exp (t • c)) *
        exp (-(t • c)) := by simp only [mul_assoc]
    _ = exp (t • c) * F b * exp (-(t • c)) := by rw [heq]

end
