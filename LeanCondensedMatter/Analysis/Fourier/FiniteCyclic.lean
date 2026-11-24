import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

set_option linter.style.header false

/-!
# Normalized Fourier modes on a finite cyclic group

The positive-exponent convention uses the standard additive character of `ZMod N`.
The inner product is the counting-measure inner product of `EuclideanSpace`.
-/

open scoped BigOperators InnerProductSpace

namespace AddChar

/-- Distinct characters of a finite abelian group, normalized for the counting-measure
inner product on Euclidean space, form an orthonormal family. Mathlib supplies the
character orthogonality for the average inner product. -/
theorem orthonormal_normalized_family {G ι : Type*} [AddCommGroup G] [Fintype G]
    (χ : ι → AddChar G ℂ) (hχ : Function.Injective χ) :
    Orthonormal ℂ (fun q => (WithLp.toLp 2 fun j : G =>
      (Real.sqrt (Fintype.card G) : ℂ)⁻¹ * χ q j : EuclideanSpace ℂ G)) := by
  classical
  rw [orthonormal_iff_ite]
  intro q r
  have h := AddChar.wInner_cWeight_eq_boole (χ q) (χ r)
  simp only [hχ.eq_iff] at h
  rw [← h]
  have hsq : (Real.sqrt (Fintype.card G) : ℂ) ^ 2 = Fintype.card G := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card G))
  have hscale : (Real.sqrt (Fintype.card G) : ℂ)⁻¹ *
      (Real.sqrt (Fintype.card G) : ℂ)⁻¹ = (Fintype.card G : ℂ)⁻¹ := by
    rw [← pow_two, inv_pow, hsq]
  simp only [PiLp.inner_apply, RCLike.wInner, RCLike.cWeight, Function.const_apply,
    RCLike.inner_apply, map_mul, map_inv₀, Complex.conj_ofReal,
    RCLike.real_smul_eq_coe_mul]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ((Real.sqrt (Fintype.card G) : ℂ)⁻¹ *
        (Real.sqrt (Fintype.card G) : ℂ)⁻¹) *
        (χ r j * (starRingEnd ℂ) (χ q j)) := by ring
    _ = _ := by
      rw [hscale]
      change _ = ((Fintype.card G : ℝ) : ℂ)⁻¹ *
        (χ r j * (starRingEnd ℂ) (χ q j))
      rw [Complex.ofReal_natCast]

end AddChar

namespace ZMod

noncomputable section
variable {N : ℕ} [NeZero N]

/-- The normalized positive-exponent Fourier mode on a finite cyclic group. -/
def fourierMode (q : ZMod N) : EuclideanSpace ℂ (ZMod N) :=
  WithLp.toLp 2 fun j => (Real.sqrt N : ℂ)⁻¹ * stdAddChar (q * j)

theorem orthonormal_fourierMode : Orthonormal ℂ (fourierMode (N := N)) := by
  have hχ : Function.Injective (fun q : ZMod N => stdAddChar.mulShift q) := by
    intro q r h
    apply injective_stdAddChar
    simpa only [AddChar.mulShift_apply, mul_one] using
      congrArg (fun ψ : AddChar (ZMod N) ℂ => ψ 1) h
  unfold fourierMode
  simpa only [ZMod.card, AddChar.mulShift_apply] using
    AddChar.orthonormal_normalized_family (fun q : ZMod N => stdAddChar.mulShift q) hχ

/-- The normalized Fourier modes as a complete orthonormal basis. -/
def fourierBasis : OrthonormalBasis (ZMod N) ℂ (EuclideanSpace ℂ (ZMod N)) :=
  (basisOfOrthonormalOfCardEqFinrank orthonormal_fourierMode
    (by simp)).toOrthonormalBasis (by
      simpa using (orthonormal_fourierMode (N := N)))

theorem fourierBasis_apply (q : ZMod N) : fourierBasis q = fourierMode q := by
  simp [fourierBasis]

end
end ZMod
