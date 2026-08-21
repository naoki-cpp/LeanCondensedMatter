import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsBoundary

set_option linter.style.header false

/-!
# Free Gibbs summability and interaction-picture evolution

At first Dyson order the recursive product is the interaction-picture interaction composed with the
zeroth Dyson coefficient, hence just the interaction-picture interaction itself.  Its free Gibbs
numerator has exactly the same diagonal coefficients as the original interaction: conjugation by
the free diagonal evolution contributes opposite phases on the same occupation state.

This file proves that fact directly on the genuinely infinite occupation space.  It supplies the
first nontrivial piece of `FreeGibbsDysonIntegralBoundary.integrand_mem` from ordinary Gibbs
summability of the interaction, without any finite occupation-basis assumption.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

omit [Fintype Mode] in
/-- Coordinate formula for the free diagonal evolution on an arbitrary algebraic-Fock vector. -/
private theorem imaginaryTimeEvolveFree_apply_coord
    (ε : Mode → ℝ) (τ : ℝ) (x : FockSpace Mode) (n : Occupation Mode) :
    imaginaryTimeEvolveFree ε τ x n =
      Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) * x n := by
  let eval : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply n
  have hmap : eval.comp (imaginaryTimeEvolveFree ε τ) =
      Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) • eval := by
    apply Finsupp.lhom_ext
    intro a b
    have hb : (Finsupp.single a b : FockSpace Mode) = b • basisState a :=
      (Finsupp.smul_single_one a b).symm
    rw [hb, LinearMap.comp_apply, map_smul, imaginaryTimeEvolveFree_basisState]
    simp only [map_smul, LinearMap.smul_apply, eval, Finsupp.lapply_apply, smul_eq_mul]
    by_cases h : a = n
    · subst a
      have hself : (basisState n : FockSpace Mode) n = 1 := by
        simp [basisState, Common.basisState]
      rw [hself]
    · have hne : (basisState a : FockSpace Mode) n = 0 := by
        simp [basisState, Common.basisState, h]
      rw [hne]
      simp
  have hx := congrArg (fun L => L x) hmap
  simpa only [eval, LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
    smul_eq_mul] using hx

omit [Fintype Mode] in
/-- Left composition by the free diagonal evolution rescales a matrix coefficient by the output
occupation's Boltzmann phase. -/
theorem matrixCoeff_imaginaryTimeEvolveFree_comp
    (ε : Mode → ℝ) (τ : ℝ) (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (m n : Occupation Mode) :
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε τ).comp A) m n =
      Complex.exp ((τ * freeEigenvalue ε m : ℝ) : ℂ) * Common.matrixCoeff A m n := by
  rw [Common.matrixCoeff, LinearMap.comp_apply, imaginaryTimeEvolveFree_apply_coord]
  rfl

omit [Fintype Mode] in
/-- The diagonal free-Gibbs numerator is invariant under interaction-picture conjugation. -/
theorem matrixCoeff_freeGibbs_interactionPicture_self
    (ε : Mode → ℝ) (β σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (n : Occupation Mode) :
    Common.matrixCoeff
        ((imaginaryTimeEvolveFree ε (-β)).comp (interactionPicture ε V σ)) n n =
      Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp V) n n := by
  rw [matrixCoeff_imaginaryTimeEvolveFree_comp,
    matrixCoeff_imaginaryTimeEvolveFree_comp, interactionPicture,
    Common.matrixCoeff_interactionPicture]
  simp

omit [Fintype Mode] in
/-- Free Gibbs summability is preserved by free interaction-picture conjugation. -/
theorem freeGibbsSummable_interactionPicture_iff
    (ε : Mode → ℝ) (β σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsSummable ε β (interactionPicture ε V σ) ↔ freeGibbsSummable ε β V := by
  unfold freeGibbsSummable
  constructor <;> intro h
  · exact h.congr fun n => matrixCoeff_freeGibbs_interactionPicture_self ε β σ V n
  · exact h.congr fun n => (matrixCoeff_freeGibbs_interactionPicture_self ε β σ V n).symm

omit [Fintype Mode] in
/-- The normalized free Gibbs expectation is invariant under free interaction-picture conjugation.
This equality is pointwise on the diagonal numerator, so no extra summability hypothesis is needed
for the equality itself. -/
theorem freeGibbsExpectation_interactionPicture
    (ε : Mode → ℝ) (β σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β (interactionPicture ε V σ) = freeGibbsExpectation ε β V := by
  unfold freeGibbsExpectation Common.tsumTrace
  congr 1
  exact tsum_congr fun n => matrixCoeff_freeGibbs_interactionPicture_self ε β σ V n

omit [Fintype Mode] in
/-- At first Dyson order, summability of the bare interaction automatically supplies the recursive
Gibbs-domain closure condition because the zeroth Dyson coefficient is the identity. -/
theorem firstDysonIntegrand_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (hV : V ∈ freeGibbsDomain ε β) :
    (interactionPicture ε V σ).comp
        (Common.dysonCoeff (freeEigenvalue ε) V 0 σ) ∈ freeGibbsDomain ε β := by
  rw [Common.dysonCoeff_zero, LinearMap.comp_id]
  exact (freeGibbsSummable_interactionPicture_iff ε β σ V).2 hV

end
end Bosonic
end SecondQuantization
