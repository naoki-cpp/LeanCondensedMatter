import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticGibbsSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-Gibbs summability of the first Dyson coefficient

On diagonal occupation matrix coefficients, free interaction-picture conjugation is invisible.  The
first Dyson integral therefore contributes only the scalar interval length to the diagonal
coefficient.  Consequently any interaction with a summable free-Gibbs numerator has a summable
first Dyson coefficient.  Combined with the quartic summability theorem, this supplies the concrete
`coeff_mem` slice at Dyson order one without commuting an infinite Gibbs sum with an integral.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

omit [Fintype Mode] in
/-- The diagonal matrix coefficient of the first arbitrary-configuration Dyson coefficient is the
bare diagonal coefficient multiplied by the signed interval length. -/
theorem matrixCoeff_infiniteDysonCoeff_one_self
    (ε : Mode → ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (t : ℝ) (n : Occupation Mode) :
    Common.matrixCoeff
        (Common.infiniteDysonCoeff (freeEigenvalue ε) V 1 t) n n =
      -(t : ℂ) * Common.matrixCoeff V n n := by
  change Common.infiniteDysonCoeff (freeEigenvalue ε) V 1 t (Common.basisState n) n = _
  rw [show 1 = 0 + 1 by omega,
    Common.infiniteDysonCoeff_succ_basisState_apply]
  simp only [Common.infiniteDysonCoeff_zero, LinearMap.id_apply]
  have hdiag : ∀ σ : ℝ,
      interactionPicture ε V σ (Common.basisState n) n = Common.matrixCoeff V n n := by
    intro σ
    change Common.matrixCoeff (interactionPicture ε V σ) n n = Common.matrixCoeff V n n
    rw [matrixCoeff_interactionPicture]
    simp
  simp_rw [hdiag]
  simp

omit [Fintype Mode] in
/-- The first Dyson coefficient's full free-Gibbs numerator is a fixed scalar multiple of the bare
interaction numerator, pointwise in occupation number. -/
theorem matrixCoeff_freeGibbs_infiniteDysonCoeff_one_self
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (t : ℝ) (n : Occupation Mode) :
    Common.matrixCoeff
        ((imaginaryTimeEvolveFree ε (-β)).comp
          (Common.infiniteDysonCoeff (freeEigenvalue ε) V 1 t)) n n =
      -(t : ℂ) *
        Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp V) n n := by
  rw [matrixCoeff_imaginaryTimeEvolveFree_comp,
    matrixCoeff_infiniteDysonCoeff_one_self,
    matrixCoeff_imaginaryTimeEvolveFree_comp]
  ring

omit [Fintype Mode] in
/-- Free-Gibbs summability of an interaction implies free-Gibbs summability of its first Dyson
coefficient.  No expectation/integral interchange is used. -/
theorem freeGibbsSummable_infiniteDysonCoeff_one
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (t : ℝ) (hV : freeGibbsSummable ε β V) :
    freeGibbsSummable ε β
      (Common.infiniteDysonCoeff (freeEigenvalue ε) V 1 t) := by
  unfold freeGibbsSummable at hV ⊢
  have h := hV.mul_left (-(t : ℂ))
  exact h.congr fun n =>
    (matrixCoeff_freeGibbs_infiniteDysonCoeff_one_self ε β V t n).symm

omit [Fintype Mode] in
/-- Domain form of `freeGibbsSummable_infiniteDysonCoeff_one`. -/
theorem infiniteDysonCoeff_one_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (t : ℝ) (hV : V ∈ freeGibbsDomain ε β) :
    Common.infiniteDysonCoeff (freeEigenvalue ε) V 1 t ∈ freeGibbsDomain ε β :=
  freeGibbsSummable_infiniteDysonCoeff_one ε β V t hV

/-- The first Dyson coefficient of a finitely supported quartic interaction belongs to the free-Gibbs
domain under positive one-mode Boltzmann exponents. -/
theorem infiniteDysonCoeff_one_quarticInteractionOn_mem_freeGibbsDomain
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (t : ℝ) :
    Common.infiniteDysonCoeff (freeEigenvalue ε) (quarticInteractionOn support g) 1 t ∈
      freeGibbsDomain ε β :=
  infiniteDysonCoeff_one_mem_freeGibbsDomain ε β (quarticInteractionOn support g) t
    (quarticInteractionOn_mem_freeGibbsDomain support ε β hpos g)

/-- On a finite mode type, the first Dyson coefficient of the all-label quartic interaction belongs
to the free-Gibbs domain. -/
theorem infiniteDysonCoeff_one_quarticInteraction_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (t : ℝ) :
    Common.infiniteDysonCoeff (freeEigenvalue ε) (quarticInteraction g) 1 t ∈
      freeGibbsDomain ε β :=
  infiniteDysonCoeff_one_mem_freeGibbsDomain ε β (quarticInteraction g) t
    (quarticInteraction_mem_freeGibbsDomain ε β hpos g)

end
end Bosonic
end SecondQuantization
