import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.VertexLabel

set_option linter.style.header false

/-!
# Bosonic quartic interaction vertices

A quartic vertex carries two creation modes and two annihilation modes. The operator order is fixed
as `a†_{create₁} a†_{create₂} a_{annihilate₂} a_{annihilate₁}`, matching the fermionic quartic
vertex convention while using bosonic ladder operators.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*}

/-- Compatibility alias for the statistics-independent quartic vertex label. -/
abbrev QuarticVertexLabel (Mode : Type*) := Common.QuarticVertexLabel Mode

/-- The ordered bosonic quartic vertex operator. -/
noncomputable def quarticVertexOperator (q : QuarticVertexLabel Mode) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (create q.create₁).comp
    ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁)))

/-- The finite bosonic quartic interaction with coupling `g`. -/
noncomputable def quarticInteraction [Fintype Mode] (g : QuarticVertexLabel Mode → ℂ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  ∑ q, g q • quarticVertexOperator q

/-- A single bosonic quartic vertex evolves by its total free-energy shift. -/
theorem interactionPicture_quarticVertexOperator (ε : Mode → ℝ) (q : QuarticVertexLabel Mode)
    (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      Complex.exp (((τ : ℂ)) * ((ε q.create₁ : ℂ) + (ε q.create₂ : ℂ) -
        (ε q.annihilate₁ : ℂ) - (ε q.annihilate₂ : ℂ))) • quarticVertexOperator q := by
  change imaginaryTimeEvolve ε τ (quarticVertexOperator q) = _
  have hcomp : imaginaryTimeEvolve ε τ (quarticVertexOperator q) =
      (imaginaryTimeEvolve ε τ (create q.create₁)).comp
        ((imaginaryTimeEvolve ε τ (create q.create₂)).comp
          ((imaginaryTimeEvolve ε τ (annihilate q.annihilate₂)).comp
            (imaginaryTimeEvolve ε τ (annihilate q.annihilate₁)))) := by
    simp only [quarticVertexOperator, imaginaryTimeEvolve_comp]
  rw [hcomp, imaginaryTimeEvolve_create, imaginaryTimeEvolve_create,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_annihilate]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  rw [show (create q.create₁).comp
      ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁))) =
      quarticVertexOperator q from rfl]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- The interaction picture distributes over the finite sum of bosonic quartic vertices. -/
theorem interactionPicture_quarticInteraction [Fintype Mode] (ε : Mode → ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (τ : ℝ) :
    interactionPicture ε (quarticInteraction g) τ =
      ∑ q, g q • interactionPicture ε (quarticVertexOperator q) τ := by
  change imaginaryTimeEvolve ε τ (quarticInteraction g) = _
  rw [quarticInteraction]
  change Common.heisenbergEvolve (freeEigenvalue ε) τ
    (∑ q, g q • quarticVertexOperator q) = _
  rw [Common.heisenbergEvolve_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Common.heisenbergEvolve_smul]
  rfl

end Bosonic
end SecondQuantization
