import LeanCondensedMatter.SecondQuantization.Common.Interaction.Quartic
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture

set_option linter.style.header false

/-!
# Imaginary-time evolution of generic quartic interactions

The quartic interaction constructors are owned by `Common.Interaction.Quartic`. This module contains
the generic diagonal Heisenberg-evolution results for quartic local legs and vertices.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Mode Config : Type*}

namespace QuarticLocalLeg

/-- A local quartic leg assembled from ladder eigenoperators evolves with its signed energy shift. -/
theorem heisenbergEvolve_operator
    (energy : Config → ℝ) (ε : Mode → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (leg : QuarticLocalLeg Mode) (τ : ℝ)
    (hcreate : ∀ i, heisenbergEvolve energy τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i)
    (hannihilate : ∀ i, heisenbergEvolve energy τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i) :
    heisenbergEvolve energy τ (leg.operator create annihilate) =
      Complex.exp (((τ * leg.energyShift ε : ℝ) : ℂ)) •
        leg.operator create annihilate := by
  cases leg <;> simp [hcreate, hannihilate, mul_comm]

end QuarticLocalLeg

/-- Scalar imaginary-time factor carried by one quartic vertex. -/
noncomputable def quarticVertexTimeFactor (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (τ : ℝ) : ℂ :=
  Complex.exp ((τ : ℂ) * (quarticVertexEnergyShift ε q : ℂ))

/-- Product of the scalar imaginary-time factors of a finite quartic-vertex sequence. -/
noncomputable def quarticVertexSequenceTimeFactor {n : ℕ}
    (ε : Mode → ℝ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) : ℂ :=
  ∏ i, quarticVertexTimeFactor ε (q i) (τ i)

/-- Prepending a vertex and its time prepends the corresponding scalar factor. -/
@[simp]
theorem quarticVertexSequenceTimeFactor_cons {n : ℕ}
    (ε : Mode → ℝ) (q0 : QuarticVertexLabel Mode)
    (q : Fin n → QuarticVertexLabel Mode) (σ : ℝ) (τ : Fin n → ℝ) :
    quarticVertexSequenceTimeFactor ε (Fin.cons q0 q) (Fin.cons σ τ) =
      quarticVertexTimeFactor ε q0 σ * quarticVertexSequenceTimeFactor ε q τ := by
  rw [quarticVertexSequenceTimeFactor, Fin.prod_univ_succ]
  simp [quarticVertexSequenceTimeFactor]

/-- A quartic vertex assembled from ladder eigenoperators evolves with their total energy shift. -/
theorem heisenbergEvolve_quarticVertexOperator
    (energy : Config → ℝ) (ε : Mode → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) (τ : ℝ)
    (hcreate : ∀ i, heisenbergEvolve energy τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i)
    (hannihilate : ∀ i, heisenbergEvolve energy τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i) :
    heisenbergEvolve energy τ (quarticVertexOperator create annihilate q) =
      quarticVertexTimeFactor ε q τ • quarticVertexOperator create annihilate q := by
  simp only [quarticVertexOperator, quarticVertexTimeFactor, ← Module.End.mul_eq_comp, map_mul]
  rw [hcreate, hcreate, hannihilate, hannihilate]
  simp only [Module.End.mul_eq_comp, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [quarticVertexEnergyShift]
  push_cast
  ring

/-- Ordered interaction-picture product of a finite quartic-vertex sequence. Coordinate zero is
the outermost/latest operator, matching the ordered-simplex convention used by Dyson expansion. -/
noncomputable def quarticVertexSequenceInteractionPicture
    (energy : Config → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    (n : ℕ) → (Fin n → QuarticVertexLabel Mode) → (Fin n → ℝ) →
      AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config
  | 0, _, _ => LinearMap.id
  | _ + 1, q, τ =>
      (interactionPicture energy (quarticVertexOperator create annihilate (q 0)) (τ 0)).comp
        (quarticVertexSequenceInteractionPicture energy create annihilate _
          (fun i => q i.succ) (fun i => τ i.succ))

@[simp]
theorem quarticVertexSequenceInteractionPicture_zero
    (energy : Config → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : Fin 0 → QuarticVertexLabel Mode) (τ : Fin 0 → ℝ) :
    quarticVertexSequenceInteractionPicture energy create annihilate 0 q τ = LinearMap.id := rfl

theorem quarticVertexSequenceInteractionPicture_succ
    (energy : Config → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (n : ℕ) (q : Fin (n + 1) → QuarticVertexLabel Mode) (τ : Fin (n + 1) → ℝ) :
    quarticVertexSequenceInteractionPicture energy create annihilate (n + 1) q τ =
      (interactionPicture energy (quarticVertexOperator create annihilate (q 0)) (τ 0)).comp
        (quarticVertexSequenceInteractionPicture energy create annihilate n
          (fun i => q i.succ) (fun i => τ i.succ)) := rfl

theorem quarticVertexSequenceInteractionPicture_cons
    (energy : Config → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (n : ℕ) (q0 : QuarticVertexLabel Mode) (q : Fin n → QuarticVertexLabel Mode)
    (σ : ℝ) (τ : Fin n → ℝ) :
    quarticVertexSequenceInteractionPicture energy create annihilate (n + 1)
        (Fin.cons q0 q) (Fin.cons σ τ) =
      (interactionPicture energy (quarticVertexOperator create annihilate q0) σ).comp
        (quarticVertexSequenceInteractionPicture energy create annihilate n q τ) := by
  rw [quarticVertexSequenceInteractionPicture_succ]
  simp

/-- A finitely supported quartic interaction evolves as the finite sum of its bare vertices with
scalar vertex time factors, provided the ladder operators obey the stated free evolution laws. -/
theorem heisenbergEvolve_quarticInteractionOn_eq_sum
    (energy : Config → ℝ) (ε : Mode → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (support : Finset (QuarticVertexLabel Mode)) (g : QuarticVertexLabel Mode → ℂ) (τ : ℝ)
    (hcreate : ∀ i, heisenbergEvolve energy τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i)
    (hannihilate : ∀ i, heisenbergEvolve energy τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i) :
    heisenbergEvolve energy τ (quarticInteractionOn support create annihilate g) =
      ∑ q : ↥support,
        (g q * quarticVertexTimeFactor ε q τ) • quarticVertexOperator create annihilate q := by
  classical
  have hinteraction :
      quarticInteractionOn support create annihilate g =
        ∑ q : ↥support, g q • quarticVertexOperator create annihilate q := by
    change (∑ q ∈ support, g q • quarticVertexOperator create annihilate q) = _
    rw [← Finset.sum_subtype support (fun _ => Iff.rfl)
      (fun q => g q • quarticVertexOperator create annihilate q)]
  rw [hinteraction, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, heisenbergEvolve_quarticVertexOperator energy ε create annihilate
    (q : QuarticVertexLabel Mode) τ hcreate hannihilate]
  simp [smul_smul]

end
end Common
end SecondQuantization
