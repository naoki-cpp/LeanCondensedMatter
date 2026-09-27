import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic

set_option linter.style.header false

/-!
# Quartic bosonic Dyson expansion

A bosonic quartic vertex is an eigenoperator of the free imaginary-time evolution.  This makes the
time dependence of a fixed vertex sequence purely scalar: each vertex contributes the exponential
of its free-energy shift, while the operator product itself is time independent.

This file isolates that physical structure before any Gibbs expectation is taken.  The resulting
finite vertex-sequence expansion is the route from the actual algebraic Dyson coefficient to the
ordered-simplex diagram layer; in particular it does not require interchanging an infinite bosonic
Gibbs sum with an interval integral.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

/-- Scalar imaginary-time factor carried by one quartic vertex. -/
noncomputable def quarticVertexTimeFactor (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (τ : ℝ) : ℂ :=
  Complex.exp ((τ : ℂ) * (quarticVertexEnergyShift ε q : ℂ))

/-- A single quartic vertex evolves by its scalar free-energy-shift factor. -/
theorem interactionPicture_quarticVertexOperator_eq_smul
    (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      quarticVertexTimeFactor ε q τ • quarticVertexOperator q := by
  simpa [interactionPicture, quarticVertexOperator, imaginaryTimeEvolve,
    quarticVertexTimeFactor] using
    (Common.heisenbergEvolve_quarticVertexOperator
      (freeEigenvalue ε) ε create annihilate q τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

/-- Ordered product of a finite sequence of bare quartic vertex operators. -/
noncomputable def quarticVertexSequenceOperator {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (List.ofFn fun i => quarticVertexOperator (q i)).prod

@[simp]
theorem quarticVertexSequenceOperator_zero
    (q : Fin 0 → QuarticVertexLabel Mode) :
    quarticVertexSequenceOperator q =
      (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) := by
  simp [quarticVertexSequenceOperator, Module.End.one_eq_id]

/-- Prepending one vertex prepends its operator by composition. -/
theorem quarticVertexSequenceOperator_cons {n : ℕ}
    (q0 : QuarticVertexLabel Mode) (q : Fin n → QuarticVertexLabel Mode) :
    quarticVertexSequenceOperator (Fin.cons q0 q) =
      (quarticVertexOperator q0).comp (quarticVertexSequenceOperator q) := by
  simp [quarticVertexSequenceOperator, Module.End.mul_eq_comp]

/-- Product of all scalar imaginary-time factors in a fixed vertex sequence. -/
noncomputable def quarticVertexSequenceTimeFactor {n : ℕ}
    (ε : Mode → ℝ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) : ℂ :=
  ∏ i, quarticVertexTimeFactor ε (q i) (τ i)

@[simp]
theorem quarticVertexSequenceTimeFactor_zero
    (ε : Mode → ℝ) (q : Fin 0 → QuarticVertexLabel Mode) (τ : Fin 0 → ℝ) :
    quarticVertexSequenceTimeFactor ε q τ = 1 := by
  simp [quarticVertexSequenceTimeFactor]

/-- Prepending a vertex and its time prepends the corresponding scalar time factor. -/
theorem quarticVertexSequenceTimeFactor_cons {n : ℕ}
    (ε : Mode → ℝ) (q0 : QuarticVertexLabel Mode)
    (q : Fin n → QuarticVertexLabel Mode) (σ : ℝ) (τ : Fin n → ℝ) :
    quarticVertexSequenceTimeFactor ε (Fin.cons q0 q) (Fin.cons σ τ) =
      quarticVertexTimeFactor ε q0 σ * quarticVertexSequenceTimeFactor ε q τ := by
  rw [quarticVertexSequenceTimeFactor, Fin.prod_univ_succ]
  simp [quarticVertexSequenceTimeFactor]

/-- The scalar time factor of a fixed vertex sequence is jointly continuous. -/
theorem continuous_quarticVertexSequenceTimeFactor {n : ℕ}
    (ε : Mode → ℝ) (q : Fin n → QuarticVertexLabel Mode) :
    Continuous (quarticVertexSequenceTimeFactor ε q) := by
  unfold quarticVertexSequenceTimeFactor quarticVertexTimeFactor
  exact continuous_finsetProd _ fun i _ =>
    Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_apply i))).mul continuous_const)

/-- The ordered product of interaction-picture vertices factors into a scalar time factor and the
corresponding bare ordered vertex product. -/
theorem quarticVertexSequenceInteractionPicture_eq_smul (ε : Mode → ℝ) :
    ∀ {n : ℕ} (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ),
      (List.ofFn fun i => interactionPicture ε (quarticVertexOperator (q i)) (τ i)).prod =
        quarticVertexSequenceTimeFactor ε q τ • quarticVertexSequenceOperator q
  | 0, q, τ => by
      simp [quarticVertexSequenceOperator, quarticVertexSequenceTimeFactor,
        Module.End.one_eq_id]
  | n + 1, q, τ => by
      rw [List.ofFn_succ, List.prod_cons,
        interactionPicture_quarticVertexOperator_eq_smul,
        quarticVertexSequenceInteractionPicture_eq_smul ε
          (fun i => q i.succ) (fun i => τ i.succ)]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [quarticVertexSequenceOperator]
      simp only [List.ofFn_succ, List.prod_cons]
      congr 1
      rw [quarticVertexSequenceTimeFactor, Fin.prod_univ_succ]
      rfl

end
end Bosonic
end SecondQuantization
