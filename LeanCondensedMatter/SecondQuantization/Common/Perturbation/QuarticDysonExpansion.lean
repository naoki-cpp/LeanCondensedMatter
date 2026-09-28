import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic

set_option linter.style.header false

/-!
# Quartic Dyson sequence helpers

Statistics-independent scalar and interaction-picture identities used when a finitely supported
quartic interaction is expanded into fixed vertex-label sequences.  Particle-statistics-specific
layers provide concrete ladder operators and their free imaginary-time eigenoperator laws.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Mode Config : Type*}

/-- The scalar time factor of a fixed vertex sequence is jointly continuous. -/
theorem continuous_quarticVertexSequenceTimeFactor {n : ℕ}
    (ε : Mode → ℝ) (q : Fin n → QuarticVertexLabel Mode) :
    Continuous (quarticVertexSequenceTimeFactor ε q) := by
  unfold quarticVertexSequenceTimeFactor quarticVertexTimeFactor
  exact continuous_finsetProd _ fun i _ =>
    Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_apply i))).mul continuous_const)

/-- The one-vertex scalar time factor is continuous in imaginary time. -/
theorem continuous_quarticVertexTimeFactor
    (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) :
    Continuous (quarticVertexTimeFactor ε q) := by
  unfold quarticVertexTimeFactor
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- Scalar coefficient of one fixed vertex-label sequence in a quartic Dyson expansion. -/
noncomputable def quarticDysonSequenceCoeff {n : ℕ}
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) (t : ℝ) : ℂ :=
  ((-1 : ℂ) ^ n * ∏ i, g (q i)) *
    intervalIntegral.orderedSimplexIntegral n t (quarticVertexSequenceTimeFactor ε q)

/-- A fixed vertex-sequence Dyson coefficient is continuous in its upper imaginary-time bound. -/
theorem continuous_quarticDysonSequenceCoeff {n : ℕ}
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) :
    Continuous (quarticDysonSequenceCoeff ε g q) := by
  have hintegrand : Continuous (Function.uncurry
      (fun (_ : ℝ) (τ : Fin n → ℝ) => quarticVertexSequenceTimeFactor ε q τ)) :=
    (continuous_quarticVertexSequenceTimeFactor ε q).comp continuous_snd
  have hsimplex :=
    intervalIntegral.continuous_orderedSimplexIntegral_of_continuous n id
      (fun (_ : ℝ) τ => quarticVertexSequenceTimeFactor ε q τ)
      continuous_id hintegrand
  change Continuous (fun t : ℝ =>
    ((-1 : ℂ) ^ n * ∏ i, g (q i)) *
      intervalIntegral.orderedSimplexIntegral n t (quarticVertexSequenceTimeFactor ε q))
  exact continuous_const.mul hsimplex

/-- Prepending a vertex gives the outer-time recursion for a fixed-sequence Dyson coefficient. -/
theorem quarticDysonSequenceCoeff_cons {n : ℕ}
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (q0 : QuarticVertexLabel Mode) (q : Fin n → QuarticVertexLabel Mode) (t : ℝ) :
    quarticDysonSequenceCoeff ε g (Fin.cons q0 q) t =
      -∫ σ in (0 : ℝ)..t,
        (g q0 * quarticVertexTimeFactor ε q0 σ) *
          quarticDysonSequenceCoeff ε g q σ := by
  have hsimplex :
      intervalIntegral.orderedSimplexIntegral (n + 1) t
          (quarticVertexSequenceTimeFactor ε (Fin.cons q0 q)) =
        ∫ σ in (0 : ℝ)..t,
          quarticVertexTimeFactor ε q0 σ *
            intervalIntegral.orderedSimplexIntegral n σ
              (quarticVertexSequenceTimeFactor ε q) := by
    rw [intervalIntegral.orderedSimplexIntegral_succ]
    apply intervalIntegral.integral_congr
    intro σ _
    calc
      intervalIntegral.orderedSimplexIntegral n σ
          (fun rest => quarticVertexSequenceTimeFactor ε (Fin.cons q0 q)
            (Fin.cons σ rest)) =
        intervalIntegral.orderedSimplexIntegral n σ
          (fun rest =>
            quarticVertexTimeFactor ε q0 σ * quarticVertexSequenceTimeFactor ε q rest) := by
              apply intervalIntegral.orderedSimplexIntegral_congr
              intro rest
              exact quarticVertexSequenceTimeFactor_cons ε q0 q σ rest
      _ = quarticVertexTimeFactor ε q0 σ *
          intervalIntegral.orderedSimplexIntegral n σ
            (quarticVertexSequenceTimeFactor ε q) :=
        intervalIntegral.orderedSimplexIntegral_smul n σ
          (quarticVertexTimeFactor ε q0 σ) (quarticVertexSequenceTimeFactor ε q)
  simp only [quarticDysonSequenceCoeff]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hsimplex]
  have hrewrite :
      (fun σ : ℝ =>
        (g q0 * quarticVertexTimeFactor ε q0 σ) *
          (((-1 : ℂ) ^ n * ∏ i, g (q i)) *
            intervalIntegral.orderedSimplexIntegral n σ
              (quarticVertexSequenceTimeFactor ε q))) =
      (fun σ : ℝ =>
        (g q0 * ((-1 : ℂ) ^ n * ∏ i, g (q i))) *
          (quarticVertexTimeFactor ε q0 σ *
            intervalIntegral.orderedSimplexIntegral n σ
              (quarticVertexSequenceTimeFactor ε q))) := by
    funext σ
    ring
  rw [hrewrite, intervalIntegral.integral_const_mul]
  ring


end
end Common
end SecondQuantization
