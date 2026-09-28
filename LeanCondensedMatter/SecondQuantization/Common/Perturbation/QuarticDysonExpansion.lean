import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion

set_option linter.style.header false

/-!
# Quartic Dyson sequence helpers

Statistics-independent scalar and ordered-simplex identities used when a quartic Dyson expansion is
resolved into fixed vertex-label sequences. Particle-statistics-specific layers provide the concrete
interaction operators whose Dyson coefficients consume these helpers.
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


/-- The finite-order Dyson coefficient of a finitely supported quartic interaction is the sum over
support-valued vertex sequences of their scalar ordered-simplex coefficients multiplying the
corresponding bare vertex products. This is statistics-independent once the ladder operators obey
the stated free imaginary-time eigenoperator laws. -/
theorem dysonCoeff_quarticInteractionOn_eq_sum
    (energy : Config → ℝ) (ε : Mode → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (support : Finset (QuarticVertexLabel Mode)) (g : QuarticVertexLabel Mode → ℂ)
    (hcreate : ∀ τ i, heisenbergEvolve energy τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i)
    (hannihilate : ∀ τ i, heisenbergEvolve energy τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i) :
    ∀ (n : ℕ) (t : ℝ),
      dysonCoeff energy (quarticInteractionOn support create annihilate g) n t =
        ∑ q : Fin n → ↥support,
          quarticDysonSequenceCoeff ε g
              (fun i => (q i : QuarticVertexLabel Mode)) t •
            quarticVertexSequenceOperator create annihilate
              (fun i => (q i : QuarticVertexLabel Mode)) := by
  classical
  intro n
  induction n with
  | zero =>
      intro t
      rw [dysonCoeff_zero]
      have huniq : Unique (Fin 0 → ↥support) := Pi.uniqueOfIsEmpty _
      rw [Fintype.sum_unique]
      simp [quarticDysonSequenceCoeff, quarticVertexSequenceOperator,
        quarticVertexSequenceTimeFactor, Module.End.one_eq_id]
  | succ n ih =>
      intro t
      apply matrixCoeff_ext
      intro m k
      change
        dysonCoeff energy (quarticInteractionOn support create annihilate g) (n + 1) t
            (basisState k) m =
          matrixCoeff
            (∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t •
                quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) m k
      rw [dysonCoeff_succ_basisState_apply]
      change
        -∫ σ in (0 : ℝ)..t,
            matrixCoeff
              ((interactionPicture energy (quarticInteractionOn support create annihilate g) σ).comp
                (dysonCoeff energy (quarticInteractionOn support create annihilate g) n σ)) m k =
          matrixCoeff
            (∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t •
                quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) m k
      let e : ↥support × (Fin n → ↥support) ≃ (Fin (n + 1) → ↥support) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun q => (q 0, fun i => q i.succ)
          left_inv := fun p => by simp
          right_inv := fun q => by funext i; refine Fin.cases ?_ ?_ i <;> simp }
      have hcomp (σ : ℝ) :
          (interactionPicture energy (quarticInteractionOn support create annihilate g) σ).comp
              (dysonCoeff energy (quarticInteractionOn support create annihilate g) n σ) =
            ∑ q0 : ↥support,
              ∑ q' : Fin n → ↥support,
                ((g q0 * quarticVertexTimeFactor ε q0 σ) *
                    quarticDysonSequenceCoeff ε g
                      (fun i => (q' i : QuarticVertexLabel Mode)) σ) •
                  quarticVertexSequenceOperator create annihilate
                    (Fin.cons (q0 : QuarticVertexLabel Mode)
                      (fun i => (q' i : QuarticVertexLabel Mode))) := by
        change
          (heisenbergEvolve energy σ (quarticInteractionOn support create annihilate g)).comp
              (dysonCoeff energy (quarticInteractionOn support create annihilate g) n σ) = _
        rw [heisenbergEvolve_quarticInteractionOn_eq_sum energy ε create annihilate
          support g σ (hcreate σ) (hannihilate σ), ih σ]
        ext x
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
          Finsupp.finsetSum_apply, quarticVertexSequenceOperator_cons]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q0 _ => ?_
        refine Finset.sum_congr rfl fun q' _ => ?_
        simp [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul, mul_assoc]
        ring
      have hpoint (σ : ℝ) :
          matrixCoeff
              ((interactionPicture energy (quarticInteractionOn support create annihilate g) σ).comp
                (dysonCoeff energy (quarticInteractionOn support create annihilate g) n σ)) m k =
            ∑ q : Fin (n + 1) → ↥support,
              ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
                  quarticDysonSequenceCoeff ε g
                    (fun i => (q i.succ : QuarticVertexLabel Mode)) σ) *
                matrixCoeff
                  (quarticVertexSequenceOperator create annihilate
                    (fun i => (q i : QuarticVertexLabel Mode))) m k := by
        rw [hcomp σ]
        change (matrixCoeffLinear m k)
            (∑ q0 : ↥support,
              ∑ q' : Fin n → ↥support,
                ((g q0 * quarticVertexTimeFactor ε q0 σ) *
                    quarticDysonSequenceCoeff ε g
                      (fun i => (q' i : QuarticVertexLabel Mode)) σ) •
                  quarticVertexSequenceOperator create annihilate
                    (Fin.cons (q0 : QuarticVertexLabel Mode)
                      (fun i => (q' i : QuarticVertexLabel Mode)))) = _
        rw [map_sum]
        simp only [map_sum, map_smul, matrixCoeffLinear_apply, smul_eq_mul]
        rw [← Fintype.sum_prod_type']
        rw [← Equiv.sum_comp e (fun q : Fin (n + 1) → ↥support =>
          ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
              quarticDysonSequenceCoeff ε g
                (fun i => (q i.succ : QuarticVertexLabel Mode)) σ) *
            matrixCoeff
              (quarticVertexSequenceOperator create annihilate
                (fun i => (q i : QuarticVertexLabel Mode))) m k)]
        refine Finset.sum_congr rfl fun p _ => ?_
        obtain ⟨q0, q'⟩ := p
        have hseq :
            Fin.cons (q0 : QuarticVertexLabel Mode)
                (fun i => (q' i : QuarticVertexLabel Mode)) =
              (fun i : Fin (n + 1) =>
                (((Fin.cons q0 q' : Fin (n + 1) → ↥support) i) :
                  QuarticVertexLabel Mode)) := by
          funext i
          refine Fin.cases ?_ ?_ i <;> simp
        rw [hseq]
        rfl
      rw [show
        (fun σ : ℝ =>
          matrixCoeff
            ((interactionPicture energy (quarticInteractionOn support create annihilate g) σ).comp
              (dysonCoeff energy (quarticInteractionOn support create annihilate g) n σ)) m k) =
        (fun σ : ℝ =>
          ∑ q : Fin (n + 1) → ↥support,
            ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
                quarticDysonSequenceCoeff ε g
                  (fun i => (q i.succ : QuarticVertexLabel Mode)) σ) *
              matrixCoeff
                (quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) m k) by
          funext σ
          exact hpoint σ]
      have hintegrability : ∀ q : Fin (n + 1) → ↥support,
          IntervalIntegrable
            (fun σ : ℝ =>
              ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
                  quarticDysonSequenceCoeff ε g
                    (fun i => (q i.succ : QuarticVertexLabel Mode)) σ) *
                matrixCoeff
                  (quarticVertexSequenceOperator create annihilate
                    (fun i => (q i : QuarticVertexLabel Mode))) m k)
            MeasureTheory.volume 0 t := by
        intro q
        exact ((((continuous_const.mul
          (continuous_quarticVertexTimeFactor ε (q 0))).mul
            (continuous_quarticDysonSequenceCoeff ε g
              (fun i => (q i.succ : QuarticVertexLabel Mode)))).mul
              continuous_const).intervalIntegrable 0 t)
      rw [intervalIntegral.integral_finsetSum (fun q _ => hintegrability q)]
      have hright :
          matrixCoeff
            (∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t •
                quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) m k =
            ∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t *
                matrixCoeff
                  (quarticVertexSequenceOperator create annihilate
                    (fun i => (q i : QuarticVertexLabel Mode))) m k := by
        change (matrixCoeffLinear m k)
            (∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t •
                quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [map_smul, matrixCoeffLinear_apply]
        rfl
      rw [hright, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [intervalIntegral.integral_mul_const]
      have hq :
          Fin.cons (q 0 : QuarticVertexLabel Mode)
              (fun i => (q i.succ : QuarticVertexLabel Mode)) =
            (fun i => (q i : QuarticVertexLabel Mode)) := by
        funext i
        refine Fin.cases ?_ ?_ i <;> simp
      have hcoeff :=
        quarticDysonSequenceCoeff_cons ε g (q 0 : QuarticVertexLabel Mode)
          (fun i => (q i.succ : QuarticVertexLabel Mode)) t
      rw [hq] at hcoeff
      rw [hcoeff]
      ring

end
end Common
end SecondQuantization
