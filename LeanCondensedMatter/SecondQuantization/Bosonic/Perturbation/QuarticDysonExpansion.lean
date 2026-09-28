import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion

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

/-- The scalar time factor of a fixed vertex sequence is jointly continuous. -/
private theorem continuous_quarticVertexSequenceTimeFactor {n : ℕ}
    (ε : Mode → ℝ) (q : Fin n → QuarticVertexLabel Mode) :
    Continuous (quarticVertexSequenceTimeFactor ε q) := by
  unfold quarticVertexSequenceTimeFactor quarticVertexTimeFactor
  exact continuous_finsetProd _ fun i _ =>
    Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_apply i))).mul continuous_const)

/-- The one-vertex scalar time factor is continuous in imaginary time. -/
private theorem continuous_quarticVertexTimeFactor
    (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) :
    Continuous (quarticVertexTimeFactor ε q) := by
  unfold quarticVertexTimeFactor
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- Scalar coefficient of one fixed vertex-label sequence in the finite-order quartic Dyson
expansion. The ordered-simplex integral contains all imaginary-time dependence; the coupling
product and Dyson sign are finite algebraic factors. -/
noncomputable def quarticDysonSequenceCoeff {n : ℕ}
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) (t : ℝ) : ℂ :=
  ((-1 : ℂ) ^ n * ∏ i, g (q i)) *
    intervalIntegral.orderedSimplexIntegral n t (quarticVertexSequenceTimeFactor ε q)

/-- A fixed vertex-sequence Dyson coefficient is continuous in its upper imaginary-time bound. -/
private theorem continuous_quarticDysonSequenceCoeff {n : ℕ}
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

/-- The fixed-sequence coefficient obeys the same outer-time recursion as the Dyson expansion:
prepending a vertex contributes its coupling and free-evolution scalar, while the extra Dyson
vertex contributes the minus sign. -/
private theorem quarticDysonSequenceCoeff_cons {n : ℕ}
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

/-- A finitely supported interaction-picture quartic interaction is the finite sum of its bare
vertices, with all time dependence exposed as scalar factors. -/
private theorem interactionPicture_quarticInteractionOn_eq_sum
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ) (τ : ℝ) :
    interactionPicture ε (quarticInteractionOn support g) τ =
      ∑ q : ↥support,
        (g q * quarticVertexTimeFactor ε q τ) • quarticVertexOperator q := by
  classical
  have hinteraction :
      quarticInteractionOn support g =
        ∑ q : ↥support, g q • quarticVertexOperator q := by
    change (∑ q ∈ support, g q • quarticVertexOperator q) = _
    rw [← Finset.sum_subtype support (fun _ => Iff.rfl)
      (fun q => g q • quarticVertexOperator q)]
  rw [hinteraction]
  change Common.heisenbergEvolve (freeEigenvalue ε) τ
      (∑ q : ↥support, g q • quarticVertexOperator q) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul]
  change g (q : QuarticVertexLabel Mode) •
      interactionPicture ε (quarticVertexOperator (q : QuarticVertexLabel Mode)) τ =
    (g q * quarticVertexTimeFactor ε q τ) • quarticVertexOperator q
  rw [interactionPicture_quarticVertexOperator_eq_smul]
  simp [smul_smul]

/-- The actual arbitrary-occupation-space Dyson coefficient of a finitely supported quartic
interaction is a finite sum over support-valued vertex-label sequences. Each summand is a static
bare operator product multiplied by its scalar ordered-simplex Dyson coefficient.

This identity is proved before taking any infinite bosonic Gibbs sum, so it requires no
sum/integral interchange assumption from `FreeGibbsDysonIntegralBoundary`, and the ambient mode
type itself need not be finite. -/
theorem dysonCoeff_quarticInteractionOn_eq_sum
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ∀ (n : ℕ) (t : ℝ),
      Common.dysonCoeff (freeEigenvalue ε) (quarticInteractionOn support g) n t =
        ∑ q : Fin n → ↥support,
          quarticDysonSequenceCoeff ε g
              (fun i => (q i : QuarticVertexLabel Mode)) t •
            Common.quarticVertexSequenceOperator create annihilate
              (fun i => (q i : QuarticVertexLabel Mode)) := by
  classical
  intro n
  induction n with
  | zero =>
      intro t
      rw [Common.dysonCoeff_zero]
      have huniq : Unique (Fin 0 → ↥support) := Pi.uniqueOfIsEmpty _
      rw [Fintype.sum_unique]
      simp [quarticDysonSequenceCoeff, Common.quarticVertexSequenceOperator,
        quarticVertexSequenceTimeFactor, Module.End.one_eq_id]
  | succ n ih =>
      intro t
      apply Common.matrixCoeff_ext
      intro m k
      change
        Common.dysonCoeff (freeEigenvalue ε) (quarticInteractionOn support g) (n + 1) t
            (Common.basisState k) m =
          Common.matrixCoeff
            (∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t •
                Common.quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) m k
      rw [Common.dysonCoeff_succ_basisState_apply]
      change
        -∫ σ in (0 : ℝ)..t,
            Common.matrixCoeff
              ((interactionPicture ε (quarticInteractionOn support g) σ).comp
                (Common.dysonCoeff (freeEigenvalue ε) (quarticInteractionOn support g) n σ)) m k =
          Common.matrixCoeff
            (∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t •
                Common.quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) m k
      let e : ↥support × (Fin n → ↥support) ≃ (Fin (n + 1) → ↥support) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun q => (q 0, fun i => q i.succ)
          left_inv := fun p => by simp
          right_inv := fun q => by funext i; refine Fin.cases ?_ ?_ i <;> simp }
      have hcomp (σ : ℝ) :
          (interactionPicture ε (quarticInteractionOn support g) σ).comp
              (Common.dysonCoeff (freeEigenvalue ε) (quarticInteractionOn support g) n σ) =
            ∑ q0 : ↥support,
              ∑ q' : Fin n → ↥support,
                ((g q0 * quarticVertexTimeFactor ε q0 σ) *
                    quarticDysonSequenceCoeff ε g
                      (fun i => (q' i : QuarticVertexLabel Mode)) σ) •
                  Common.quarticVertexSequenceOperator create annihilate
                    (Fin.cons (q0 : QuarticVertexLabel Mode)
                      (fun i => (q' i : QuarticVertexLabel Mode))) := by
        rw [interactionPicture_quarticInteractionOn_eq_sum, ih σ]
        ext x
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
          Finsupp.finsetSum_apply, Common.quarticVertexSequenceOperator_cons]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q0 _ => ?_
        refine Finset.sum_congr rfl fun q' _ => ?_
        simp [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul, mul_assoc]
        ring
      have hpoint (σ : ℝ) :
          Common.matrixCoeff
              ((interactionPicture ε (quarticInteractionOn support g) σ).comp
                (Common.dysonCoeff (freeEigenvalue ε) (quarticInteractionOn support g) n σ)) m k =
            ∑ q : Fin (n + 1) → ↥support,
              ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
                  quarticDysonSequenceCoeff ε g
                    (fun i => (q i.succ : QuarticVertexLabel Mode)) σ) *
                Common.matrixCoeff
                  (Common.quarticVertexSequenceOperator create annihilate
                    (fun i => (q i : QuarticVertexLabel Mode))) m k := by
        rw [hcomp σ]
        change (Common.matrixCoeffLinear m k)
            (∑ q0 : ↥support,
              ∑ q' : Fin n → ↥support,
                ((g q0 * quarticVertexTimeFactor ε q0 σ) *
                    quarticDysonSequenceCoeff ε g
                      (fun i => (q' i : QuarticVertexLabel Mode)) σ) •
                  Common.quarticVertexSequenceOperator create annihilate
                    (Fin.cons (q0 : QuarticVertexLabel Mode)
                      (fun i => (q' i : QuarticVertexLabel Mode)))) = _
        rw [map_sum]
        simp only [map_sum, map_smul, Common.matrixCoeffLinear_apply, smul_eq_mul]
        rw [← Fintype.sum_prod_type']
        rw [← Equiv.sum_comp e (fun q : Fin (n + 1) → ↥support =>
          ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
              quarticDysonSequenceCoeff ε g
                (fun i => (q i.succ : QuarticVertexLabel Mode)) σ) *
            Common.matrixCoeff
              (quarticVertexSequenceOperator
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
          Common.matrixCoeff
            ((interactionPicture ε (quarticInteractionOn support g) σ).comp
              (Common.dysonCoeff (freeEigenvalue ε) (quarticInteractionOn support g) n σ)) m k) =
        (fun σ : ℝ =>
          ∑ q : Fin (n + 1) → ↥support,
            ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
                quarticDysonSequenceCoeff ε g
                  (fun i => (q i.succ : QuarticVertexLabel Mode)) σ) *
              Common.matrixCoeff
                (Common.quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) m k) by
          funext σ
          exact hpoint σ]
      have hintegrability : ∀ q : Fin (n + 1) → ↥support,
          IntervalIntegrable
            (fun σ : ℝ =>
              ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
                  quarticDysonSequenceCoeff ε g
                    (fun i => (q i.succ : QuarticVertexLabel Mode)) σ) *
                Common.matrixCoeff
                  (Common.quarticVertexSequenceOperator create annihilate
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
          Common.matrixCoeff
            (∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t •
                Common.quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) m k =
            ∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t *
                Common.matrixCoeff
                  (Common.quarticVertexSequenceOperator create annihilate
                    (fun i => (q i : QuarticVertexLabel Mode))) m k := by
        change (Common.matrixCoeffLinear m k)
            (∑ q : Fin (n + 1) → ↥support,
              quarticDysonSequenceCoeff ε g
                  (fun i => (q i : QuarticVertexLabel Mode)) t •
                Common.quarticVertexSequenceOperator create annihilate
                  (fun i => (q i : QuarticVertexLabel Mode))) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [map_smul, Common.matrixCoeffLinear_apply]
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
end Bosonic
end SecondQuantization
