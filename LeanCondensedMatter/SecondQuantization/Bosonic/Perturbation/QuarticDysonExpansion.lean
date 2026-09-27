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

/-- Scalar imaginary-time factor carried by one quartic vertex. -/
noncomputable def quarticVertexTimeFactor (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (τ : ℝ) : ℂ :=
  Complex.exp ((τ : ℂ) * (quarticVertexEnergyShift ε q : ℂ))

/-- A single quartic vertex evolves by its scalar free-energy-shift factor. -/
theorem interactionPicture_quarticVertexOperator_eq_smul
    (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      quarticVertexTimeFactor ε q τ • quarticVertexOperator q := by
  change Common.heisenbergEvolve (freeEigenvalue ε) τ (quarticVertexOperator q) =
    quarticVertexTimeFactor ε q τ • quarticVertexOperator q
  simpa [quarticVertexOperator, quarticVertexTimeFactor] using
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
      congr 1
      · have hq : Fin.cons (q 0) (fun i => q i.succ) = q := by
          change Fin.cons (q 0) (Fin.tail q) = q
          exact Fin.cons_self_tail q
        have hτ : Fin.cons (τ 0) (fun i => τ i.succ) = τ := by
          change Fin.cons (τ 0) (Fin.tail τ) = τ
          exact Fin.cons_self_tail τ
        simpa [mul_comm, hq, hτ] using
          (quarticVertexSequenceTimeFactor_cons ε (q 0) (fun i => q i.succ)
            (τ 0) (fun i => τ i.succ)).symm
      · rw [Module.End.mul_eq_comp]
        rw [← quarticVertexSequenceOperator_cons
          (q0 := q 0) (q := fun i => q i.succ)]
        congr
        funext i
        refine Fin.cases ?_ ?_ i <;> simp


/-- The one-vertex scalar time factor is continuous in imaginary time. -/
theorem continuous_quarticVertexTimeFactor
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

/-- The fixed-sequence coefficient obeys the same outer-time recursion as the Dyson expansion:
prepending a vertex contributes its coupling and free-evolution scalar, while the extra Dyson
vertex contributes the minus sign. -/
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

/-- The interaction-picture quartic interaction is the finite sum of its bare vertices, with all
time dependence exposed as scalar factors. -/
theorem interactionPicture_quarticInteraction_eq_sum [Fintype Mode]
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ) (τ : ℝ) :
    interactionPicture ε (quarticInteraction g) τ =
      ∑ q : QuarticVertexLabel Mode,
        (g q * quarticVertexTimeFactor ε q τ) • quarticVertexOperator q := by
  classical
  change Common.heisenbergEvolve (freeEigenvalue ε) τ
      (∑ q : QuarticVertexLabel Mode, g q • quarticVertexOperator q) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul]
  change g q • interactionPicture ε (quarticVertexOperator q) τ =
    (g q * quarticVertexTimeFactor ε q τ) • quarticVertexOperator q
  rw [interactionPicture_quarticVertexOperator_eq_smul]
  simp [smul_smul]

/-- The actual arbitrary-occupation-space Dyson coefficient of the finite-mode quartic interaction
is a finite sum over vertex-label sequences. Each summand is a static bare operator product
multiplied by its scalar ordered-simplex Dyson coefficient.

This identity is proved before taking any infinite bosonic Gibbs sum, so it requires no
sum/integral interchange assumption from `FreeGibbsDysonIntegralBoundary`. -/
theorem dysonCoeff_quarticInteraction_eq_sum [Fintype Mode]
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ∀ (n : ℕ) (t : ℝ),
      Common.dysonCoeff (freeEigenvalue ε) (quarticInteraction g) n t =
        ∑ q : Fin n → QuarticVertexLabel Mode,
          quarticDysonSequenceCoeff ε g q t • quarticVertexSequenceOperator q := by
  classical
  intro n
  induction n with
  | zero =>
      intro t
      rw [Common.dysonCoeff_zero]
      have huniq : Unique (Fin 0 → QuarticVertexLabel Mode) := Pi.uniqueOfIsEmpty _
      rw [Fintype.sum_unique]
      simp [quarticDysonSequenceCoeff]
  | succ n ih =>
      intro t
      apply Common.matrixCoeff_ext
      intro m k
      change
        Common.dysonCoeff (freeEigenvalue ε) (quarticInteraction g) (n + 1) t
            (Common.basisState k) m =
          Common.matrixCoeff
            (∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
              quarticDysonSequenceCoeff ε g q t • quarticVertexSequenceOperator q) m k
      rw [Common.dysonCoeff_succ_basisState_apply]
      change
        -∫ σ in (0 : ℝ)..t,
            Common.matrixCoeff
              ((interactionPicture ε (quarticInteraction g) σ).comp
                (Common.dysonCoeff (freeEigenvalue ε) (quarticInteraction g) n σ)) m k =
          Common.matrixCoeff
            (∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
              quarticDysonSequenceCoeff ε g q t • quarticVertexSequenceOperator q) m k
      let e : QuarticVertexLabel Mode × (Fin n → QuarticVertexLabel Mode) ≃
          (Fin (n + 1) → QuarticVertexLabel Mode) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun q => (q 0, fun i => q i.succ)
          left_inv := fun p => by simp
          right_inv := fun q => by funext i; refine Fin.cases ?_ ?_ i <;> simp }
      have hcomp (σ : ℝ) :
          (interactionPicture ε (quarticInteraction g) σ).comp
              (Common.dysonCoeff (freeEigenvalue ε) (quarticInteraction g) n σ) =
            ∑ q0 : QuarticVertexLabel Mode,
              ∑ q' : Fin n → QuarticVertexLabel Mode,
                ((g q0 * quarticVertexTimeFactor ε q0 σ) *
                    quarticDysonSequenceCoeff ε g q' σ) •
                  quarticVertexSequenceOperator (Fin.cons q0 q') := by
        rw [interactionPicture_quarticInteraction_eq_sum, ih σ]
        ext x
        simp [LinearMap.sum_apply, LinearMap.comp_apply, quarticVertexSequenceOperator_cons,
          smul_smul, mul_assoc]
      have hpoint (σ : ℝ) :
          Common.matrixCoeff
              ((interactionPicture ε (quarticInteraction g) σ).comp
                (Common.dysonCoeff (freeEigenvalue ε) (quarticInteraction g) n σ)) m k =
            ∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
              ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
                  quarticDysonSequenceCoeff ε g (fun i => q i.succ) σ) *
                Common.matrixCoeff (quarticVertexSequenceOperator q) m k := by
        rw [hcomp σ]
        simp only [← Common.matrixCoeffLinear_apply, map_sum, map_smul,
          Common.matrixCoeffLinear_apply, smul_eq_mul]
        rw [← Fintype.sum_prod_type']
        rw [← Equiv.sum_comp e (fun q : Fin (n + 1) → QuarticVertexLabel Mode =>
          ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
              quarticDysonSequenceCoeff ε g (fun i => q i.succ) σ) *
            Common.matrixCoeff (quarticVertexSequenceOperator q) m k)]
        refine Finset.sum_congr rfl fun p _ => ?_
        obtain ⟨q0, q'⟩ := p
        simp [e]
      rw [show
        (fun σ : ℝ =>
          Common.matrixCoeff
            ((interactionPicture ε (quarticInteraction g) σ).comp
              (Common.dysonCoeff (freeEigenvalue ε) (quarticInteraction g) n σ)) m k) =
        (fun σ : ℝ =>
          ∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
            ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
                quarticDysonSequenceCoeff ε g (fun i => q i.succ) σ) *
              Common.matrixCoeff (quarticVertexSequenceOperator q) m k) by
          funext σ
          exact hpoint σ]
      have hintegrability : ∀ q : Fin (n + 1) → QuarticVertexLabel Mode,
          IntervalIntegrable
            (fun σ : ℝ =>
              ((g (q 0) * quarticVertexTimeFactor ε (q 0) σ) *
                  quarticDysonSequenceCoeff ε g (fun i => q i.succ) σ) *
                Common.matrixCoeff (quarticVertexSequenceOperator q) m k)
            MeasureTheory.volume 0 t := by
        intro q
        exact ((((continuous_const.mul
          (continuous_quarticVertexTimeFactor ε (q 0))).mul
            (continuous_quarticDysonSequenceCoeff ε g (fun i => q i.succ))).mul
              continuous_const).intervalIntegrable 0 t)
      rw [intervalIntegral.integral_finsetSum (fun q _ => hintegrability q)]
      have hright :
          Common.matrixCoeff
            (∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
              quarticDysonSequenceCoeff ε g q t • quarticVertexSequenceOperator q) m k =
            ∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
              quarticDysonSequenceCoeff ε g q t *
                Common.matrixCoeff (quarticVertexSequenceOperator q) m k := by
        simp only [← Common.matrixCoeffLinear_apply, map_sum, map_smul,
          Common.matrixCoeffLinear_apply, smul_eq_mul]
      rw [hright, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [intervalIntegral.integral_mul_const]
      have hq : Fin.cons (q 0) (fun i => q i.succ) = q := by
        change Fin.cons (q 0) (Fin.tail q) = q
        exact Fin.cons_self_tail q
      have hcoeff :=
        quarticDysonSequenceCoeff_cons ε g (q 0) (fun i => q i.succ) t
      rw [hq] at hcoeff
      rw [hcoeff]
      ring

end
end Bosonic
end SecondQuantization
