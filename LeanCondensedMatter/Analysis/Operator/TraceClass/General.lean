import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

set_option linter.style.header false

/-!
# General trace-class membership and trace norm

This module defines trace-class membership for bounded operators on a complete complex Hilbert
space. For a Hilbert basis `d`, `IsTraceClassWrt d T` means that the nonnegative diagonal
series of the canonical operator absolute value `CFC.abs T = |T|` is summable.

Basis independence is reduced to the existing Hilbert--Schmidt basis-independence theorem by
identifying the diagonal of `|T|` with the squared basis norms of `CFC.sqrt (CFC.abs T)`.
The same identification gives the canonical trace norm as the Hilbert--Schmidt norm square
and its basis formulas, including the positive-operator and polar-factor formulas.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The lossless diagonal expectation of the operator absolute value scales by the norm
of a complex scalar. -/
theorem diagonalExpectationValue_abs_smul
    (c : ℂ) (T : H →L[ℂ] H) (x : H) :
    diagonalExpectationValue (CFC.abs (c • T)) (CFC.abs_nonneg (c • T)).isSelfAdjoint x =
      ‖c‖ * diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint x := by
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue_right, Complex.ofReal_mul,
    coe_diagonalExpectationValue_right, CFC.abs_smul]
  rw [smul_apply]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) ‖c‖ ((CFC.abs T) x)]
  rw [inner_smul_right]
  rfl

/-- Trace-class membership with respect to a Hilbert basis: the diagonal series of `|T|` is
summable. -/
def IsTraceClassWrt {ι : Type*} (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : Prop :=
  Summable (fun i =>
    diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i))

/-- A diagonal matrix element of `|T|` is the squared norm of
`sqrt(|T|)` applied to the same vector. -/
theorem diagonalExpectationValue_abs_eq_norm_sq_sqrt_abs
    (T : H →L[ℂ] H) (x : H) :
    diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint x =
      ‖CFC.sqrt (CFC.abs T) x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue_right]
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg (CFC.abs T)).isSelfAdjoint
  have hsq : S * S = CFC.abs T := by
    exact CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  have hinner : inner ℂ x ((CFC.abs T) x) = inner ℂ (S x) (S x) := by
    rw [← hsq, mul_apply_eq_comp]
    calc
      inner ℂ x (S (S x)) =
          inner ℂ x ((ContinuousLinearMap.adjoint S) (S x)) := by rw [hS.adjoint_eq]
      _ = inner ℂ (S x) (S x) := ContinuousLinearMap.adjoint_inner_right S x (S x)
  rw [hinner, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- A bounded operator is trace class when `sqrt(|T|)` is Hilbert--Schmidt. The equivalent
Hilbert-basis diagonal criterion is `isTraceClass_iff_isTraceClassWrt`. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  IsHilbertSchmidt (CFC.sqrt (CFC.abs T))

/-- Trace-class membership is equivalent to summability of the diagonal of `|T|` in any chosen
Hilbert basis. -/
theorem isTraceClass_iff_isTraceClassWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) :
    IsTraceClass T ↔ IsTraceClassWrt d T := by
  unfold IsTraceClass IsTraceClassWrt
  simpa only [IsHilbertSchmidtWrt, diagonalExpectationValue_abs_eq_norm_sq_sqrt_abs] using
    (isHilbertSchmidt_iff_isHilbertSchmidtWrt d (CFC.sqrt (CFC.abs T)))


/-! ## Trace norm -/

namespace IsTraceClass

/-- The trace norm of a trace-class operator. -/
noncomputable def traceNorm {T : H →L[ℂ] H} (hT : IsTraceClass T) : ℝ :=
  IsHilbertSchmidt.normSq hT

/-- The diagonal series of `|T|` sums to the trace norm in every Hilbert basis. -/
theorem hasSum_abs_diagonalExpectationValue {T : H →L[ℂ] H}
    (hT : IsTraceClass T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue (CFC.abs T)
      (CFC.abs_nonneg T).isSelfAdjoint (d i)) hT.traceNorm := by
  simpa only [traceNorm, diagonalExpectationValue_abs_eq_norm_sq_sqrt_abs] using
    IsHilbertSchmidt.hasSum_norm_sq_apply hT d

/-- The trace norm is the diagonal series of `|T|` in every Hilbert basis. -/
theorem traceNorm_eq_tsum_diagonalExpectationValue {T : H →L[ℂ] H}
    (hT : IsTraceClass T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.traceNorm =
      ∑' i, diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) :=
  (hT.hasSum_abs_diagonalExpectationValue d).tsum_eq.symm

/-- If `U` is a left polar factor for `T`, the trace norm is the absolute diagonal
pairing of `U` with `T` in every Hilbert basis. -/
theorem traceNorm_eq_tsum_norm_inner_left_of_polar {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (U : H →L[ℂ] H)
    (hU : ContinuousLinearMap.adjoint U * T = CFC.abs T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.traceNorm = ∑' i, ‖inner ℂ (U (d i)) (T (d i))‖ := by
  rw [hT.traceNorm_eq_tsum_diagonalExpectationValue d]
  apply tsum_congr
  intro i
  have hdiag :
      (diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) : ℂ) =
        inner ℂ (U (d i)) (T (d i)) := by
    rw [coe_diagonalExpectationValue_right, ← hU, mul_apply_eq_comp]
    exact ContinuousLinearMap.adjoint_inner_right U (d i) (T (d i))
  have hnonneg := diagonalExpectationValue_nonneg
    (CFC.abs T) (nonneg_iff_isPositive.mp (CFC.abs_nonneg T)) (d i)
  rw [← hdiag, Complex.norm_real, Real.norm_of_nonneg hnonneg]

/-- The trace norm is independent of the proof of trace-class membership. -/
theorem traceNorm_proof_irrel {T : H →L[ℂ] H} (hT hT' : IsTraceClass T) :
    hT.traceNorm = hT'.traceNorm := by
  exact congrArg traceNorm (Subsingleton.elim hT hT')

/-- Equal trace-class operators have equal trace norms, independently of the
chosen proofs of trace-class membership. -/
theorem traceNorm_congr
    {S R : H →L[ℂ] H} (hS : IsTraceClass S) (hR : IsTraceClass R) (hSR : S = R) :
    hS.traceNorm = hR.traceNorm := by
  subst R
  exact IsTraceClass.traceNorm_proof_irrel _ _

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    0 ≤ hT.traceNorm :=
  IsHilbertSchmidt.normSq_nonneg hT

/-- For a positive trace-class operator, the diagonal expectation values in every Hilbert basis
sum to the trace norm. -/
theorem hasSum_diagonalExpectationValue_eq_traceNorm {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hpos : T.IsPositive) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (d i)) hT.traceNorm := by
  have habs : CFC.abs T = T := CFC.abs_of_nonneg T (nonneg_iff_isPositive.mpr hpos)
  simpa only [habs] using hT.hasSum_abs_diagonalExpectationValue d

/-- For a positive trace-class operator, the diagonal sum over any orthonormal family is bounded
by the trace norm. -/
theorem sum_diagonalExpectationValue_le_traceNorm {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hpos : T.IsPositive) {ι : Type*} {d : ι → H}
    (hd : Orthonormal ℂ d) :
    Summable (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (d i)) ∧
      ∑' i, diagonalExpectationValue T hpos.isSelfAdjoint (d i) ≤ hT.traceNorm := by
  obtain ⟨w, b, hsub, hb_eq⟩ := hd.toSubtypeRange.exists_hilbertBasis_extension
  set g : w → ℝ := fun j =>
    diagonalExpectationValue T hpos.isSelfAdjoint (b j) with hg_def
  have htr : HasSum g hT.traceNorm := by
    simpa [g] using hT.hasSum_diagonalExpectationValue_eq_traceNorm hpos b
  have hgsum : Summable g := htr.summable
  have hgnonneg : ∀ j : w, 0 ≤ g j := fun j => by
    simpa [g] using diagonalExpectationValue_nonneg T hpos (b j)
  have hd_inj : Function.Injective d := hd.linearIndependent.injective
  set e : ι → w := fun i => ⟨d i, hsub ⟨i, rfl⟩⟩ with he_def
  have he_inj : Function.Injective e := fun i j hij => hd_inj (congrArg Subtype.val hij)
  have hge : ∀ i, g (e i) = diagonalExpectationValue T hpos.isSelfAdjoint (d i) := fun i => by
    change diagonalExpectationValue T hpos.isSelfAdjoint (b (e i)) = _
    rw [show (b (e i) : H) = d i from by rw [hb_eq]]
  have hfsum : Summable (fun i => g (e i)) := hgsum.comp_injective he_inj
  have hle : ∑' i, g (e i) ≤ hT.traceNorm :=
    hasSum_le_inj e he_inj (fun j _ => hgnonneg j) (fun _ => le_rfl) hfsum.hasSum htr
  refine ⟨hfsum.congr hge, ?_⟩
  rwa [tsum_congr hge] at hle

/-- If a positive operator has strictly positive diagonal value on every unit vector, an
orthonormal family can saturate its trace norm only when its span has trivial orthogonal
complement. -/
theorem orthogonal_span_eq_bot_of_sum_diagonalExpectationValue_eq_traceNorm
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (hTpos : T.IsPositive)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d)
    (hdiag_pos : ∀ v : H, ‖v‖ = 1 →
      0 < diagonalExpectationValue T hTpos.isSelfAdjoint v)
    (heq : ∑' i, diagonalExpectationValue T hTpos.isSelfAdjoint (d i) =
      hT.traceNorm) :
    (Submodule.span ℂ (Set.range d))ᗮ = ⊥ := by
  classical
  obtain ⟨w, b, hsub, hb_eq⟩ := hd.toSubtypeRange.exists_hilbertBasis_extension
  set g : w → ℝ := fun j =>
    diagonalExpectationValue T hTpos.isSelfAdjoint (b j) with hg_def
  have htr : HasSum g (hT.traceNorm) :=
    hT.hasSum_diagonalExpectationValue_eq_traceNorm hTpos b
  have hgnonneg : ∀ j : w, 0 ≤ g j := fun j => by
    simpa [g] using diagonalExpectationValue_nonneg T hTpos (b j)
  have hd_inj : Function.Injective d := hd.linearIndependent.injective
  set e : ι → w := fun i => ⟨d i, hsub ⟨i, rfl⟩⟩ with he_def
  have he_inj : Function.Injective e := fun i j hij =>
    hd_inj (congrArg Subtype.val hij)
  have hge : ∀ i, g (e i) =
      diagonalExpectationValue T hTpos.isSelfAdjoint (d i) := fun i => by
    change diagonalExpectationValue T hTpos.isSelfAdjoint (b (e i)) = _
    rw [show (b (e i) : H) = d i from by rw [hb_eq]]
  have heqg : ∑' i, g (e i) = hT.traceNorm := by
    calc
      ∑' i, g (e i) =
          ∑' i, diagonalExpectationValue T hTpos.isSelfAdjoint (d i) :=
        tsum_congr hge
      _ = hT.traceNorm := heq
  have he_surj : Function.Surjective e := by
    by_contra hsurj
    have hsurj' : ∃ j, ∀ i, e i ≠ j := by
      simpa only [Function.Surjective, not_forall, not_exists] using hsurj
    obtain ⟨j, hj⟩ := hsurj'
    have hjrange : j ∉ Set.range e := by
      rintro ⟨i, hi⟩
      exact hj i hi
    have hgjpos : 0 < g j := by
      simpa [g] using hdiag_pos (b j) (b.orthonormal.1 j)
    have hsub : Summable (fun k : ↥((Set.range e)ᶜ) => g (k : w)) :=
      htr.summable.comp_injective Subtype.val_injective
    have hpos : 0 < ∑' k : ↥((Set.range e)ᶜ), g (k : w) :=
      hsub.tsum_pos (fun k => hgnonneg k) ⟨j, hjrange⟩ hgjpos
    have hrange : (∑' i, g (e i)) = ∑' k : Set.range e, g (k : w) := by
      simpa using (Equiv.tsum_eq (Equiv.ofInjective e he_inj) (fun k : Set.range e => g (k : w)))
    have hsplit := htr.summable.tsum_subtype_add_tsum_subtype_compl (Set.range e)
    rw [← hrange, heqg, htr.tsum_eq] at hsplit
    linarith
  apply le_antisymm
  · intro x hx
    have hinner : ∀ j : w, inner ℂ (b j) x = 0 := by
      intro j
      obtain ⟨i, hi⟩ := he_surj j
      have hbdi : b j = d i := by
        rw [← hi]
        rw [hb_eq]
      rw [hbdi]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self i)) hx
    have hrepr : b.repr x = 0 := by
      ext j
      rw [b.repr_apply_apply]
      exact hinner j
    have hx0 : x = 0 := b.repr.injective (by simpa using hrepr)
    rw [hx0]
    exact Submodule.zero_mem _
  · exact bot_le

end IsTraceClass

end ContinuousLinearMap
