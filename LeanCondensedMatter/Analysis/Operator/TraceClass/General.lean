import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.header false

/-!
# General trace-class operators

This module defines trace-class operators without compactness or self-adjointness assumptions.
The definition uses the Hilbert-space factorization characterization: `T` is trace-class when it
factors as a product of two Hilbert–Schmidt operators. The trace norm is the infimum of the
products of their Hilbert–Schmidt norms.

This interface is designed to reuse the basis-independent Hilbert–Schmidt inner product already
developed in LCM. It is separate from `SpectralTraceClass`, which remains a convenient bundled
interface for compact symmetric operators with summable eigenvalues.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

/-- A bounded operator is trace-class if it is a product of two Hilbert–Schmidt operators.

This is the Hilbert-space factorization characterization of trace-class operators. It places no
compactness or self-adjointness assumption on `T`. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ S R : H →L[ℂ] H, IsHilbertSchmidt S ∧ IsHilbertSchmidt R ∧ S * R = T

/-- The diagonal series of an operator against a specified Hilbert basis. It is used only when
`T` is trace-class; `traceDiagonal_summable` establishes convergence and
`traceDiagonal_eq_of_isTraceClass` proves basis independence. -/
noncomputable def traceDiagonal {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) : ℂ :=
  ∑' i, (inner ℂ (T (d i)) (d i) : ℂ)

private theorem traceDiagonal_eq_innerHS_of_factorization {ι : Type*}
    (d : HilbertBasis ι ℂ H) {S R : H →L[ℂ] H} {T : H →L[ℂ] H}
    (hSR : S * R = T) : traceDiagonal d T = innerHS d R (ContinuousLinearMap.adjoint S) := by
  unfold traceDiagonal innerHS
  apply tsum_congr
  intro i
  rw [← hSR, mul_apply_eq_comp]
  exact (ContinuousLinearMap.adjoint_inner_right S (R (d i)) (d i)).symm

/-- If `T` is trace-class, its diagonal series converges absolutely in every Hilbert basis. -/
theorem traceDiagonal_summable {ι : Type*} (d : HilbertBasis ι ℂ H)
    (hT : IsTraceClass T) :
    Summable (fun i => (inner ℂ (T (d i)) (d i) : ℂ)) := by
  obtain ⟨S, R, hS, hR, hSR⟩ := hT
  have hS' : IsHilbertSchmidt (ContinuousLinearMap.adjoint S) := isHilbertSchmidt_adjoint hS
  have hsum := summable_inner_apply_of_isHilbertSchmidtWrt d
    (hR.isHilbertSchmidtWrt d) (hS'.isHilbertSchmidtWrt d)
  exact hsum.congr fun i => by
    rw [← hSR, mul_apply_eq_comp]
    exact ContinuousLinearMap.adjoint_inner_right S (R (d i)) (d i)

/-- For a trace-class operator, the diagonal sum is independent of the Hilbert basis. -/
theorem traceDiagonal_eq_of_isTraceClass {ι κ : Type*}
    (d : HilbertBasis ι ℂ H) (e : HilbertBasis κ ℂ H) (hT : IsTraceClass T) :
    traceDiagonal d T = traceDiagonal e T := by
  obtain ⟨S, R, hS, hR, hSR⟩ := hT
  rw [traceDiagonal_eq_innerHS_of_factorization d hSR,
    traceDiagonal_eq_innerHS_of_factorization e hSR]
  exact innerHS_eq_of_isHilbertSchmidt d e hR (isHilbertSchmidt_adjoint hS)

/-- The Hilbert–Schmidt norm computed against a specified Hilbert basis. -/
noncomputable def hilbertSchmidtNormWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (S : H →L[ℂ] H) : ℝ :=
  Real.sqrt (∑' i, ‖S (d i)‖ ^ 2)

/-- The Hilbert–Schmidt norm does not depend on the Hilbert basis when `S` is
Hilbert–Schmidt. -/
theorem hilbertSchmidtNormWrt_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (e : HilbertBasis κ ℂ H) {S : H →L[ℂ] H} (hS : IsHilbertSchmidt S) :
    hilbertSchmidtNormWrt d S = hilbertSchmidtNormWrt e S := by
  unfold hilbertSchmidtNormWrt
  congr 1
  exact (summable_norm_sq_apply_and_tsum_eq d e S (hS.isHilbertSchmidtWrt d)).2.symm

/-- The cost of a Hilbert–Schmidt factorization, computed against a specified basis. -/
noncomputable def traceFactorizationCostWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (S R : H →L[ℂ] H) : ℝ :=
  hilbertSchmidtNormWrt d S * hilbertSchmidtNormWrt d R

private theorem traceFactorizationCostWrt_eq {ι κ : Type*}
    (d : HilbertBasis ι ℂ H) (e : HilbertBasis κ ℂ H)
    {S R : H →L[ℂ] H} (hS : IsHilbertSchmidt S) (hR : IsHilbertSchmidt R) :
    traceFactorizationCostWrt d S R = traceFactorizationCostWrt e S R := by
  unfold traceFactorizationCostWrt
  rw [hilbertSchmidtNormWrt_eq d e hS, hilbertSchmidtNormWrt_eq d e hR]

/-- The trace norm computed against a specified Hilbert basis, as the infimum of the products of
Hilbert–Schmidt norms over all Hilbert–Schmidt factorizations of `T`. -/
noncomputable def traceNormWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) : ℝ :=
  sInf {r : ℝ | ∃ S R : H →L[ℂ] H, IsHilbertSchmidt S ∧ IsHilbertSchmidt R ∧
    S * R = T ∧ traceFactorizationCostWrt d S R ≤ r}

/-- The trace norm of a trace-class operator is independent of the Hilbert basis used to compute
the Hilbert–Schmidt norms in its factorization formula. -/
theorem traceNormWrt_eq {ι κ : Type*}
    (d : HilbertBasis ι ℂ H) (e : HilbertBasis κ ℂ H) :
    traceNormWrt d T = traceNormWrt e T := by
  have hsets :
      {r : ℝ | ∃ S R : H →L[ℂ] H, IsHilbertSchmidt S ∧ IsHilbertSchmidt R ∧
        S * R = T ∧ traceFactorizationCostWrt d S R ≤ r} =
      {r : ℝ | ∃ S R : H →L[ℂ] H, IsHilbertSchmidt S ∧ IsHilbertSchmidt R ∧
        S * R = T ∧ traceFactorizationCostWrt e S R ≤ r} := by
    ext r
    constructor
    · rintro ⟨S, R, hS, hR, hSR, hr⟩
      have hcost := traceFactorizationCostWrt_eq d e hS hR
      rw [hcost] at hr
      exact ⟨S, R, hS, hR, hSR, hr⟩
    · rintro ⟨S, R, hS, hR, hSR, hr⟩
      have hcost := traceFactorizationCostWrt_eq e d hS hR
      rw [hcost] at hr
      exact ⟨S, R, hS, hR, hSR, hr⟩
  unfold traceNormWrt
  rw [hsets]

/-! ### Basis-free public API -/

private noncomputable def someHilbertBasis : Σ w : Set H, HilbertBasis w ℂ H := by
  obtain ⟨w, d, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  exact ⟨w, d⟩

namespace IsTraceClass

/-- The trace of a trace-class operator. Its definition uses one chosen Hilbert basis; the public
formula `trace_eq_traceDiagonal` shows that every Hilbert basis gives the same value. -/
noncomputable def trace (_hT : IsTraceClass T) : ℂ :=
  traceDiagonal someHilbertBasis.2 T

theorem trace_eq_traceDiagonal (hT : IsTraceClass T) {ι : Type*}
    (d : HilbertBasis ι ℂ H) : hT.trace = traceDiagonal d T :=
  traceDiagonal_eq_of_isTraceClass someHilbertBasis.2 d hT

/-- The trace norm of a trace-class operator, computed using one chosen Hilbert basis. -/
noncomputable def traceNorm (_hT : IsTraceClass T) : ℝ :=
  traceNormWrt someHilbertBasis.2 T

theorem traceNorm_eq_traceNormWrt (hT : IsTraceClass T) {ι : Type*}
    (d : HilbertBasis ι ℂ H) : hT.traceNorm = traceNormWrt d T :=
  traceNormWrt_eq someHilbertBasis.2 d

end IsTraceClass

end ContinuousLinearMap
