import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.DensityOperator.Purity
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Finite-dimensional density-operator specialization

Finite dimensionality does not introduce a second density-state type. This module collects the
bridges from the canonical dimension-independent `DensityOperator` API to ordinary finite matrix
traces and finite-index corollaries.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Construct the canonical density state from a positive finite-dimensional trace-one operator. -/
noncomputable def DensityOperator.ofFiniteDimensional
    (ρ : H →L[ℂ] H) (hpos : ρ.IsPositive)
    (htrace : LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) = 1) : DensityOperator H := by
  have hsymm : ρ.IsSymmetric := hpos.isSelfAdjoint.isSymmetric
  have hcompact : IsCompactOperator ρ :=
    isCompactOperator_of_locallyCompactSpace_dom ρ
  letI : Finite (EigenvectorIndex ρ) :=
    (orthonormal_eigenvectorFamily hcompact hsymm).linearIndependent.finite
  have hsummable : HasSummableRealEigenvalues ρ := Summable.of_finite
  let hstc : SpectralTraceClass ρ :=
    SpectralTraceClass.ofPositive hcompact hpos hsummable
  refine
    { op := ρ
      pos := hpos
      spectralTraceClass := hstc
      spectralTrace_eq_one := ?_ }
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    hsymm.eigenvectorBasis rfl
  have hb (i : Fin (Module.finrank ℂ H)) :
      ρ (b i) = (hsymm.eigenvalues rfl i : ℂ) • b i := by
    change (ρ : H →ₗ[ℂ] H) (b i) = (hsymm.eigenvalues rfl i : ℂ) • b i
    simpa [b] using hsymm.apply_eigenvectorBasis rfl i
  have hsum := (hstc.hasSum_diagonalExpectationValue b.toHilbertBasis).tsum_eq
  rw [tsum_fintype] at hsum
  have heigenComplex :
      ((∑ i, hsymm.eigenvalues rfl i : ℝ) : ℂ) =
        LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) :=
    (hsymm.trace_eq_sum_eigenvalues (hn := rfl)).symm
  rw [htrace] at heigenComplex
  have heigen : ∑ i, hsymm.eigenvalues rfl i = 1 := by
    exact_mod_cast heigenComplex
  calc
    hstc.trace = ∑ i, diagonalExpectationValue ρ hstc.isSelfAdjoint (b i) := by
      simpa using hsum.symm
    _ = ∑ i, hsymm.eigenvalues rfl i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Complex.ofReal_injective
      rw [coe_diagonalExpectationValue_right, hb i, inner_smul_right,
        inner_self_eq_norm_sq_to_K, b.norm_eq_one]
      simp
    _ = 1 := heigen

@[simp]
theorem DensityOperator.ofFiniteDimensional_op
    (ρ : H →L[ℂ] H) (hpos : ρ.IsPositive)
    (htrace : LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) = 1) :
    (DensityOperator.ofFiniteDimensional ρ hpos htrace).op = ρ :=
  rfl

/-- In finite dimensions, the spectral expectation equals the ordinary trace `Tr(ρA)`. -/
theorem DensityOperator.expectation_eq_linearMap_trace (ρ : DensityOperator H)
    (A : H →L[ℂ] H) :
    ρ.expectation A =
      LinearMap.trace ℂ H ((ρ.op ∘L A : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  classical
  let hρcompact : IsCompactOperator ρ.op := ρ.spectralTraceClass.compact
  let hρsym : ρ.op.IsSymmetric := ρ.isSymmetric
  let e : EigenvectorIndex ρ.op → H := eigenvectorFamily hρcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hρcompact hρsym
  obtain ⟨u, b, hsub, hb⟩ := he.toSubtypeRange.exists_orthonormalBasis_extension
  let j : EigenvectorIndex ρ.op → u := fun a => ⟨e a, hsub ⟨a, rfl⟩⟩
  have hj : Function.Injective j := by
    intro a a' haa'
    apply he.linearIndependent.injective
    exact congrArg Subtype.val haa'
  let g : u → ℂ := fun i => inner ℂ (b i) ((ρ.op ∘L A) (b i))
  have hb_j (a : EigenvectorIndex ρ.op) : b (j a) = e a := by
    rw [hb]
  have hpoint (a : EigenvectorIndex ρ.op) :
      g (j a) = (a.1.1 : ℂ) * inner ℂ (e a) (A (e a)) := by
    change inner ℂ (b (j a))
        ((ρ.op : H →ₗ[ℂ] H) ((A : H →ₗ[ℂ] H) (b (j a)))) =
      (a.1.1 : ℂ) * inner ℂ (e a) ((A : H →ₗ[ℂ] H) (e a))
    rw [hb_j]
    calc
      inner ℂ (e a) ((ρ.op : H →ₗ[ℂ] H) ((A : H →ₗ[ℂ] H) (e a))) =
          inner ℂ ((ρ.op : H →ₗ[ℂ] H) (e a)) ((A : H →ₗ[ℂ] H) (e a)) :=
        (hρsym (e a) ((A : H →ₗ[ℂ] H) (e a))).symm
      _ = (a.1.1 : ℂ) * inner ℂ (e a) ((A : H →ₗ[ℂ] H) (e a)) := by
        rw [apply_eigenvectorFamily hρcompact, inner_smul_left]
        simp [e]
  have hzero (x : u) (hx : x ∉ Set.range j) : g x = 0 := by
    letI : Finite u := b.orthonormal.linearIndependent.finite
    letI : Fintype u := Fintype.ofFinite u
    have hxker := hilbertBasis_apply_eq_zero_of_not_mem_eigenvector_range
      hρcompact hρsym b.toHilbertBasis j (fun a => by simpa [e] using hb_j a) x hx
    change inner ℂ (b x) ((ρ.op : H →ₗ[ℂ] H) ((A : H →ₗ[ℂ] H) (b x))) = 0
    calc
      inner ℂ (b x) ((ρ.op : H →ₗ[ℂ] H) ((A : H →ₗ[ℂ] H) (b x))) =
          inner ℂ ((ρ.op : H →ₗ[ℂ] H) (b x)) ((A : H →ₗ[ℂ] H) (b x)) :=
        (hρsym (b x) ((A : H →ₗ[ℂ] H) (b x))).symm
      _ = 0 := by rw [hxker, inner_zero_left]
  have hfull : HasSum g (∑ i, g i) := hasSum_fintype _
  have hrestricted : HasSum
      (fun a : EigenvectorIndex ρ.op =>
        (a.1.1 : ℂ) * inner ℂ (e a) (A (e a)))
      (∑ i, g i) := by
    simpa only [Function.comp_apply] using
      HasSum.congr_fun ((hj.hasSum_iff hzero).mpr hfull) fun a => (hpoint a).symm
  have hsum :
      (∑' a : EigenvectorIndex ρ.op,
        (a.1.1 : ℂ) * inner ℂ (e a) (A (e a))) = ∑ i, g i :=
    (ρ.summable_expectation_term A).hasSum.unique hrestricted
  have htrace := LinearMap.trace_eq_sum_inner
    ((ρ.op ∘L A : H →L[ℂ] H) : H →ₗ[ℂ] H) b
  have hgtrace :
      LinearMap.trace ℂ H ((ρ.op ∘L A : H →L[ℂ] H) : H →ₗ[ℂ] H) =
        ∑ i, g i := by
    simpa [g] using htrace
  rw [ρ.expectation_apply, hsum, ← hgtrace]

/-- In finite dimensions, the ordinary trace of a density operator is one. -/
theorem DensityOperator.linearMap_trace_eq_one (ρ : DensityOperator H) :
    LinearMap.trace ℂ H (ρ.op : H →ₗ[ℂ] H) = 1 := by
  have h := (ρ.expectation_eq_linearMap_trace (ContinuousLinearMap.id ℂ H)).symm.trans
    ρ.expectation_id
  simpa using h

omit [FiniteDimensional ℂ H] in
/-- A finite diagonal expectation is the finite-index corollary of the countable Hilbert-basis
formula; no separate finite-dimensional hypothesis is needed once the finite basis is supplied. -/
theorem DensityOperator.expectation_eq_sum_diagonal {ι : Type*} [Fintype ι]
    (ρ : DensityOperator H) (A : H →L[ℂ] H) (b : OrthonormalBasis ι ℂ H)
    (w : ι → ℝ) (hρ : ∀ i, (ρ.op : H →ₗ[ℂ] H) (b i) = (w i : ℂ) • b i) :
    ρ.expectation A = ∑ i, (w i : ℂ) * inner ℂ (b i) (A (b i)) := by
  simpa [tsum_fintype] using
    ρ.expectation_eq_tsum_diagonal A b.toHilbertBasis w (fun i => by simpa using hρ i)

/-- In finite dimensions, the ordinary matrix trace `Tr(ρ²)` is the complex embedding of purity. -/
theorem DensityOperator.linearMap_trace_sq_eq_purity (ρ : DensityOperator H) :
    LinearMap.trace ℂ H
      ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H) = (purity ρ : ℂ) := by
  calc
    LinearMap.trace ℂ H
        ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H) = ρ.expectation ρ.op :=
      (ρ.expectation_eq_linearMap_trace ρ.op).symm
    _ = (purity ρ : ℂ) := ρ.expectation_op

end QuantumTheory
