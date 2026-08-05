import LeanCondensedMatter.Analysis.Operator.TraceClass.DiagonalSpectralTrace
import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic

/-!
# Diagonal density operators

Constructs a density operator from a Hilbert basis and summable nonnegative weights, and exposes
the converse spectral fact that every density operator admits a Hilbert-basis diagonalization.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Normalize summable nonnegative diagonal weights to obtain a density operator. -/
def diagonalDensityOperator (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) : DensityOperator H := by
  let Z : ℝ := ∑' i, a i
  let p : ι → ℝ := fun i => Z⁻¹ * a i
  have hZ_pos : 0 < Z := by simpa [Z] using hZ
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ_pos
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    exact mul_nonneg (inv_nonneg.mpr hZ_pos.le) (ha_nonneg i)
  have hp_norm : Summable fun i => ‖p i‖ := by
    have hscaled := ha.mul_left ‖Z⁻¹‖
    simpa [p, norm_mul] using hscaled
  refine
    { op := HilbertBasis.diagonalOp b (fun i => (p i : ℂ))
      pos := HilbertBasis.diagonalOp_isPositive b p hp_norm hp_nonneg
      spectralTraceClass := HilbertBasis.diagonalOpSpectralTraceClass b p hp_norm hp_nonneg
      spectralTrace_eq_one := ?_ }
  calc
    (HilbertBasis.diagonalOpSpectralTraceClass b p hp_norm hp_nonneg).trace
        = ∑' i, p i :=
      HilbertBasis.diagonalOpSpectralTraceClass_trace b p hp_norm hp_nonneg
    _ = Z⁻¹ * ∑' i, a i := by
      simp only [p]
      rw [tsum_mul_left]
    _ = 1 := by
      change Z⁻¹ * Z = 1
      exact inv_mul_cancel₀ hZ_ne

/-- Every density operator is diagonal in a Hilbert basis. The basis extends the canonical
orthonormal family of nonzero spectral eigenvectors; all additional basis vectors lie in the
kernel and therefore have weight zero. -/
theorem DensityOperator.exists_diagonal_hilbertBasis (ρ : DensityOperator H) :
    ∃ (u : Set H) (b : HilbertBasis u ℂ H) (w : u → ℝ),
      ∀ i, ρ.op (b i) = (w i : ℂ) • b i := by
  classical
  let hρcompact : IsCompactOperator ρ.op := ρ.spectralTraceClass.compact
  let hρsym : ρ.op.IsSymmetric := ρ.isSymmetric
  let e : EigenvectorIndex ρ.op → H := eigenvectorFamily hρcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hρcompact hρsym
  obtain ⟨u, b, hsub, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let j : EigenvectorIndex ρ.op → u := fun a => ⟨e a, hsub ⟨a, rfl⟩⟩
  have hb_j (a : EigenvectorIndex ρ.op) : b (j a) = e a := by
    rw [hb]
  have heigen (x : u) : ∃ c : ℝ, ρ.op (b x) = (c : ℂ) • b x := by
    by_cases hx : x ∈ Set.range j
    · rcases hx with ⟨a, rfl⟩
      refine ⟨a.1.1, ?_⟩
      rw [hb_j]
      exact apply_eigenvectorFamily hρcompact a
    · have hspan : Submodule.span ℂ (Set.range e) ≤ (ℂ ∙ (b x : H))ᗮ := by
        rw [Submodule.span_le]
        rintro y ⟨a, rfl⟩
        refine (Submodule.mem_orthogonal_singleton_iff_inner_left).2 ?_
        have hne : j a ≠ x := by
          intro h
          exact hx ⟨a, h⟩
        have horth : inner ℂ (b (j a)) (b x) = 0 := b.orthonormal.2 hne
        rw [hb_j] at horth
        exact horth
      have hxorth : (b x : H) ∈ (Submodule.span ℂ (Set.range e)).topologicalClosureᗮ := by
        rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
        intro y hy
        have hy' := hspan hy
        exact (Submodule.mem_orthogonal_singleton_iff_inner_left).1 hy'
      have hxker_mem :
          (b x : H) ∈ Module.End.eigenspace (ρ.op : H →ₗ[ℂ] H) (0 : ℂ) := by
        rw [← orthogonal_closure_span_eigenvectorFamily hρcompact hρsym]
        simpa [e] using hxorth
      have hxker : ρ.op (b x) = 0 := by
        have hxev := Module.End.mem_eigenspace_iff.mp hxker_mem
        simpa using hxev
      exact ⟨0, by simpa using hxker⟩
  choose w hw using heigen
  exact ⟨u, b, w, hw⟩

end QuantumTheory
