import LeanCondensedMatter.QuantumTheory.Gibbs.Uniqueness

/-!
# Uniqueness of the Gibbs minimizer

The equality components recovered in `Gibbs.Uniqueness` identify a minimizing density operator with
the canonical Gibbs state.  The public result is the final if-and-only-if characterization; the
one-way implication is kept local to its proof.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For nonzero inverse temperature, the Helmholtz equality case is attained exactly by the
canonical Gibbs state. -/
theorem helmholtzFreeEnergy_eq_iff_eq_gibbsState
    (ρ : DensityOperator H) (Hop : Observable H) (β : ℝ) (hβ : β ≠ 0)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal =
        -(1 / β) * Real.log (spectralTrace (gibbsOp Hop β)) ↔
      ρ = gibbsState Hop β hcompact hZ := by
  constructor
  · intro hfree
    letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
    let σ := gibbsState Hop β hcompact hZ
    set d := eigenvectorFamily ρ.spectralTraceClass.compact with hd_def
    set h : EigenvectorIndex ρ.op → ℝ :=
      fun a => diagonalExpectationValue Hop.1 Hop.2 (d a) with hh_def
    set q : EigenvectorIndex ρ.op → ℝ := fun a =>
      diagonalExpectationValue (gibbsOp Hop β)
        (gibbsOp_isPositive Hop β).isSelfAdjoint (d a) with hq_def
    set Z : ℝ := spectralTrace (gibbsOp Hop β) with hZ_def
    obtain ⟨hqsum, hpq, hpeierls⟩ :=
      helmholtzFreeEnergy_eq_components ρ Hop β hβ hcompact hZ hfree
    have hd_orth : Orthonormal ℂ d :=
      orthonormal_eigenvectorFamily ρ.spectralTraceClass.compact ρ.isSymmetric
    have hd_unit : ∀ a, ‖d a‖ = 1 := eigenvectorFamily_norm_eq_one ρ
    have hqsum' : ∑' a, q a = Z := by
      simpa [d, q, Z] using hqsum
    have hpq' : ∀ a, a.1.1 = q a / Z := by
      intro a
      simpa [d, q, Z] using hpq a
    have hpeierls' : ∀ a, Real.exp (-β * h a) = q a := by
      intro a
      simpa [d, h, q] using hpeierls a
    have hcomplete : (Submodule.span ℂ (Set.range d))ᗮ = ⊥ := by
      apply gibbsOp_orthogonal_span_eq_bot_of_diagonal_sum_eq_spectralTrace
        Hop β hcompact hd_orth
      simpa [q, Z] using hqsum'
    have henergyEigen : ∀ a,
        (Hop.1 : H →ₗ[ℂ] H) (d a) = (h a : ℂ) • d a := by
      intro a
      apply (gibbs_peierls_bogoliubov_eq_iff_eigenvector
        Hop.1 Hop.2 β hβ (d a) (hd_unit a)).mp
      have heqComplex :
          (Real.exp (-β * h a) : ℂ) =
            inner ℂ (gibbsOp Hop β (d a)) (d a) := by
        rw [← coe_diagonalExpectationValue
          (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint (d a)]
        exact_mod_cast hpeierls' a
      simpa [h, gibbsOp] using heqComplex
    have honFamily : ∀ a, ρ.op (d a) = σ.op (d a) := by
      intro a
      have hρ := apply_eigenvectorFamily ρ.spectralTraceClass.compact a
      have hσ := gibbsState_apply_eigenvector Hop β hcompact hZ (henergyEigen a)
      have hcoeffReal : a.1.1 = Z⁻¹ * Real.exp (-β * h a) := by
        rw [hpq' a, hpeierls' a]
        ring
      have hcoeffComplex :
          (a.1.1 : ℂ) = ((Z⁻¹ : ℝ) • (Real.exp (-β * h a) : ℂ)) := by
        rw [Complex.real_smul]
        exact_mod_cast hcoeffReal
      calc
        ρ.op (d a) = (a.1.1 : ℂ) • d a := hρ
        _ = (((Z⁻¹ : ℝ) • (Real.exp (-β * h a) : ℂ)) • d a) := by
          rw [hcoeffComplex]
        _ = σ.op (d a) := by
          simpa [σ, Z] using hσ.symm
    have hspan_top : Submodule.span ℂ (Set.range d) = ⊤ :=
      Submodule.orthogonal_eq_bot_iff.mp hcomplete
    apply DensityOperator.ext
    apply ContinuousLinearMap.ext
    intro x
    have hx : x ∈ Submodule.span ℂ (Set.range d) := by
      rw [hspan_top]
      exact Submodule.mem_top
    have hspan_le :
        Submodule.span ℂ (Set.range d) ≤
          LinearMap.ker ((ρ.op : H →ₗ[ℂ] H) - (σ.op : H →ₗ[ℂ] H)) := by
      rw [Submodule.span_le]
      rintro y ⟨a, rfl⟩
      change ρ.op (d a) - σ.op (d a) = 0
      exact sub_eq_zero.mpr (honFamily a)
    have hxker := hspan_le hx
    change ρ.op x - σ.op x = 0 at hxker
    exact sub_eq_zero.mp hxker
  · intro hρ
    rw [hρ]
    exact gibbsState_helmholtzFreeEnergy_eq Hop β hβ hcompact hZ

end QuantumTheory
