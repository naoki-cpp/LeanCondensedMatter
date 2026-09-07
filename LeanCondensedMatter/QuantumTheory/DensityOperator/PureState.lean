import LeanCondensedMatter.QuantumTheory.DensityOperator.Pure

/-!
# Physical pure states

Physical pure states are represented by rank-one density operators. Normalized vectors remain
computational representatives, while equality of `PureState` values is equality of the underlying
density operators and therefore does not distinguish a global phase.
-/

noncomputable section

namespace QuantumTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A density operator is physically pure when it is represented by a normalized state vector. -/
def IsPureDensity (ρ : DensityOperator H) : Prop :=
  ∃ ψ : StateVector H, ρ = pure ψ

/-- A physical pure state, stored canonically as a rank-one density operator. -/
def PureState (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  { ρ : DensityOperator H // IsPureDensity ρ }

/-- Every rank-one density operator constructed from a normalized vector is physically pure. -/
@[simp]
theorem isPureDensity_pure (ψ : StateVector H) : IsPureDensity (pure ψ) :=
  ⟨ψ, rfl⟩

/-- The rank-one density operator is invariant under multiplication of its representative by a
unit-modulus global phase. -/
theorem pure_smul_of_norm_eq_one (ψ : StateVector H) {c : ℂ} (hc : ‖c‖ = 1) :
    pure (⟨c • ψ.1, by rw [norm_smul, hc, ψ.2, one_mul]⟩ : StateVector H) = pure ψ := by
  apply DensityOperator.ext
  change InnerProductSpace.rankOne ℂ (c • ψ.1) (c • ψ.1) =
    InnerProductSpace.rankOne ℂ ψ.1 ψ.1
  have hunit : (starRingEnd ℂ) c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  ext x
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul]
  rw [mul_assoc, mul_comm (inner ℂ ψ.1 x) c, ← mul_assoc, hunit, one_mul]

/-- Two normalized vector representatives define the same rank-one density operator exactly when
they differ by a unit-modulus global phase. -/
theorem pure_eq_iff_exists_phase (ψ φ : StateVector H) :
    pure ψ = pure φ ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ φ.1 = c • ψ.1 := by
  constructor
  · intro h
    have hop := congrArg (fun ρ : DensityOperator H => ρ.op) h
    change InnerProductSpace.rankOne ℂ ψ.1 ψ.1 =
      InnerProductSpace.rankOne ℂ φ.1 φ.1 at hop
    have hφeig :
        φ.1 ∈ Module.End.eigenspace
          ((InnerProductSpace.rankOne ℂ φ.1 φ.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) 1 := by
      rw [eigenspace_rankOne_one φ.2]
      exact Submodule.subset_span (by simp)
    have hψeig :
        φ.1 ∈ Module.End.eigenspace
          ((InnerProductSpace.rankOne ℂ ψ.1 ψ.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) 1 := by
      rw [hop]
      exact hφeig
    have hspan : φ.1 ∈ Submodule.span ℂ {ψ.1} := by
      rw [← eigenspace_rankOne_one ψ.2]
      exact hψeig
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
    refine ⟨c, ?_, hc.symm⟩
    have hnorm := congrArg norm hc
    simpa [norm_smul, ψ.2, φ.2] using hnorm
  · rintro ⟨c, hc, hφ⟩
    have hstate :
        φ = (⟨c • ψ.1, by rw [norm_smul, hc, ψ.2, one_mul]⟩ : StateVector H) := by
      apply Subtype.ext
      exact hφ
    rw [hstate]
    exact (pure_smul_of_norm_eq_one ψ hc).symm

namespace PureState

/-- Map a normalized state-vector representative to its physical pure state. -/
noncomputable def ofStateVector (ψ : StateVector H) : PureState H :=
  ⟨pure ψ, isPureDensity_pure ψ⟩

@[simp]
theorem val_ofStateVector (ψ : StateVector H) :
    (ofStateVector ψ).1 = pure ψ :=
  rfl

/-- Every physical pure state has at least one normalized state-vector representative. -/
theorem exists_stateVector (ρ : PureState H) :
    ∃ ψ : StateVector H, ρ.1 = pure ψ := by
  simpa [IsPureDensity] using ρ.2

/-- The canonical map from normalized vector representatives to physical pure states identifies
global-phase-related representatives. -/
@[simp]
theorem ofStateVector_smul_of_norm_eq_one (ψ : StateVector H) {c : ℂ} (hc : ‖c‖ = 1) :
    ofStateVector (⟨c • ψ.1, by rw [norm_smul, hc, ψ.2, one_mul]⟩ : StateVector H) =
      ofStateVector ψ := by
  apply Subtype.ext
  exact pure_smul_of_norm_eq_one ψ hc

/-- Equality of physical pure states coming from normalized vectors is exactly global-phase
equivalence of those representatives. -/
theorem ofStateVector_eq_iff_exists_phase (ψ φ : StateVector H) :
    ofStateVector ψ = ofStateVector φ ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ φ.1 = c • ψ.1 := by
  constructor
  · intro h
    apply (pure_eq_iff_exists_phase ψ φ).mp
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact (pure_eq_iff_exists_phase ψ φ).mpr h

end PureState

end QuantumTheory
