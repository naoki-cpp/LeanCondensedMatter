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
theorem pure_smul_of_norm_eq_one (ψ : StateVector H) {c : ℂ} (hc : ‖c‖ = 1)
    (hψ' : ‖c • ψ.1‖ = 1) :
    pure (⟨c • ψ.1, hψ'⟩ : StateVector H) = pure ψ := by
  apply DensityOperator.ext
  change InnerProductSpace.rankOne ℂ (c • ψ.1) (c • ψ.1) =
    InnerProductSpace.rankOne ℂ ψ.1 ψ.1
  have hunit : (starRingEnd ℂ) c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  ext x
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul]
  rw [mul_assoc, mul_comm (inner ℂ ψ.1 x) c, ← mul_assoc, hunit, one_mul]

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
theorem ofStateVector_smul_of_norm_eq_one (ψ : StateVector H) {c : ℂ} (hc : ‖c‖ = 1)
    (hψ' : ‖c • ψ.1‖ = 1) :
    ofStateVector (⟨c • ψ.1, hψ'⟩ : StateVector H) = ofStateVector ψ := by
  apply Subtype.ext
  exact pure_smul_of_norm_eq_one ψ hc hψ'

end PureState

end QuantumTheory
