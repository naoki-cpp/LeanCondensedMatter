import LeanCondensedMatter.SecondQuantization.Fermionic.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# Finite weighted traces and normalized diagonal functionals (algebraic)

Phase 6.5 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): thin,
`FermionOccupation Mode`-specialized wrappers around `Common.WeightedDiagonalFunctional`'s
statistics-generic `traceFock`/`weightedTrace`/`weightSum`/`normalizedWeightedDiagonal` — mirroring
`Common/TimeOrdering.lean`'s "generic in `Common/`, thin wrapper per statistics" split. The weight
`w : FermionOccupation Mode → ℂ` is *arbitrary* here — not yet the genuine Gibbs weight
`e^{-βE(n)}` — and no analytic `exp` appears in this file.

`[Fintype Mode]` throughout: `FermionOccupation Mode = Finset Mode` is itself a `Fintype` once
`Mode` is, so every trace below is a finite sum.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-! ## Traces and weighted sums -/

/-- **The `(m, n)` matrix coefficient** of an operator `A`, in the occupation-number basis:
`⟨m| A |n⟩`, i.e. the coefficient of `basisState m` in `A (basisState n)`. Delegates to
`Common.matrixCoeff`, so the meaning is guaranteed to match the bosonic line's
`Bosonic.diagonalCoeff`. -/
noncomputable def matrixCoeff (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (m n : FermionOccupation Mode) : ℂ :=
  Common.matrixCoeff A m n

/-- **The Fock-space trace** of an operator, `Tr A := Σₙ ⟨n| A |n⟩`. Delegates to
`Common.traceFock`. -/
noncomputable def traceFock (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : ℂ :=
  Common.traceFock A

/-- **The weighted trace**, `Tr_w A := Σₙ w(n) ⟨n| A |n⟩` — the un-normalized weighted diagonal
functional of `A` against the weight `w`. It becomes the un-normalized thermal weighted trace
only for a Gibbs/Boltzmann weight. Delegates to `Common.weightedTrace`. -/
noncomputable def weightedTrace (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : ℂ :=
  Common.weightedTrace w A

/-- **The total weight** of a weight function `w`, `weightSum(w) := ∑ₙ w(n)`. `w` is an arbitrary
`FermionOccupation Mode → ℂ` here, not necessarily a genuine Boltzmann weight. The physical
partition function is introduced separately by the Gibbs-specialized `freePartitionFunction`.
Delegates to `Common.weightSum`. -/
noncomputable def weightSum (w : FermionOccupation Mode → ℂ) : ℂ :=
  Common.weightSum w

/-- **The normalized weighted diagonal functional** of `A` against `w`, `Tr_w(A) / weightSum(w)`.
It is a genuine thermal (Gibbs-state) expectation only once `w` is specialized to a positive
Boltzmann weight with `weightSum(w) ≠ 0`. For a general complex `w` this is simply a `w`-weighted,
`weightSum(w)`-normalized diagonal functional, with no guarantee of positivity, reality (even
against a Hermitian `A`), or a Gibbs-state interpretation. Delegates to
`Common.normalizedWeightedDiagonal`. -/
noncomputable def normalizedWeightedDiagonal (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : ℂ :=
  Common.normalizedWeightedDiagonal w A

/-! ## Unfolding to the raw sum, for callers that need to compute -/

omit [LinearOrder Mode] in
/-- `traceFock` as its defining sum, headed by the fermionic `matrixCoeff` (not
`Common.matrixCoeff`) so it composes with fermionic-specific diagonal-coefficient facts (e.g.
`matrixCoeff_of_smul_basisState`) without a further unfold step. -/
theorem traceFock_eq_sum (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    traceFock A = ∑ n : FermionOccupation Mode, matrixCoeff A n n := rfl

omit [LinearOrder Mode] in
/-- `weightedTrace` as its defining sum, headed by the fermionic `matrixCoeff`. -/
theorem weightedTrace_eq_sum (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    weightedTrace w A = ∑ n : FermionOccupation Mode, w n * matrixCoeff A n n := rfl

omit [DecidableEq Mode] [LinearOrder Mode] in
/-- `weightSum` as its defining sum. -/
theorem weightSum_eq_sum (w : FermionOccupation Mode → ℂ) :
    weightSum w = ∑ n : FermionOccupation Mode, w n := rfl

omit [LinearOrder Mode] in
/-- `normalizedWeightedDiagonal` as its defining quotient, headed by the fermionic
`weightedTrace`/`weightSum`. -/
theorem normalizedWeightedDiagonal_eq_div (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedWeightedDiagonal w A = weightedTrace w A / weightSum w := rfl

/-! ## Linearity of `weightedTrace`/`normalizedWeightedDiagonal` in the operator argument -/

omit [LinearOrder Mode] in
theorem weightedTrace_smul (c : ℂ) (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    weightedTrace w (c • A) = c * weightedTrace w A :=
  Common.weightedTrace_smul c w A

omit [LinearOrder Mode] in
theorem weightedTrace_add (w : FermionOccupation Mode → ℂ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    weightedTrace w (A + B) = weightedTrace w A + weightedTrace w B :=
  Common.weightedTrace_add w A B

omit [LinearOrder Mode] in
theorem normalizedWeightedDiagonal_smul (c : ℂ) (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedWeightedDiagonal w (c • A) = c * normalizedWeightedDiagonal w A :=
  Common.normalizedWeightedDiagonal_smul c w A

omit [LinearOrder Mode] in
theorem normalizedWeightedDiagonal_add (w : FermionOccupation Mode → ℂ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedWeightedDiagonal w (A + B) =
      normalizedWeightedDiagonal w A + normalizedWeightedDiagonal w B :=
  Common.normalizedWeightedDiagonal_add w A B

omit [LinearOrder Mode] in
theorem normalizedWeightedDiagonal_neg (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedWeightedDiagonal w (-A) = -normalizedWeightedDiagonal w A :=
  Common.normalizedWeightedDiagonal_neg w A

omit [LinearOrder Mode] in
theorem normalizedWeightedDiagonal_sub (w : FermionOccupation Mode → ℂ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedWeightedDiagonal w (A - B) =
      normalizedWeightedDiagonal w A - normalizedWeightedDiagonal w B :=
  Common.normalizedWeightedDiagonal_sub w A B

/-! ## Matrix coefficients of diagonal operators -/

omit [LinearOrder Mode] [Fintype Mode] in
/-- **Diagonal matrix coefficients.** If `A` acts on `basisState n` as `c • basisState n`
(e.g. `numberOperator_basisState`/`totalNumberOperator_basisState`/`freeHamiltonian_basisState`
each give such a `c`), the `(n, n)` matrix coefficient is exactly `c`. Delegates to
`Common.matrixCoeff_of_smul_basisState`. -/
theorem matrixCoeff_of_smul_basisState {A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode}
    {n : FermionOccupation Mode} {c : ℂ} (h : A (basisState n) = c • basisState n) :
    matrixCoeff A n n = c :=
  Common.matrixCoeff_of_smul_basisState h

omit [LinearOrder Mode] in
@[simp]
theorem traceFock_id : traceFock (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] _) =
    (Fintype.card (FermionOccupation Mode) : ℂ) :=
  Common.traceFock_id

omit [LinearOrder Mode] in
/-- **The weighted trace of the identity is the partition function itself**,
`Tr_w(id) = Σₙ w(n) = weightSum(w)`. -/
theorem weightedTrace_id (w : FermionOccupation Mode → ℂ) :
    weightedTrace w (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] _) = weightSum w :=
  Common.weightedTrace_id w

omit [LinearOrder Mode] in
/-- **The normalized weighted functional of the identity is `1`**,
`⟨id⟩_w = weightSum(w)/weightSum(w) = 1`, given a nonzero total weight. For a Gibbs/Boltzmann
weight this is the corresponding Gibbs statement. -/
theorem normalizedWeightedDiagonal_id (w : FermionOccupation Mode → ℂ) (hw : weightSum w ≠ 0) :
    normalizedWeightedDiagonal w (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] _) = 1 :=
  Common.normalizedWeightedDiagonal_id w hw

/-! ## Weighted traces of the number operators -/

theorem weightedTrace_numberOperator (w : FermionOccupation Mode → ℂ) (i : Mode) :
    weightedTrace w (numberOperator i) =
      ∑ n ∈ (Finset.univ : Finset (FermionOccupation Mode)).filter (i ∈ ·), w n := by
  have h : ∀ n : FermionOccupation Mode,
      Common.matrixCoeff (numberOperator i) n n = if i ∈ n then 1 else 0 := fun n => by
    rcases Finset.decidableMem i n with hi | hi
    · exact matrixCoeff_of_smul_basisState (by
        rw [numberOperator_basisState, if_neg hi, if_neg hi, zero_smul])
    · exact matrixCoeff_of_smul_basisState (by
        rw [numberOperator_basisState, if_pos hi, if_pos hi, one_smul])
  simp only [weightedTrace, Common.weightedTrace, h, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]

theorem weightedTrace_totalNumberOperator (w : FermionOccupation Mode → ℂ) :
    weightedTrace w totalNumberOperator =
      ∑ n : FermionOccupation Mode, (fermionParticleNumber n : ℂ) * w n := by
  have h : ∀ n : FermionOccupation Mode,
      Common.matrixCoeff totalNumberOperator n n = (fermionParticleNumber n : ℂ) :=
    fun n => matrixCoeff_of_smul_basisState (totalNumberOperator_basisState n)
  simp only [weightedTrace, Common.weightedTrace, h]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

end SecondQuantization
