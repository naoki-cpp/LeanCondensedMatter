import LeanCondensedMatter.SecondQuantization.Fermionic.Hamiltonian

set_option linter.style.header false

/-!
# Finite weighted traces and normalized diagonal functionals (algebraic)

Phase 6.5 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
finite-mode-set trace, weighted trace, partition function, and normalized weighted diagonal
functional, for an
*arbitrary* weight `w : FermionOccupation Mode → ℂ` — not yet the genuine Gibbs weight
`e^{-βE(n)}`, and no analytic `exp` anywhere in this file. This is deliberate: it isolates the
purely combinatorial "sum over basis states, weighted" structure that both a formal Gibbs weight
and (later) a genuine analytic one will specialize to, without committing to either yet.

`[Fintype Mode]` throughout: `FermionOccupation Mode = Finset Mode` is itself a `Fintype` once
`Mode` is, so every trace below is a finite sum.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-! ## Traces -/

/-- **The `(m, n)` matrix coefficient** of an operator `A`, in the occupation-number basis:
`⟨m| A |n⟩`, i.e. the coefficient of `basisState m` in `A (basisState n)`. Delegates to
`Common.matrixCoeff`, so the meaning is guaranteed to match the bosonic line's
`Bosonic.diagonalCoeff`. -/
noncomputable def matrixCoeff (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (m n : FermionOccupation Mode) : ℂ :=
  Common.matrixCoeff A m n

/-- **The Fock-space trace** of an operator, `Tr A := Σₙ ⟨n| A |n⟩`. -/
noncomputable def traceFock (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : ℂ :=
  ∑ n : FermionOccupation Mode, matrixCoeff A n n

/-- **The weighted trace**, `Tr_w A := Σₙ w(n) ⟨n| A |n⟩` — the un-normalized weighted diagonal
functional of `A` against the weight `w`. It becomes the un-normalized thermal weighted trace
only for a Gibbs/Boltzmann weight. -/
noncomputable def weightedTrace (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : ℂ :=
  ∑ n : FermionOccupation Mode, w n * matrixCoeff A n n

/-- **The partition function** of a weight `w`, `Z(w) := Σₙ w(n)`. `w` is an arbitrary
`FermionOccupation Mode → ℂ` here, not necessarily a genuine Boltzmann weight
`w(n) = e^{-βE(n)}` — `Z(w)` is only the physical partition function `Tr(e^{-βH})` once `w` is
specialized to that positive, real-valued form. -/
noncomputable def partitionFunction (w : FermionOccupation Mode → ℂ) : ℂ :=
  ∑ n : FermionOccupation Mode, w n

/-- **The normalized weighted diagonal functional** of `A` against `w`, `Tr_w(A) / Z(w)`.
The normalized weighted diagonal functional is `normalizedWeightedDiagonal`; it is a genuine thermal (Gibbs-state)
expectation only once `w` is specialized to a positive Boltzmann weight with `Z(w) ≠ 0`. For a
general complex `w` this is simply a `w`-weighted, `Z(w)`-normalized diagonal functional, with no
guarantee of positivity, reality (even against a Hermitian `A`), or a Gibbs-state interpretation. -/
noncomputable def normalizedWeightedDiagonal (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : ℂ :=
  weightedTrace w A / partitionFunction w

/-! ## Linearity of `weightedTrace`/`normalizedWeightedDiagonal` in the operator argument -/

omit [LinearOrder Mode] in
theorem weightedTrace_smul (c : ℂ) (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    weightedTrace w (c • A) = c * weightedTrace w A := by
  simp only [weightedTrace, matrixCoeff, Common.matrixCoeff_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

omit [LinearOrder Mode] in
theorem weightedTrace_add (w : FermionOccupation Mode → ℂ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    weightedTrace w (A + B) = weightedTrace w A + weightedTrace w B := by
  simp only [weightedTrace, matrixCoeff, Common.matrixCoeff_add, mul_add]
  exact Finset.sum_add_distrib

omit [LinearOrder Mode] in
theorem normalizedWeightedDiagonal_smul (c : ℂ) (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedWeightedDiagonal w (c • A) = c * normalizedWeightedDiagonal w A := by
  rw [normalizedWeightedDiagonal, normalizedWeightedDiagonal, weightedTrace_smul, mul_div_assoc]

omit [LinearOrder Mode] in
theorem normalizedWeightedDiagonal_add (w : FermionOccupation Mode → ℂ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedWeightedDiagonal w (A + B) = normalizedWeightedDiagonal w A + normalizedWeightedDiagonal w B := by
  rw [normalizedWeightedDiagonal, normalizedWeightedDiagonal, normalizedWeightedDiagonal, weightedTrace_add, add_div]

omit [LinearOrder Mode] in
theorem normalizedWeightedDiagonal_neg (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedWeightedDiagonal w (-A) = -normalizedWeightedDiagonal w A := by
  rw [show (-A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) = (-1 : ℂ) • A from
    (neg_one_smul ℂ A).symm, normalizedWeightedDiagonal_smul, neg_one_mul]

omit [LinearOrder Mode] in
theorem normalizedWeightedDiagonal_sub (w : FermionOccupation Mode → ℂ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedWeightedDiagonal w (A - B) = normalizedWeightedDiagonal w A - normalizedWeightedDiagonal w B := by
  change normalizedWeightedDiagonal w (A + -B) =
    normalizedWeightedDiagonal w A + -normalizedWeightedDiagonal w B
  rw [normalizedWeightedDiagonal_add, normalizedWeightedDiagonal_neg]

/-! ## Matrix coefficients of diagonal operators -/

omit [LinearOrder Mode] [Fintype Mode] in
/-- **Diagonal matrix coefficients.** If `A` acts on `basisState n` as `c • basisState n`
(e.g. `numberOperator_basisState`/`totalNumberOperator_basisState`/`freeHamiltonian_basisState`
each give such a `c`), the `(n, n)` matrix coefficient is exactly `c`. -/
theorem matrixCoeff_of_smul_basisState {A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode}
    {n : FermionOccupation Mode} {c : ℂ} (h : A (basisState n) = c • basisState n) :
    matrixCoeff A n n = c := by
  change A (basisState n) n = c
  rw [h, basisState, Common.smul_basisState_apply_self]

omit [LinearOrder Mode] in
@[simp]
theorem traceFock_id : traceFock (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] _) =
    (Fintype.card (FermionOccupation Mode) : ℂ) := by
  have h : ∀ n : FermionOccupation Mode, matrixCoeff (LinearMap.id) n n = 1 := fun n =>
    matrixCoeff_of_smul_basisState (by rw [LinearMap.id_apply, one_smul])
  simp [traceFock, h]

omit [LinearOrder Mode] in
/-- **The weighted trace of the identity is the partition function itself**,
`Tr_w(id) = Σₙ w(n) = Z(w)`. -/
theorem weightedTrace_id (w : FermionOccupation Mode → ℂ) :
    weightedTrace w (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] _) = partitionFunction w := by
  have h : ∀ n : FermionOccupation Mode, matrixCoeff (LinearMap.id) n n = 1 := fun n =>
    matrixCoeff_of_smul_basisState (by rw [LinearMap.id_apply, one_smul])
  simp [weightedTrace, partitionFunction, h]

omit [LinearOrder Mode] in
/-- **The normalized weighted functional of the identity is `1`**, `⟨id⟩_w = Z(w)/Z(w) = 1`,
given a nonzero partition function. For a Gibbs/Boltzmann weight this is the corresponding Gibbs
statement. -/
theorem normalizedWeightedDiagonal_id (w : FermionOccupation Mode → ℂ) (hw : partitionFunction w ≠ 0) :
    normalizedWeightedDiagonal w (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] _) = 1 := by
  rw [normalizedWeightedDiagonal, weightedTrace_id, div_self hw]

/-! ## Weighted traces of the number operators -/

theorem weightedTrace_numberOperator (w : FermionOccupation Mode → ℂ) (i : Mode) :
    weightedTrace w (numberOperator i) =
      ∑ n ∈ (Finset.univ : Finset (FermionOccupation Mode)).filter (i ∈ ·), w n := by
  have h : ∀ n : FermionOccupation Mode,
      matrixCoeff (numberOperator i) n n = if i ∈ n then 1 else 0 := fun n => by
    rcases Finset.decidableMem i n with hi | hi
    · exact matrixCoeff_of_smul_basisState (by
        rw [numberOperator_basisState, if_neg hi, if_neg hi, zero_smul])
    · exact matrixCoeff_of_smul_basisState (by
        rw [numberOperator_basisState, if_pos hi, if_pos hi, one_smul])
  simp only [weightedTrace, h, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]

theorem weightedTrace_totalNumberOperator (w : FermionOccupation Mode → ℂ) :
    weightedTrace w totalNumberOperator =
      ∑ n : FermionOccupation Mode, (fermionParticleNumber n : ℂ) * w n := by
  have h : ∀ n : FermionOccupation Mode,
      matrixCoeff totalNumberOperator n n = (fermionParticleNumber n : ℂ) :=
    fun n => matrixCoeff_of_smul_basisState (totalNumberOperator_basisState n)
  simp only [weightedTrace, h]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

end SecondQuantization
