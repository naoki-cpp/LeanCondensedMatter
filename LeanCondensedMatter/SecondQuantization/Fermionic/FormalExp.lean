import LeanCondensedMatter.SecondQuantization.Fermionic.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# The formal operator exponential (algebraic, no analytic `exp`)

Phase 7 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
formal (term-by-term) power-series expansion of `exp(-H)` for `H : FockSpaceFermionic Mode →ₗ[ℂ]
FockSpaceFermionic Mode`, and its finite truncations.

**Naming note.** `formalExpTerm`/`formalExpTruncation` deliberately do *not* use "Dyson" in their
name, even though `(-1)ⁿ/n! • Hⁿ` is literally the `n`-th term of a Taylor expansion of `exp(-H)`.
The name `DysonExpansion`/`dysonTerm` is reserved for the *genuine* physical Dyson series — the
imaginary-time interaction-picture expansion `Û_I(τ,τ') = T_τ exp[-∫_{τ'}^τ V̂_I(τ') dτ']`, which
splits `H = H₀ + V` combinatorially by perturbation order and needs continuous imaginary-time
integration — a genuinely different, not-yet-started future target (see
`notes/roadmaps/second-quantization.md`'s Phase 9 plan). This file is that Dyson series' `V = 0`
degenerate case, and only that.

This is deliberately *not* the analytic operator exponential either: `FockSpaceFermionic Mode`
carries no topology in this development (see `FockSpaceFermionic.lean`'s module docstring —
algebraic only, no Hilbert-space completion), so "`exp(-H)`" itself is not a well-formed term
here. What *is* well-formed, purely algebraically, is each individual term `(-1)ⁿ/n! • Hⁿ` of its
would-be Taylor series, and any finite sum of such terms (a truncation) — enough for
`formalExpPartitionFunction` below to make sense as an honest (if only approximate, at finite
truncation order) finite sum, without asserting any convergence claim. Reaching the genuine
`e^{-βH}` Gibbs weight is a later, explicitly analytic target — see the note at the end of this
file.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-! ## The formal series, term by term -/

/-- **The `n`-th term** of the formal Taylor series for `exp(-H)`, `(-1)ⁿ/n! • Hⁿ`. Purely
algebraic: `n!` is invertible in `ℂ`, so this is well-defined for every `n` without any topology
or convergence claim. -/
noncomputable def formalExpTerm (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (n : ℕ) : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ((-1 : ℂ) ^ n / n.factorial) • H ^ n

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem formalExpTerm_zero (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    formalExpTerm H 0 = LinearMap.id := by
  simp [formalExpTerm, Module.End.one_eq_id]

omit [LinearOrder Mode] [Fintype Mode] in
theorem formalExpTerm_one (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    formalExpTerm H 1 = -H := by
  simp [formalExpTerm]

/-! ## Finite truncations -/

/-- **The order-`N` truncation** of the formal exponential series for `exp(-H)`,
`Σₙ₌₀^N (-1)ⁿ/n! • Hⁿ`. -/
noncomputable def formalExpTruncation (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (N : ℕ) : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ∑ n ∈ Finset.range (N + 1), formalExpTerm H n

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem formalExpTruncation_zero (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    formalExpTruncation H 0 = LinearMap.id := by
  simp [formalExpTruncation]

omit [LinearOrder Mode] [Fintype Mode] in
theorem formalExpTruncation_succ (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (N : ℕ) :
    formalExpTruncation H (N + 1) = formalExpTruncation H N + formalExpTerm H (N + 1) :=
  Finset.sum_range_succ _ _

/-- **The order-`N` formal partition function**: `traceFock` of the order-`N` truncated formal
exponential series, standing in for the (not-yet-analytic) `Tr(e^{-βH})` at finite truncation
order. -/
noncomputable def formalExpPartitionFunction
    (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (N : ℕ) : ℂ :=
  traceFock (formalExpTruncation H N)

/-! ## Sanity check: the free Hamiltonian's truncated series has the expected eigenvalue -/

theorem freeHamiltonian_pow_basisState (ε : Mode → ℝ) (n : FermionOccupation Mode) (k : ℕ) :
    (freeHamiltonian ε ^ k) (basisState n) = ((∑ i ∈ n, (ε i : ℂ)) ^ k) • basisState n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, freeHamiltonian_basisState, smul_smul,
      ← pow_succ]

/-- **On the free Hamiltonian**, `formalExpTerm` reduces to the expected scalar Taylor-series
term of `exp(-E(n))`, where `E(n) := Σ_{i∈n} ε(i)` is the occupation state's energy
(`freeHamiltonian_basisState`). -/
theorem formalExpTerm_freeHamiltonian_basisState (ε : Mode → ℝ) (n : FermionOccupation Mode)
    (k : ℕ) :
    formalExpTerm (freeHamiltonian ε) k (basisState n) =
      ((-1 : ℂ) ^ k / k.factorial * (∑ i ∈ n, (ε i : ℂ)) ^ k) • basisState n := by
  rw [formalExpTerm, LinearMap.smul_apply, freeHamiltonian_pow_basisState, smul_smul]

/-- **On the free Hamiltonian**, `formalExpTruncation H N` reduces to the order-`N` partial sum
of the scalar Taylor series for `exp(-E(n))`. -/
theorem formalExpTruncation_freeHamiltonian_basisState (ε : Mode → ℝ)
    (n : FermionOccupation Mode) (N : ℕ) :
    formalExpTruncation (freeHamiltonian ε) N (basisState n) =
      (∑ k ∈ Finset.range (N + 1),
        (-1 : ℂ) ^ k / k.factorial * (∑ i ∈ n, (ε i : ℂ)) ^ k) • basisState n := by
  simp only [formalExpTruncation, LinearMap.sum_apply, formalExpTerm_freeHamiltonian_basisState]
  rw [← Finset.sum_smul]

/-- **The order-`N` truncated Boltzmann weight** of an occupation state `n`, for the free
Hamiltonian's dispersion `ε`: the order-`N` partial sum of the scalar Taylor series for
`exp(-E(n))`, `E(n) := Σ_{i∈n} ε(i)`. This is exactly the scalar produced by
`formalExpTruncation_freeHamiltonian_basisState`, named separately so it can be fed to
`partitionFunction`/`weightedTrace` (`WeightedDiagonalFunctional.lean`) as a genuine (if only
finite-order-approximate) weight. -/
noncomputable def truncatedBoltzmannWeight (ε : Mode → ℝ) (N : ℕ) (n : FermionOccupation Mode) :
    ℂ :=
  ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ k / k.factorial * (∑ i ∈ n, (ε i : ℂ)) ^ k

/-- **The free Hamiltonian's truncated formal exponential is diagonal**, with `(n, n)` matrix
coefficient exactly `truncatedBoltzmannWeight ε N n`. -/
theorem matrixCoeff_formalExpTruncation_freeHamiltonian (ε : Mode → ℝ) (N : ℕ)
    (n : FermionOccupation Mode) :
    matrixCoeff (formalExpTruncation (freeHamiltonian ε) N) n n =
      truncatedBoltzmannWeight ε N n :=
  matrixCoeff_of_smul_basisState (formalExpTruncation_freeHamiltonian_basisState ε n N)

/-- **The order-`N` formal partition function of the free Hamiltonian** is exactly
`partitionFunction` applied to the order-`N` truncated Boltzmann weight — the finite-Taylor-order
approximation to the Gibbs weight has entered `WeightedDiagonalFunctional.lean`'s machinery. -/
theorem traceFock_formalExpTruncation_freeHamiltonian (ε : Mode → ℝ) (N : ℕ) :
    traceFock (formalExpTruncation (freeHamiltonian ε) N) =
      partitionFunction (truncatedBoltzmannWeight ε N) := by
  simp [traceFock, partitionFunction, matrixCoeff_formalExpTruncation_freeHamiltonian]

/-- **Weighted-trace version.** For any additional weight `w`, `weightedTrace w` of the free
Hamiltonian's order-`N` truncated formal exponential is `partitionFunction` of the pointwise
product `w * truncatedBoltzmannWeight ε N`. -/
theorem weightedTrace_formalExpTruncation_freeHamiltonian (ε : Mode → ℝ) (N : ℕ)
    (w : FermionOccupation Mode → ℂ) :
    weightedTrace w (formalExpTruncation (freeHamiltonian ε) N) =
      partitionFunction (fun n => w n * truncatedBoltzmannWeight ε N n) := by
  simp [weightedTrace, partitionFunction, matrixCoeff_formalExpTruncation_freeHamiltonian]

/-- **The order-`N` formal partition function of the free Hamiltonian** is the expected finite sum
over occupation states of the order-`N` partial sum of the scalar Taylor series for `exp(-E(n))`. -/
theorem formalExpPartitionFunction_freeHamiltonian (ε : Mode → ℝ) (N : ℕ) :
    formalExpPartitionFunction (freeHamiltonian ε) N =
      ∑ n : FermionOccupation Mode,
        ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ k / k.factorial * (∑ i ∈ n, (ε i : ℂ)) ^ k :=
  traceFock_formalExpTruncation_freeHamiltonian ε N

/-! ## What remains

The genuine `weightedTrace`/`partitionFunction` against the Gibbs weight `n ↦ e^{-βE(n)}` needs
the analytic exponential on `ℂ` applied to each (finite, real) eigenvalue `E(n)` — an easy,
purely scalar step that does *not* need `formalExpTerm`/`formalExpTruncation` above, and belongs
to a later phase once the project is ready to introduce `Real.exp`/`Complex.exp` for this purpose.

`formalExpTerm`/`formalExpTruncation` are the algebraic, `V = 0` special case of a much larger
future target: the genuine (interaction-picture, `H = H₀ + V`) Dyson series — see this file's
module docstring's naming note. That combinatorial-by-perturbation-order expansion, and the
moment/cumulant formal-power-series machinery connecting it to Track B's partition-lattice Möbius
work, are both separate, not-yet-started future targets.
-/

end SecondQuantization
