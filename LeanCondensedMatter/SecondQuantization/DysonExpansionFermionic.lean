import LeanCondensedMatter.SecondQuantization.ThermalExpectationFermionic

set_option linter.style.header false

/-!
# The formal Dyson series (algebraic, no analytic `exp`)

Phase 7 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
formal (term-by-term) power-series expansion of `exp(-H)` for `H : FockSpaceFermionic Mode →ₗ[ℂ]
FockSpaceFermionic Mode`, and its finite truncations.

This is deliberately *not* the analytic operator exponential: `FockSpaceFermionic Mode` carries no
topology in this development (see `FockSpaceFermionic.lean`'s module docstring — algebraic only,
no Hilbert-space completion), so "`exp(-H)`" itself is not a well-formed term here. What *is*
well-formed, purely algebraically, is each individual term `(-1)ⁿ/n! • Hⁿ` of its would-be Taylor
series, and any finite sum of such terms (a truncation). This suffices for `dysonPartitionFunction`
below to make sense as an honest (if only approximate, at finite truncation order) finite sum,
without asserting any convergence claim. Reaching the genuine `e^{-βH}` Gibbs weight is a later,
explicitly analytic target — see the note at the end of this file.

The imaginary-time interaction-picture expansion `Û_I(τ,τ') = T_τ exp[-∫_{τ'}^τ V̂_I(τ') dτ']`
(the reference route to the physical Dyson series, cf. `finite-temperature-Green-function.tex`
§13.3 in the accompanying physics notes) additionally needs continuous imaginary-time integration,
which is out of scope for the same reason. This file's finite truncations are a first, purely
algebraic approximation to that expansion at `V = 0` (i.e. for `H = H₀` alone); splitting `H₀ + V`
combinatorially by perturbation order is left to a later phase.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-! ## The formal series, term by term -/

/-- **The `n`-th term** of the formal Taylor series for `exp(-H)`, `(-1)ⁿ/n! • Hⁿ`. Purely
algebraic: `n!` is invertible in `ℂ`, so this is well-defined for every `n` without any topology
or convergence claim. -/
noncomputable def dysonTerm (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ((-1 : ℂ) ^ n / n.factorial) • H ^ n

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem dysonTerm_zero (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    dysonTerm H 0 = LinearMap.id := by
  simp [dysonTerm, Module.End.one_eq_id]

omit [LinearOrder Mode] [Fintype Mode] in
theorem dysonTerm_one (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    dysonTerm H 1 = -H := by
  simp [dysonTerm]

/-! ## Finite truncations -/

/-- **The order-`N` truncation** of the formal Dyson series for `exp(-H)`,
`Σₙ₌₀^N (-1)ⁿ/n! • Hⁿ`. -/
noncomputable def dysonTruncation (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (N : ℕ) : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ∑ n ∈ Finset.range (N + 1), dysonTerm H n

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem dysonTruncation_zero (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    dysonTruncation H 0 = LinearMap.id := by
  simp [dysonTruncation]

omit [LinearOrder Mode] [Fintype Mode] in
theorem dysonTruncation_succ (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (N : ℕ) : dysonTruncation H (N + 1) = dysonTruncation H N + dysonTerm H (N + 1) :=
  Finset.sum_range_succ _ _

/-- **The order-`N` formal partition function**: `traceFock` of the order-`N` truncated Dyson
series, standing in for the (not-yet-analytic) `Tr(e^{-βH})` at finite truncation order. -/
noncomputable def dysonPartitionFunction (H : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (N : ℕ) : ℂ :=
  traceFock (dysonTruncation H N)

/-! ## Sanity check: the free Hamiltonian's truncated series has the expected eigenvalue -/

theorem freeHamiltonian_pow_basisState (ε : Mode → ℝ) (n : FermionOccupation Mode) (k : ℕ) :
    (freeHamiltonian ε ^ k) (basisState n) = ((∑ i ∈ n, (ε i : ℂ)) ^ k) • basisState n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, freeHamiltonian_basisState, smul_smul,
      ← pow_succ]

/-- **On the free Hamiltonian**, `dysonTerm` reduces to the expected scalar Taylor-series term of
`exp(-E(n))`, where `E(n) := Σ_{i∈n} ε(i)` is the occupation state's energy
(`freeHamiltonian_basisState`). -/
theorem dysonTerm_freeHamiltonian_basisState (ε : Mode → ℝ) (n : FermionOccupation Mode)
    (k : ℕ) :
    dysonTerm (freeHamiltonian ε) k (basisState n) =
      ((-1 : ℂ) ^ k / k.factorial * (∑ i ∈ n, (ε i : ℂ)) ^ k) • basisState n := by
  rw [dysonTerm, LinearMap.smul_apply, freeHamiltonian_pow_basisState, smul_smul]

/-- **On the free Hamiltonian**, `dysonTruncation H N` reduces to the order-`N` partial sum of the
scalar Taylor series for `exp(-E(n))`. -/
theorem dysonTruncation_freeHamiltonian_basisState (ε : Mode → ℝ) (n : FermionOccupation Mode)
    (N : ℕ) :
    dysonTruncation (freeHamiltonian ε) N (basisState n) =
      (∑ k ∈ Finset.range (N + 1),
        (-1 : ℂ) ^ k / k.factorial * (∑ i ∈ n, (ε i : ℂ)) ^ k) • basisState n := by
  simp only [dysonTruncation, LinearMap.sum_apply, dysonTerm_freeHamiltonian_basisState]
  rw [← Finset.sum_smul]

/-- **The order-`N` formal partition function of the free Hamiltonian** is the expected finite sum
over occupation states of the order-`N` partial sum of the scalar Taylor series for `exp(-E(n))`. -/
theorem dysonPartitionFunction_freeHamiltonian (ε : Mode → ℝ) (N : ℕ) :
    dysonPartitionFunction (freeHamiltonian ε) N =
      ∑ n : FermionOccupation Mode,
        ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ k / k.factorial * (∑ i ∈ n, (ε i : ℂ)) ^ k := by
  simp only [dysonPartitionFunction, traceFock, matrixCoeff,
    dysonTruncation_freeHamiltonian_basisState, Finsupp.smul_apply]
  simp [basisState]

/-! ## What remains

The genuine `weightedTrace`/`partitionFunction` against the Gibbs weight `n ↦ e^{-βE(n)}` needs
the analytic exponential on `ℂ` applied to each (finite, real) eigenvalue `E(n)` — an easy,
purely scalar step that does *not* need `dysonTerm`/`dysonTruncation` above, and belongs to a
later phase once the project is ready to introduce `Real.exp`/`Complex.exp` for this purpose.
`dysonTerm`/`dysonTruncation` are the *operator*-level, `V`-including machinery: splitting
`H = H₀ + V` combinatorially by perturbation order (the actual interaction-picture Dyson series)
remains for a later phase.
-/

end SecondQuantization
