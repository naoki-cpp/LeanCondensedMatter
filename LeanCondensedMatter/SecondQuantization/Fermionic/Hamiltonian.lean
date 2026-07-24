import LeanCondensedMatter.SecondQuantization.Fermionic.NumberOperator

set_option linter.style.header false

/-!
# Fermionic Hamiltonians

Phase 6 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
free/interaction Hamiltonians, each a `Common.diagonalOperator` (`Common/AlgebraicFock.lean`) whose
eigenvalue at occupation state `n` is the corresponding occupation-dependent scalar (total particle
number, free energy, or interaction energy). Since each `n : FermionOccupation Mode := Finset Mode`
is itself finite regardless of whether `Mode` is, these sums are all over `n` (or `n × n`), **not**
over all of `Mode` — so, unlike an earlier version of this file built from finite sums of
`numberOperator i` over `i : Mode`, none of the three definitions below needs `[Fintype Mode]`.

Field operators are still out of scope (see `CreationAnnihilationFermionic.lean`'s module
docstring); so is anything beyond the algebraic level (no self-adjointness, no spectral theory,
no completion) — those are deferred past the algebraic Linked Cluster Theorem, per this track's
design principles.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-! ## Free and interaction Hamiltonians -/

omit [LinearOrder Mode] in
/-- **The total number operator**, `N := Σᵢ Nᵢ` — the `Common.diagonalOperator` with eigenvalue
`n.card` (the total particle number) at each occupation state `n`. -/
noncomputable def totalNumberOperator : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Common.diagonalOperator fun n : FermionOccupation Mode => (fermionParticleNumber n : ℂ)

omit [LinearOrder Mode] in
theorem totalNumberOperator_basisState (n : FermionOccupation Mode) :
    totalNumberOperator (basisState n) = (fermionParticleNumber n : ℂ) • basisState n :=
  Common.diagonalOperator_basisState _ n

omit [LinearOrder Mode] in
/-- **The free (non-interacting) Hamiltonian** for a dispersion `ε : Mode → ℝ`,
`H₀ := Σᵢ ε(i) Nᵢ` — the `Common.diagonalOperator` with eigenvalue `Σᵢ∈n ε(i)` at each occupation
state `n`. -/
noncomputable def freeHamiltonian (ε : Mode → ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Common.diagonalOperator fun n : FermionOccupation Mode => (∑ i ∈ n, (ε i : ℂ))

omit [LinearOrder Mode] in
theorem freeHamiltonian_basisState (ε : Mode → ℝ) (n : FermionOccupation Mode) :
    freeHamiltonian ε (basisState n) = (∑ i ∈ n, (ε i : ℂ)) • basisState n :=
  Common.diagonalOperator_basisState _ n

omit [LinearOrder Mode] in
/-- **A density-density interaction Hamiltonian** for a coupling `V : Mode → Mode → ℝ`,
`H_int := Σᵢⱼ V(i,j) Nᵢ Nⱼ` — the `Common.diagonalOperator` with eigenvalue `Σᵢ∈n Σⱼ∈n V(i,j)` at
each occupation state `n`, matching `Nᵢ Nⱼ`'s eigenvalue `[i ∈ n] · [j ∈ n]` on occupation numbers.

**Summation convention, fixed explicitly since it is not forced by the physics alone:** the sum
runs over *every* ordered pair `(i, j) : Mode × Mode`, including `i = j` (contributing `V(i,i) Nᵢ`,
since `Nᵢ² = Nᵢ` on occupation numbers), with **no `1/2` prefactor** and **no assumption that `V`
is symmetric**. Consequently, for symmetric `V` this double-counts each unordered pair `{i, j}`
with `i ≠ j` (contributing `V(i,j) + V(j,i) = 2V(i,j)`) relative to the more common physics
convention `H_int = ½ Σᵢⱼ V(i,j) Nᵢ Nⱼ` (summed the same way) or `Σ_{i<j} V(i,j) Nᵢ Nⱼ`. Callers
building a specific physical model must choose `V` (and, if matching a `½ Σ` convention, halve it)
accordingly — this file makes no claim about which convention `V` follows.

This interaction is diagonal in the occupation-number basis (as `interactionHamiltonian_basisState`
below shows) and hence commutes with `freeHamiltonian`/`numberOperator` — a genuinely restrictive
special case, not a general quartic interaction. A general fermionic interaction
`Σᵢⱼₖₗ V(i,j,k,l) cᵢ† cⱼ† cₖ cₗ` (not basis-diagonal, needed for a non-trivial Wick/Dyson
expansion) is a separate future target; see `notes/roadmaps/second-quantization.md`. -/
noncomputable def interactionHamiltonian (V : Mode → Mode → ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Common.diagonalOperator fun n : FermionOccupation Mode => (∑ i ∈ n, ∑ j ∈ n, (V i j : ℂ))

omit [LinearOrder Mode] in
theorem interactionHamiltonian_basisState (V : Mode → Mode → ℝ) (n : FermionOccupation Mode) :
    interactionHamiltonian V (basisState n) =
      (∑ i ∈ n, ∑ j ∈ n, (V i j : ℂ)) • basisState n :=
  Common.diagonalOperator_basisState _ n

end SecondQuantization
