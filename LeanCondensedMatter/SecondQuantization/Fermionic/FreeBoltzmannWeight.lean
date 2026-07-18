import LeanCondensedMatter.SecondQuantization.Fermionic.ThermalGreenFunction

set_option linter.style.header false

/-!
# The free Boltzmann weight, and the genuine free thermal Green function

Phase 9 (`notes/roadmaps/second-quantization.md`): specializes `thermalExpectation`,
`partitionFunction`, and `thermalGreenFunction` — all previously stated for an *arbitrary* complex
weight `w` — to the genuine free Gibbs weight `w(n) = e^{-β E(n)}`, `E(n) := Σᵢ∈n ε(i)`, for the
same dispersion `ε` used by `imaginaryTimeEvolve`. This closes both gaps
`ThermalGreenFunction.lean`'s module docstring flagged: `w` is now a genuine positive weight, and
it is the free weight for the same `ε` the evolution uses.

**This is the free Gibbs-weight specialization of the time-ordered correlator, not yet the full
Matsubara Green-function apparatus.** `freeThermalGreenFunction` accepts any `β : ℝ` and `τ, τ' :
ℝ` with no further structure — the standard finite-temperature package (`0 < β`, the fundamental
domain `0 ≤ τ, τ' ≤ β`, KMS antiperiodicity away from coincident-time discontinuities, together
with the corresponding one-sided boundary relations) is not yet
established. The closed-form free-fermion occupation number `⟨N_i⟩₀ = 1/(e^{βε_i}+1)` is now
proved in `Fermionic/FreePartitionFunction.lean`, and the closed-form two-point Green function
(`G₀,ᵢⱼ = 0` for `i ≠ j`, its explicit `τ`-dependence for `i = j`) in
`Fermionic/FreeTwoPointFunction.lean`; only the KMS/fundamental-domain package remains future
work.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The free Boltzmann weight**, `w(n) := e^{-β E(n)}`, `E(n) := Σᵢ∈n ε(i)` — the genuine Gibbs
weight for the free Hamiltonian `freeHamiltonian ε` at inverse temperature `β`. -/
noncomputable def freeBoltzmannWeight (ε : Mode → ℝ) (β : ℝ) (n : FermionOccupation Mode) : ℂ :=
  Complex.exp (-(β : ℂ) * ∑ i ∈ n, (ε i : ℂ))

omit [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] in
/-- **The free Boltzmann weight is a cast of a positive real number.** Makes its positivity (hence
non-vanishing) available directly from `Real.exp_pos`, without reasoning about `Complex.exp` on a
complex argument. -/
theorem freeBoltzmannWeight_eq_ofReal (ε : Mode → ℝ) (β : ℝ) (n : FermionOccupation Mode) :
    freeBoltzmannWeight ε β n = ((Real.exp (-β * ∑ i ∈ n, ε i) : ℝ) : ℂ) := by
  rw [freeBoltzmannWeight,
    show -(β : ℂ) * ∑ i ∈ n, (ε i : ℂ) = ((-β * ∑ i ∈ n, ε i : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_exp]

omit [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] in
theorem freeBoltzmannWeight_ne_zero (ε : Mode → ℝ) (β : ℝ) (n : FermionOccupation Mode) :
    freeBoltzmannWeight ε β n ≠ 0 :=
  Complex.exp_ne_zero _

omit [DecidableEq Mode] [LinearOrder Mode] in
/-- **The free partition function is nonzero.** `Z(w) := Σₙ w(n)` is a sum of casts of strictly
positive reals (`Real.exp_pos`) over the nonempty `Fintype` `FermionOccupation Mode` (it always
contains `fermionVacuum`), hence itself a positive real cast, hence nonzero. -/
theorem partitionFunction_freeBoltzmannWeight_ne_zero (ε : Mode → ℝ) (β : ℝ) :
    partitionFunction (freeBoltzmannWeight ε β) ≠ 0 := by
  rw [partitionFunction]
  simp_rw [freeBoltzmannWeight_eq_ofReal]
  rw [← Complex.ofReal_sum]
  refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
  exact Finset.sum_pos (fun n _ => Real.exp_pos _) Finset.univ_nonempty

/-- **The free partition function**, `Z₀(β) := Σₙ e^{-β E(n)}`: `partitionFunction` specialized to
`freeBoltzmannWeight`. -/
noncomputable def freePartitionFunction (ε : Mode → ℝ) (β : ℝ) : ℂ :=
  partitionFunction (freeBoltzmannWeight ε β)

omit [DecidableEq Mode] [LinearOrder Mode] in
theorem freePartitionFunction_ne_zero (ε : Mode → ℝ) (β : ℝ) : freePartitionFunction ε β ≠ 0 :=
  partitionFunction_freeBoltzmannWeight_ne_zero ε β

/-- **The free thermal expectation value**, `⟨A⟩₀,β`: `thermalExpectation` specialized to
`freeBoltzmannWeight`. -/
noncomputable def freeThermalExpectation (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : ℂ :=
  thermalExpectation (freeBoltzmannWeight ε β) A

/-- **The free thermal two-point correlator `G₀`**: `thermalGreenFunction` specialized to the free
Boltzmann weight for the *same* dispersion `ε` used in the imaginary-time evolution — `w` is a
genuine positive Gibbs weight (`partitionFunction_freeBoltzmannWeight_ne_zero`) for the same `ε`
the evolution uses, closing the two gaps `ThermalGreenFunction.lean` flagged. See the module
docstring for what finite-temperature structure (KMS antiperiodicity, the fundamental domain)
still remains before this is the full Matsubara Green function. -/
noncomputable def freeThermalGreenFunction (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ) : ℂ :=
  thermalGreenFunction ε (freeBoltzmannWeight ε β) i j τ τ'

end SecondQuantization
