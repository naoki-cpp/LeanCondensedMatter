import LeanCondensedMatter.SecondQuantization.Fermionic.WeightedFreeTwoPointFunction
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Common.FiniteOperatorIntegral

set_option linter.style.header false

/-!
# The free Boltzmann weight, and the genuine free thermal Green function

Phase 9 (`notes/roadmaps/second-quantization.md`): specializes `normalizedWeightedDiagonal`,
`weightSum`, and `weightedFreeTwoPointFunction` — all previously stated for an *arbitrary* complex
weight `w` — to the genuine free Gibbs weight `w(n) = e^{-β E(n)}`, `E(n) := Σᵢ∈n ε(i)`, for the
same dispersion `ε` used by `imaginaryTimeEvolve`. This closes both gaps
`WeightedFreeTwoPointFunction.lean`'s module docstring flagged: `w` is now a genuine positive
weight, and it is the free weight for the same `ε` the evolution uses.

**This is the free Gibbs-weight specialization of the time-ordered correlator, not yet the full
Matsubara Green-function apparatus.** `freeGibbsGreenFunction` accepts any `β : ℝ` and `τ, τ' :
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
theorem weightSum_freeBoltzmannWeight_ne_zero (ε : Mode → ℝ) (β : ℝ) :
    weightSum (freeBoltzmannWeight ε β) ≠ 0 := by
  rw [weightSum_eq_sum]
  simp_rw [freeBoltzmannWeight_eq_ofReal]
  rw [← Complex.ofReal_sum]
  refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
  exact Finset.sum_pos (fun n _ => Real.exp_pos _) Finset.univ_nonempty

/-- **The free partition function**, `Z₀(β) := Σₙ e^{-β E(n)}`: `weightSum` specialized to
`freeBoltzmannWeight`. -/
noncomputable def freePartitionFunction (ε : Mode → ℝ) (β : ℝ) : ℂ :=
  weightSum (freeBoltzmannWeight ε β)

omit [DecidableEq Mode] [LinearOrder Mode] in
theorem freePartitionFunction_ne_zero (ε : Mode → ℝ) (β : ℝ) : freePartitionFunction ε β ≠ 0 :=
  weightSum_freeBoltzmannWeight_ne_zero ε β

/-- **The free Gibbs expectation value**, `⟨A⟩₀,β`: `normalizedWeightedDiagonal` specialized to
`freeBoltzmannWeight`. -/
noncomputable def freeGibbsExpectation (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : ℂ :=
  normalizedWeightedDiagonal (freeBoltzmannWeight ε β) A

omit [LinearOrder Mode] in
/-- **`freeGibbsExpectation` scales**: `⟨c • A⟩₀ = c * ⟨A⟩₀`, directly
`normalizedWeightedDiagonal_smul` at `w := freeBoltzmannWeight ε β`. -/
theorem freeGibbsExpectation_smul (ε : Mode → ℝ) (β : ℝ) (c : ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    freeGibbsExpectation ε β (c • A) = c * freeGibbsExpectation ε β A :=
  normalizedWeightedDiagonal_smul c (freeBoltzmannWeight ε β) A

omit [LinearOrder Mode] in
/-- **`freeGibbsExpectation` negates**: `⟨-A⟩₀ = -⟨A⟩₀`, from `freeGibbsExpectation_smul` at
`c := -1`. -/
theorem freeGibbsExpectation_neg (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    freeGibbsExpectation ε β (-A) = - freeGibbsExpectation ε β A := by
  rw [show (-A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) = (-1 : ℂ) • A from
    (neg_one_smul ℂ A).symm, freeGibbsExpectation_smul, neg_one_mul]

omit [LinearOrder Mode] in
/-- **`freeGibbsExpectation` commutes with `operatorIntervalIntegral`**: `⟨∫ F⟩₀ = ∫ ⟨F⟩₀`, given
interval-integrability of every diagonal matrix coefficient `F` contributes — directly
`Common.normalizedWeightedDiagonal_operatorIntervalIntegral` at `w := freeBoltzmannWeight ε β`. -/
theorem freeGibbsExpectation_operatorIntervalIntegral (ε : Mode → ℝ) (β : ℝ)
    (F : ℝ → FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (a b : ℝ)
    (hF : ∀ n : FermionOccupation Mode, IntervalIntegrable
      (fun τ => Common.matrixCoeff (F τ) n n) MeasureTheory.volume a b) :
    freeGibbsExpectation ε β (Common.operatorIntervalIntegral F a b) =
      ∫ τ in a..b, freeGibbsExpectation ε β (F τ) :=
  Common.normalizedWeightedDiagonal_operatorIntervalIntegral (freeBoltzmannWeight ε β) F a b hF

/-- **The free Gibbs two-point correlator `G₀`**: `weightedFreeTwoPointFunction` specialized to the
free Boltzmann weight for the *same* dispersion `ε` used in the imaginary-time evolution — `w` is a
genuine positive Gibbs weight (`weightSum_freeBoltzmannWeight_ne_zero`) for the same `ε`
the evolution uses, closing the two gaps `WeightedFreeTwoPointFunction.lean` flagged. See the
module docstring for what finite-temperature structure (KMS antiperiodicity, the fundamental
domain) still remains before this is the full Matsubara Green function. -/
noncomputable def freeGibbsGreenFunction (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ) : ℂ :=
  weightedFreeTwoPointFunction ε (freeBoltzmannWeight ε β) i j τ τ'

omit [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] in
/-- **`freeBoltzmannWeight` is `Common.boltzmannWeight` at `fermionEnergy`**: both are
`e^{-βE(n)}`, the only difference being which sum (`Σᵢ∈n ε(i)` spelled out directly, vs. routed
through `fermionEnergy`) computes `E(n)`. -/
theorem freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy (ε : Mode → ℝ) (β : ℝ)
    (n : FermionOccupation Mode) :
    freeBoltzmannWeight ε β n = Common.boltzmannWeight (fermionEnergy ε) β n := by
  rw [freeBoltzmannWeight, Common.boltzmannWeight, fermionEnergy]
  push_cast
  ring_nf

omit [LinearOrder Mode] in
/-- **`freeGibbsExpectation` is `Common.gibbsExpectation` at `fermionEnergy`**: both are the
`e^{-βE(n)}`-normalized diagonal functional on the same underlying `AlgebraicFock
(FermionOccupation Mode) = FockSpaceFermionic Mode`, differing only in how the weight's exponent
is spelled (`freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy`) — the bridge PR 6's
application of the general Bloch–de Dominicis theorem
(`Common.BlochDeDominicis.gibbsExpectation_prodComp_eq_sum_pairing`, stated for
`Common.gibbsExpectation`) needs to reach `freeGibbsExpectation`. -/
theorem freeGibbsExpectation_eq_gibbsExpectation (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    freeGibbsExpectation ε β A = Common.gibbsExpectation (fermionEnergy ε) β A := by
  have hw : freeBoltzmannWeight ε β = Common.boltzmannWeight (fermionEnergy ε) β :=
    funext (freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy ε β)
  rw [freeGibbsExpectation, normalizedWeightedDiagonal, Common.gibbsExpectation, hw]

omit [LinearOrder Mode] in
/-- **`freeGibbsExpectation` is additive over a `Finset.sum`**: `⟨∑ᵢ Aᵢ⟩₀ = ∑ᵢ ⟨Aᵢ⟩₀`, via the
`Common.gibbsExpectation` bridge (`freeGibbsExpectation_eq_gibbsExpectation`) and
`Common.gibbsExpectationLinearMap`'s generic `map_sum`. -/
theorem freeGibbsExpectation_finsetSum (ε : Mode → ℝ) (β : ℝ) {ι : Type*} (s : Finset ι)
    (F : ι → FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    freeGibbsExpectation ε β (∑ i ∈ s, F i) = ∑ i ∈ s, freeGibbsExpectation ε β (F i) := by
  simp_rw [freeGibbsExpectation_eq_gibbsExpectation]
  exact map_sum (Common.gibbsExpectationLinearMap (fermionEnergy ε) β) F s

end SecondQuantization
