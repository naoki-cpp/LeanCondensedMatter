import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# A free-evolution time-ordered two-point functional

Phase 9, step 3 (`notes/roadmaps/second-quantization.md`):
`weightedFreeTwoPointFunction ε w i j τ τ' := -⟨T_τ c_i(τ) c_j†(τ')⟩_w`, assembled from the
previous two steps —
`ImaginaryTimeEvolution.lean`'s `imaginaryTimeEvolve` (still only defined for evolution under the
*free* Hamiltonian `H₀ = freeHamiltonian ε`) and `Common/ImaginaryTime/TimeOrdering.lean`'s
`Common.timeOrderedProduct Statistics.fermion` — applied to `annihilate i`/`create j` and
evaluated with `Common.normalizedWeightedDiagonal w`.

**This is not yet the free Gibbs Green function `G₀` in general.** Two independent restrictions
must both hold before that name applies:
- as with `Common.normalizedWeightedDiagonal`/`Common.weightSum`, `w` is an arbitrary complex
  weight here, not necessarily a genuine Boltzmann weight;
- even if `w` *is* a genuine Boltzmann weight, it must be the *free* one associated to the same
  `ε` used in the evolution (`w n = exp(-β Σᵢ∈n ε i)`) — a Boltzmann weight for some other
  Hamiltonian (e.g. one including an interaction) would evolve the operators with the wrong
  generator, since `imaginaryTimeEvolve` only knows about `H₀ = freeHamiltonian ε`.

The identifier `weightedFreeTwoPointFunction` becomes the genuine `G₀` only once both hold.
Neither restriction is encoded in the type here; `FreeBoltzmannWeight.lean`'s
`freeGibbsGreenFunction` specializes to the weight that satisfies both.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The fermionic two-point (imaginary-)time-ordered correlator**,
`G_{ij}(τ, τ') := -⟨T_τ c_i(τ) c_j†(τ')⟩_w`, for the free Hamiltonian's imaginary-time evolution
`c_i(τ) := imaginaryTimeEvolve ε τ (annihilate i)`, `c_j†(τ') := imaginaryTimeEvolve ε τ'
(create j)`, and an arbitrary weight `w`. See the module docstring for what must additionally
hold for this to be the physical free Gibbs Green function `G₀`. -/
noncomputable def weightedFreeTwoPointFunction (ε : Mode → ℝ) (w : FermionOccupation Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  - Common.normalizedWeightedDiagonal w
      (Common.timeOrderedProduct Statistics.fermion
        (imaginaryTimeEvolve ε τ (annihilate i)) (imaginaryTimeEvolve ε τ' (create j)) τ τ')

/-- **For `τ' < τ`**, time-ordering already has `c_i(τ)` to the left: `G_{ij}(τ, τ') =
-⟨c_i(τ) c_j†(τ')⟩_w`. -/
theorem weightedFreeTwoPointFunction_of_gt (ε : Mode → ℝ) (w : FermionOccupation Mode → ℂ)
    (i j : Mode)
    {τ τ' : ℝ} (h : τ' < τ) :
    weightedFreeTwoPointFunction ε w i j τ τ' =
      - Common.normalizedWeightedDiagonal w
          ((imaginaryTimeEvolve ε τ (annihilate i)).comp
            (imaginaryTimeEvolve ε τ' (create j))) := by
  rw [weightedFreeTwoPointFunction, Common.timeOrderedProduct_of_gt Statistics.fermion _ _ h]

/-- **For `τ < τ'`**, time-ordering swaps to `c_j†(τ')` on the left, picking up the fermionic
exchange sign `-1`, which cancels the definition's outer `-1`: `G_{ij}(τ, τ') =
+⟨c_j†(τ') c_i(τ)⟩_w`. This sign — the double negative from the fermionic swap composing with the
Green function's own minus sign — is exactly the standard finite-temperature Green-function
convention. -/
theorem weightedFreeTwoPointFunction_of_lt (ε : Mode → ℝ) (w : FermionOccupation Mode → ℂ)
    (i j : Mode) {τ τ' : ℝ} (h : τ < τ') :
    weightedFreeTwoPointFunction ε w i j τ τ' =
      Common.normalizedWeightedDiagonal w
        ((imaginaryTimeEvolve ε τ' (create j)).comp
          (imaginaryTimeEvolve ε τ (annihilate i))) := by
  rw [weightedFreeTwoPointFunction, Common.timeOrderedProduct_of_lt Statistics.fermion _ _ h,
    Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one, neg_one_smul,
    Common.normalizedWeightedDiagonal, Common.weightedTrace]
  simp only [Common.matrixCoeff, LinearMap.neg_apply, Finsupp.neg_apply, mul_neg,
    Common.normalizedWeightedDiagonal, Common.weightedTrace, Finset.sum_neg_distrib, neg_div,
    neg_neg]

/-- **At equal times**, this selects the `θ(0) = 1/2` convention `Common/ImaginaryTime/TimeOrdering.lean` fixes
— an average of the two one-sided orderings, *not* a claim that the fermionic Green function's two
one-sided limits `G(0⁺)`/`G(0⁻)` agree (they generically don't: `G(0⁺) = -⟨cc†⟩`,
`G(0⁻) = +⟨c†c⟩`, and CAR gives their difference `-⟨cc†⟩ - ⟨c†c⟩ = -⟨{c,c†}⟩ = -1`). -/
theorem weightedFreeTwoPointFunction_self_time (ε : Mode → ℝ) (w : FermionOccupation Mode → ℂ)
    (i j : Mode) (τ : ℝ) :
    weightedFreeTwoPointFunction ε w i j τ τ =
      - Common.normalizedWeightedDiagonal w
          ((2⁻¹ : ℂ) • ((imaginaryTimeEvolve ε τ (annihilate i)).comp
              (imaginaryTimeEvolve ε τ (create j)) +
            (-1 : ℂ) •
              ((imaginaryTimeEvolve ε τ (create j)).comp
                (imaginaryTimeEvolve ε τ (annihilate i))))) := by
  rw [weightedFreeTwoPointFunction, Common.timeOrderedProduct_self_time Statistics.fermion,
    Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]

end SecondQuantization
