import LeanCondensedMatter.SecondQuantization.ThermalExpectationFermionic
import LeanCondensedMatter.Combinatorics.CumulantFactorization

set_option linter.style.header false

/-!
# Connecting thermal occupation correlators to Track B's moment-cumulant machinery

Phase 8 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the first
bridge between Track D (thermal expectation values on `FockSpaceFermionic`) and Track B (the
abstract moment-cumulant duality on the partition lattice, `Combinatorics/MomentCumulant.lean`,
`Combinatorics/CumulantFactorization.lean`).

`occupationMoment w S := (Σₙ (if S ⊆ n then w n else 0)) / Z(w)` is the normalized thermal
expectation value of the simultaneous occupation of every mode in `S`, `⟨∏ᵢ∈S nᵢ⟩_w`, computed
directly as a weighted sum rather than via an operator product (the `numberOperator i`'s commute as
they're simultaneously diagonal, but `FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode` has no
`CommMonoid` structure under composition to state that with `Finset.prod`, so this file bypasses
the issue rather than solving it). It lands exactly in Track B's `Finset Mode → ℂ` moment-function
type, with
`occupationMoment w ⊥ = 1` matching `IsIndependentAcross`'s normalization hypothesis.

`occupationProjector S` supplies the operator-level witness `∏ᵢ∈S nᵢ` (diagonal in the
occupation-number basis, built via `Finsupp.lift` exactly as `create`/`annihilate` are), with
`thermalExpectation_occupationProjector` confirming it reproduces `occupationMoment` and
`occupationProjector_singleton` confirming it agrees with `numberOperator` at a single mode.

This remains a modest step: it does *not* yet establish `IsIndependentAcross` for a genuine
product/Gibbs weight, nor assemble the `log Z = Σ` over connected clusters statement itself — see
`notes/roadmaps/second-quantization.md` for what remains.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The thermal occupation-correlator moment.** `occupationMoment w S` is the normalized weighted
occupation correlator under the weight `w` — the thermal expectation value `⟨∏ᵢ∈S nᵢ⟩_w` of the
simultaneous occupation of `S`, computed directly as a weighted sum. For positive real weights (a
genuine Boltzmann weight) it is the probability that every mode in `S` is occupied; `w` here is an
arbitrary complex-valued weight, so no probabilistic interpretation is assumed in general. As with
`thermalExpectation`, division by `partitionFunction w` is only physically meaningful when
`partitionFunction w ≠ 0`. -/
noncomputable def occupationMoment (w : FermionOccupation Mode → ℂ) (S : Finset Mode) : ℂ :=
  (∑ n ∈ (Finset.univ : Finset (FermionOccupation Mode)).filter (S ⊆ ·), w n) /
    partitionFunction w

omit [LinearOrder Mode] in
/-- **`occupationMoment` at `⊥` is `1`** (given a nonzero partition function): every occupation
state vacuously contains the empty set of modes, so the numerator is exactly `Z(w)`. This matches
`Finpartition.IsIndependentAcross`'s `m ⊥ = 1` normalization hypothesis. -/
theorem occupationMoment_bot {w : FermionOccupation Mode → ℂ} (hZ : partitionFunction w ≠ 0) :
    occupationMoment w ⊥ = 1 := by
  have hfilter : (Finset.univ : Finset (FermionOccupation Mode)).filter ((⊥ : Finset Mode) ⊆ ·) =
      Finset.univ := by
    ext n; simp
  rw [occupationMoment, hfilter]
  exact div_self hZ

/-- **`occupationMoment` at a singleton `{i}` is the thermal expectation of `numberOperator i`.**
Connects the weighted-sum definition back to Track D's operator-level `thermalExpectation`. -/
theorem occupationMoment_singleton (w : FermionOccupation Mode → ℂ) (i : Mode) :
    occupationMoment w {i} = thermalExpectation w (numberOperator i) := by
  rw [occupationMoment, thermalExpectation, weightedTrace_numberOperator]
  have hfilter : (Finset.univ : Finset (FermionOccupation Mode)).filter
      (({i} : Finset Mode) ⊆ ·) = (Finset.univ : Finset (FermionOccupation Mode)).filter
      (i ∈ ·) := by
    ext n; simp [Finset.subset_iff]
  rw [hfilter]

/-! ## The occupation projector: an operator-level witness for `occupationMoment` -/

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The occupation-projector operator, on a basis state.** `basisState n` if `n` occupies every
mode of `S`, `0` otherwise — the simultaneous-occupation observable `∏ᵢ∈S nᵢ` at the basis-state
level. -/
noncomputable def occupationProjectorBasis (S : Finset Mode) (n : FermionOccupation Mode) :
    FockSpaceFermionic Mode :=
  if S ⊆ n then basisState n else 0

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The occupation-projector operator**, extended linearly from `occupationProjectorBasis`.
Diagonal in the occupation-number basis, so it commutes with itself and with every
`numberOperator i`, without needing a `CommMonoid` structure on
`FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode` under composition. -/
noncomputable def occupationProjector (S : Finset Mode) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Finsupp.lift (FockSpaceFermionic Mode) ℂ (FermionOccupation Mode) (occupationProjectorBasis S)

omit [LinearOrder Mode] [Fintype Mode] in
theorem occupationProjector_basisState (S : Finset Mode) (n : FermionOccupation Mode) :
    occupationProjector S (basisState n) = if S ⊆ n then basisState n else 0 := by
  change Finsupp.lift _ ℂ _ (occupationProjectorBasis S) (Finsupp.single n 1) =
    occupationProjectorBasis S n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index, occupationProjectorBasis]

omit [Fintype Mode] in
/-- **`occupationProjector` at the singleton `{i}` is exactly `numberOperator i`.** Confirms the
operator-level definition matches the physical "number operator" reading. -/
theorem occupationProjector_singleton (i : Mode) :
    occupationProjector ({i} : Finset Mode) = numberOperator i := by
  apply linearMap_ext_basisState
  intro n
  simp [occupationProjector_basisState, numberOperator_basisState, Finset.singleton_subset_iff]

omit [LinearOrder Mode] in
/-- **`thermalExpectation` of `occupationProjector S` is `occupationMoment w S`.** The operator-
level bridge promised by `occupationMoment`'s docstring: the simultaneous-occupation observable's
thermal expectation value agrees with the direct weighted-sum definition. -/
theorem thermalExpectation_occupationProjector (w : FermionOccupation Mode → ℂ) (S : Finset Mode) :
    thermalExpectation w (occupationProjector S) = occupationMoment w S := by
  rw [thermalExpectation, occupationMoment]
  congr 1
  have h : ∀ n : FermionOccupation Mode,
      matrixCoeff (occupationProjector S) n n = if S ⊆ n then 1 else 0 := fun n => by
    by_cases hs : S ⊆ n
    · exact matrixCoeff_of_smul_basisState (by
        rw [occupationProjector_basisState, if_pos hs, if_pos hs, one_smul])
    · exact matrixCoeff_of_smul_basisState (by
        rw [occupationProjector_basisState, if_neg hs, if_neg hs, zero_smul])
  simp only [weightedTrace, h, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]

end SecondQuantization
