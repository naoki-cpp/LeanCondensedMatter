import LeanCondensedMatter.SecondQuantization.ThermalExpectationFermionic
import LeanCondensedMatter.Combinatorics.CumulantFactorization

set_option linter.style.header false

/-!
# Connecting thermal occupation correlators to Track B's moment-cumulant machinery

Phase 8 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the first
bridge between Track D (thermal expectation values on `FockSpaceFermionic`) and Track B (the
abstract moment-cumulant duality on the partition lattice, `Combinatorics/MomentCumulant.lean`,
`Combinatorics/CumulantFactorization.lean`).

`occupationMoment w S := (Σₙ (if S ⊆ n then w n else 0)) / Z(w)` is the thermal expectation value
of the simultaneous occupation of every mode in `S`, `⟨∏ᵢ∈S nᵢ⟩_w`, computed directly as a weighted
sum rather than via an operator product (the `numberOperator i`'s commute as they're simultaneously
diagonal, but `FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode` has no `CommMonoid` structure
under composition to state that with `Finset.prod`, so this file bypasses the issue rather than
solving it). It lands exactly in Track B's `Finset Mode → ℂ` moment-function type, with
`occupationMoment w ⊥ = 1` matching `IsIndependentAcross`'s normalization hypothesis.

This is a first, deliberately modest step: it connects the types and proves the basic sanity facts
(`occupationMoment` at `⊥` and at a singleton). It does *not* yet establish `IsIndependentAcross`
for a genuine Gibbs weight, nor assemble the `log Z = Σ` over connected clusters statement itself —
see `notes/roadmaps/second-quantization.md` for what remains.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The thermal occupation-correlator moment.** `occupationMoment w S` is the (un-normalized)
probability, under the weight `w`, that every mode in `S` is occupied — the thermal expectation
value `⟨∏ᵢ∈S nᵢ⟩_w` of the simultaneous occupation of `S`, computed directly as a weighted sum. -/
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

end SecondQuantization
