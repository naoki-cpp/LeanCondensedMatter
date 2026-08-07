import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.UnboundedExpectation
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option linter.style.header false

/-!
# Mode-level summability for the completed free fermion Gibbs state

The trace-class construction in `FreeGibbs.lean` takes absolute summability of the Boltzmann
weights over all finite occupation configurations as its minimal analytic hypothesis.  For a free
fermion system this condition can be reduced to a more useful one-particle criterion.

Writing

```text
qᵢ = exp (-β εᵢ),
```

the occupation weight factors as `∏ i ∈ n, qᵢ`.  Mathlib's summability theorem for products over
all finite subsets then shows that `Summable q` is sufficient for the completed Gibbs state to
exist.  The same argument gives the infinite-mode fermionic partition-product formula

```text
Z(β) = ∏' i, (1 + exp (-β εᵢ)).
```

No explicit finiteness or countability typeclass is imposed on `Mode`; the summability hypothesis
itself carries the required analytic restriction.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*}

/-- The one-particle free Boltzmann factor `qᵢ = exp (-β εᵢ)`. -/
noncomputable def completedFreeModeBoltzmannWeight
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) : ℝ :=
  Real.exp (-β * ε i)

@[simp]
theorem completedFreeModeBoltzmannWeight_pos
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    0 < completedFreeModeBoltzmannWeight ε β i := by
  exact Real.exp_pos _

@[simp]
theorem completedFreeModeBoltzmannWeight_nonneg
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    0 ≤ completedFreeModeBoltzmannWeight ε β i :=
  (completedFreeModeBoltzmannWeight_pos ε β i).le

/-- The free occupation Boltzmann weight factors into the one-particle Boltzmann factors of the
occupied modes. -/
theorem completedFreeBoltzmannRealWeight_eq_prod
    (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    completedFreeBoltzmannRealWeight ε β n =
      ∏ i ∈ n, completedFreeModeBoltzmannWeight ε β i := by
  calc
    completedFreeBoltzmannRealWeight ε β n =
        Real.exp (-β * ∑ i ∈ n, ε i) := by
      rfl
    _ = Real.exp (∑ i ∈ n, (-β * ε i)) := by
      congr 1
      rw [Finset.mul_sum]
    _ = ∏ i ∈ n, Real.exp (-β * ε i) := by
      exact Real.exp_sum n (fun i => -β * ε i)
    _ = ∏ i ∈ n, completedFreeModeBoltzmannWeight ε β i := by
      rfl

/-- A mode-level sufficient hypothesis for the completed free Gibbs state: the one-particle
Boltzmann factors are summable over modes. -/
def CompletedFreeModeBoltzmannSummable (ε : Mode → ℝ) (β : ℝ) : Prop :=
  Summable (completedFreeModeBoltzmannWeight ε β)

/-- Mode-level Boltzmann summability implies summability of the free Boltzmann weights over every
finite fermionic occupation configuration. -/
theorem completedFreeBoltzmannRealWeight_summable_of_mode
    (ε : Mode → ℝ) (β : ℝ)
    (hmode : CompletedFreeModeBoltzmannSummable ε β) :
    Summable (completedFreeBoltzmannRealWeight ε β) := by
  have hprod :
      Summable fun n : Finset Mode =>
        ∏ i ∈ n, completedFreeModeBoltzmannWeight ε β i :=
    summable_finsetProd_of_summable_nonneg
      (completedFreeModeBoltzmannWeight_nonneg ε β) hmode
  have hweights :
      completedFreeBoltzmannRealWeight ε β =
        fun n : Occupation Mode =>
          ∏ i ∈ n, completedFreeModeBoltzmannWeight ε β i := by
    funext n
    exact completedFreeBoltzmannRealWeight_eq_prod ε β n
  rw [hweights]
  exact hprod

/-- The one-particle summability criterion is sufficient for the trace-class Gibbs hypothesis used
by `completedFreeGibbsDensityOperator`. -/
theorem completedFreeGibbsSummable_of_mode
    (ε : Mode → ℝ) (β : ℝ)
    (hmode : CompletedFreeModeBoltzmannSummable ε β) :
    CompletedFreeGibbsSummable ε β := by
  unfold CompletedFreeGibbsSummable
  exact (completedFreeBoltzmannRealWeight_summable_of_mode ε β hmode).norm

/-- Under the one-particle summability criterion, the completed free fermion partition function is
the infinite product `∏ᵢ (1 + exp (-β εᵢ))`. -/
theorem completedFreePartitionFunction_eq_tprod_one_add
    (ε : Mode → ℝ) (β : ℝ)
    (hmode : CompletedFreeModeBoltzmannSummable ε β) :
    completedFreePartitionFunction ε β =
      ∏' i : Mode, (1 + completedFreeModeBoltzmannWeight ε β i) := by
  have hprod :
      Summable fun n : Finset Mode =>
        ∏ i ∈ n, completedFreeModeBoltzmannWeight ε β i :=
    summable_finsetProd_of_summable_nonneg
      (completedFreeModeBoltzmannWeight_nonneg ε β) hmode
  rw [completedFreePartitionFunction]
  calc
    (∑' n : Occupation Mode, completedFreeBoltzmannRealWeight ε β n) =
        ∑' n : Finset Mode, ∏ i ∈ n, completedFreeModeBoltzmannWeight ε β i := by
      apply tsum_congr
      intro n
      exact completedFreeBoltzmannRealWeight_eq_prod ε β n
    _ = ∏' i : Mode, (1 + completedFreeModeBoltzmannWeight ε β i) :=
      (tprod_one_add hprod).symm

/-- The mode-level criterion supplies the positivity hypothesis for normalization without requiring
callers to first construct the occupation-level summability proof explicitly. -/
theorem completedFreePartitionFunction_pos_of_mode
    (ε : Mode → ℝ) (β : ℝ)
    (hmode : CompletedFreeModeBoltzmannSummable ε β) :
    0 < completedFreePartitionFunction ε β :=
  completedFreePartitionFunction_pos ε β
    (completedFreeGibbsSummable_of_mode ε β hmode)

end
end Fermionic
end SecondQuantization
