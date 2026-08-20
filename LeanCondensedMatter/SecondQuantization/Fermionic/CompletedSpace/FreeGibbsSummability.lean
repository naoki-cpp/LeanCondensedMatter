import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option linter.style.header false

/-!
# Mode-level summability for the completed free fermion Gibbs state

The completed free fermion Gibbs state is the generic pure-point Gibbs state on occupation energies
`fermionEnergy ε`.  Its occupation-level summability follows from the corresponding one-particle
pure-point summability condition.  Writing

```text
qᵢ = exp (-β εᵢ),
```

the occupation weight factors as `∏ i ∈ n, qᵢ`.  Mathlib's summability theorem for products over
all finite subsets then gives both occupation-level Gibbs summability and the partition-product
formula

```text
Z(β) = ∏' i, (1 + exp (-β εᵢ)).
```

No explicit finiteness or countability typeclass is imposed on `Mode`; the summability hypothesis
itself carries the required analytic restriction.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- The free occupation Boltzmann weight factors into the one-particle pure-point Boltzmann weights
of the occupied modes. -/
theorem purePointBoltzmannWeight_fermionEnergy_eq_prod
    (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    purePointBoltzmannWeight (fermionEnergy ε) β n =
      ∏ i ∈ n, purePointBoltzmannWeight ε β i := by
  calc
    purePointBoltzmannWeight (fermionEnergy ε) β n =
        Real.exp (-β * ∑ i ∈ n, ε i) := by
      rfl
    _ = Real.exp (∑ i ∈ n, (-β * ε i)) := by
      congr 1
      rw [Finset.mul_sum]
    _ = ∏ i ∈ n, Real.exp (-β * ε i) := by
      exact Real.exp_sum n (fun i => -β * ε i)
    _ = ∏ i ∈ n, purePointBoltzmannWeight ε β i := by
      rfl

private theorem purePointBoltzmannWeight_fermionEnergy_summable_of_mode
    (ε : Mode → ℝ) (β : ℝ) (hmode : PurePointGibbsSummable ε β) :
    Summable (purePointBoltzmannWeight (fermionEnergy ε) β) := by
  have hprod :
      Summable fun n : Finset Mode =>
        ∏ i ∈ n, purePointBoltzmannWeight ε β i :=
    summable_finsetProd_of_summable_nonneg
      (purePointBoltzmannWeight_nonneg ε β)
      (purePointBoltzmannWeight_summable ε β hmode)
  have hweights :
      purePointBoltzmannWeight (fermionEnergy ε) β =
        fun n : Occupation Mode => ∏ i ∈ n, purePointBoltzmannWeight ε β i := by
    funext n
    exact purePointBoltzmannWeight_fermionEnergy_eq_prod ε β n
  rw [hweights]
  exact hprod

/-- One-particle pure-point Gibbs summability implies summability of the free fermion Gibbs weights
over all finite occupation configurations. -/
theorem purePointGibbsSummable_fermionEnergy_of_mode
    (ε : Mode → ℝ) (β : ℝ) (hmode : PurePointGibbsSummable ε β) :
    PurePointGibbsSummable (fermionEnergy ε) β := by
  unfold PurePointGibbsSummable
  exact (purePointBoltzmannWeight_fermionEnergy_summable_of_mode ε β hmode).norm

/-- Under one-particle pure-point Gibbs summability, the free fermion partition function is the
infinite product `∏ᵢ (1 + exp (-β εᵢ))`. -/
theorem purePointPartitionFunction_fermionEnergy_eq_tprod_one_add
    (ε : Mode → ℝ) (β : ℝ) (hmode : PurePointGibbsSummable ε β) :
    purePointPartitionFunction (fermionEnergy ε) β =
      ∏' i : Mode, (1 + purePointBoltzmannWeight ε β i) := by
  have hprod :
      Summable fun n : Finset Mode =>
        ∏ i ∈ n, purePointBoltzmannWeight ε β i :=
    summable_finsetProd_of_summable_nonneg
      (purePointBoltzmannWeight_nonneg ε β)
      (purePointBoltzmannWeight_summable ε β hmode)
  rw [purePointPartitionFunction]
  calc
    (∑' n : Occupation Mode, purePointBoltzmannWeight (fermionEnergy ε) β n) =
        ∑' n : Finset Mode, ∏ i ∈ n, purePointBoltzmannWeight ε β i := by
      apply tsum_congr
      intro n
      exact purePointBoltzmannWeight_fermionEnergy_eq_prod ε β n
    _ = ∏' i : Mode, (1 + purePointBoltzmannWeight ε β i) :=
      (tprod_one_add hprod).symm

end
end Fermionic
end SecondQuantization
