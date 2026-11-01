import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.QuantumTheory.Gibbs.Boltzmann
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option linter.style.header false

/-!
# Infinite-mode fermionic grand-canonical Gibbs summability and partition product

For an arbitrary mode type and explicit chemical potential `μ`, write the effective one-particle
energy as `ξ i = ε i - μ`. One-particle Gibbs summability
`EigenbasisGibbsSummable ξ β` implies summability of the grand-canonical occupation
weights for `K(n) = E(n) - μ N(n)`, and the grand partition function factorizes as

```text
Ξ(β, μ) = ∏' i, (1 + exp (-β * (ε i - μ))).
```

The product ranges over **all** modes, not a finite subset. The proof uses the generic
occupation energy shift and a summable product over finite occupied subsets. There is no
`[Fintype Mode]` or countability typeclass: the analytic summability condition is
explicit and nontrivial in an infinite-mode system. The finite-coordinate results are
separate downstream consequences, not the foundation of this construction.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- The free occupation Boltzmann weight factors into the one-particle pure-point Boltzmann weights
of the occupied modes. -/
theorem eigenbasisBoltzmannWeight_fermionEnergy_eq_prod
    (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    eigenbasisBoltzmannWeight (fermionEnergy ε) β n =
      ∏ i ∈ n, eigenbasisBoltzmannWeight ε β i := by
  calc
    eigenbasisBoltzmannWeight (fermionEnergy ε) β n =
        Real.exp (-β * ∑ i ∈ n, ε i) := by
      simp only [eigenbasisBoltzmannWeight, fermionEnergy_eq_sum]
    _ = Real.exp (∑ i ∈ n, (-β * ε i)) := by
      congr 1
      rw [Finset.mul_sum]
    _ = ∏ i ∈ n, Real.exp (-β * ε i) := by
      exact Real.exp_sum n (fun i => -β * ε i)
    _ = ∏ i ∈ n, eigenbasisBoltzmannWeight ε β i := by
      rfl

/-- Under one-particle pure-point Gibbs summability, the free fermion partition function is the
infinite product `∏ᵢ (1 + exp (-β εᵢ))`. -/
private theorem eigenbasisPartitionFunction_fermionEnergy_eq_tprod_one_add
    (ε : Mode → ℝ) (β : ℝ) (hmode : EigenbasisGibbsSummable ε β) :
    eigenbasisPartitionFunction (fermionEnergy ε) β =
      ∏' i : Mode, (1 + eigenbasisBoltzmannWeight ε β i) := by
  have hprod :
      Summable fun n : Finset Mode =>
        ∏ i ∈ n, eigenbasisBoltzmannWeight ε β i :=
    summable_finsetProd_of_summable_nonneg
      (eigenbasisBoltzmannWeight_nonneg ε β)
      (eigenbasisBoltzmannWeight_summable ε β hmode)
  rw [eigenbasisPartitionFunction]
  calc
    (∑' n : Occupation Mode, eigenbasisBoltzmannWeight (fermionEnergy ε) β n) =
        ∑' n : Finset Mode, ∏ i ∈ n, eigenbasisBoltzmannWeight ε β i := by
      apply tsum_congr
      intro n
      exact eigenbasisBoltzmannWeight_fermionEnergy_eq_prod ε β n
    _ = ∏' i : Mode, (1 + eigenbasisBoltzmannWeight ε β i) :=
      (tprod_one_add hprod).symm


/-- For any (possibly infinite) mode type, summability of the one-particle weights
`exp (-β * (ε i - μ))` ensures existence of the full-Fock grand-canonical
Gibbs density operator through the common constructor. -/
theorem grandCanonicalGibbsSummable_of_mode
    (ε : Mode → ℝ) (β μ : ℝ)
    (hmode : EigenbasisGibbsSummable (fun i => ε i - μ) β) :
    EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β := by
  apply (Common.grandCanonicalGibbsSummable_iff_shifted
    (Config := Occupation Mode) ε β μ).2
  change EigenbasisGibbsSummable (fermionEnergy (fun i => ε i - μ)) β
  unfold EigenbasisGibbsSummable
  have hprod :
      Summable fun n : Finset Mode =>
        ∏ i ∈ n, eigenbasisBoltzmannWeight (fun i => ε i - μ) β i :=
    summable_finsetProd_of_summable_nonneg
      (eigenbasisBoltzmannWeight_nonneg (fun i => ε i - μ) β)
      (eigenbasisBoltzmannWeight_summable (fun i => ε i - μ) β hmode)
  have hweights :
      eigenbasisBoltzmannWeight (fermionEnergy (fun i => ε i - μ)) β =
        fun n : Occupation Mode =>
          ∏ i ∈ n, eigenbasisBoltzmannWeight (fun i => ε i - μ) β i := by
    funext n
    exact eigenbasisBoltzmannWeight_fermionEnergy_eq_prod (fun i => ε i - μ) β n
  rw [hweights]
  exact hprod.norm

/-- The full-Fock grand partition function of free fermions on arbitrary modes
factorizes into the infinite product of one-mode contributions at explicit `μ`.
The one-particle summability condition is required for the genuine Gibbs state. -/
theorem grandCanonicalPartitionFunction_eq_tprod_one_add
    (ε : Mode → ℝ) (β μ : ℝ)
    (hmode : EigenbasisGibbsSummable (fun i => ε i - μ) β) :
    Common.grandCanonicalPartitionFunction (Config := Occupation Mode) ε β μ =
      ∏' i : Mode,
        (1 + eigenbasisBoltzmannWeight (fun j => ε j - μ) β i) := by
  rw [Common.grandCanonicalPartitionFunction_eq_shifted]
  exact eigenbasisPartitionFunction_fermionEnergy_eq_tprod_one_add
    (fun i => ε i - μ) β hmode

end
end Fermionic
end SecondQuantization
