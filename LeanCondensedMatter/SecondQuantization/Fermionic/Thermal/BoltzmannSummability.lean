import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
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
  simp only [eigenbasisBoltzmannWeight, fermionEnergy_eq_sum, Finset.mul_sum, Real.exp_sum]

private theorem summable_occupationWeightProduct
    (ε : Mode → ℝ) (β : ℝ) (hmode : EigenbasisGibbsSummable ε β) :
    Summable (fun n : Finset Mode => ∏ i ∈ n, eigenbasisBoltzmannWeight ε β i) :=
  summable_finsetProd_of_summable_nonneg
    (eigenbasisBoltzmannWeight_nonneg ε β)
    (eigenbasisBoltzmannWeight_summable ε β hmode)

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
  simp only [EigenbasisGibbsSummable, eigenbasisBoltzmannWeight_fermionEnergy_eq_prod]
  exact (summable_occupationWeightProduct (fun i => ε i - μ) β hmode).norm


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
  change eigenbasisPartitionFunction (fermionEnergy (fun i => ε i - μ)) β = _
  simp only [eigenbasisPartitionFunction, eigenbasisBoltzmannWeight_fermionEnergy_eq_prod]
  exact (tprod_one_add
    (summable_occupationWeightProduct (fun i => ε i - μ) β hmode)).symm

end
end Fermionic
end SecondQuantization
