import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate

set_option linter.style.header false

/-!
# Factorization of the finite fermionic grand-canonical partition function

For a finite mode type the common grand-canonical partition function is

`Ξ(β, μ) = ∑ₙ exp(-β(E(n)-μ N(n))) = ∏ᵢ (1 + exp(-β(εᵢ-μ)))`.

The proof uses the shared grand-canonical energy and generic finite Boltzmann coordinates.
There is no parallel finite Gibbs state or implicit zero-chemical-potential partition API.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] [Fintype Mode] in
private theorem boltzmannWeight_fermionEnergy_eq_prod
    (ξ : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    Common.boltzmannWeight (fermionEnergy ξ) β n =
      ∏ i ∈ n, Complex.exp (-(β : ℂ) * (ξ i : ℂ)) := by
  rw [Common.boltzmannWeight, fermionEnergy_eq_sum, Finset.mul_sum]
  push_cast
  rw [Complex.exp_sum]

omit [LinearOrder Mode] [Fintype Mode] in
private theorem sum_boltzmannWeight_powerset_eq_prod
    (ξ : Mode → ℝ) (β : ℝ) (s : Finset Mode) :
    ∑ t ∈ s.powerset, Common.boltzmannWeight (fermionEnergy ξ) β t =
      ∏ j ∈ s, (1 + Complex.exp (-(β : ℂ) * (ξ j : ℂ))) := by
  classical
  simp_rw [boltzmannWeight_fermionEnergy_eq_prod]
  have h := Finset.prod_add (fun j => Complex.exp (-(β : ℂ) * (ξ j : ℂ)))
    (fun _ => (1 : ℂ)) s
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun j _ => add_comm _ _

omit [LinearOrder Mode] in
/-- The grand-canonical partition sum over finite fermionic occupation Fock space
factorizes into one-mode terms at explicit chemical potential `μ`. The normalization
uses the shared real partition function; this identity is its complex coordinate form. -/
theorem coe_grandCanonicalPartitionFunction_eq_prod
    (ε : Mode → ℝ) (β μ : ℝ) :
    (Common.grandCanonicalPartitionFunction (Config := Occupation Mode) ε β μ : ℂ) =
      ∏ i, (1 + Complex.exp (-(β : ℂ) * ((ε i - μ : ℝ) : ℂ))) := by
  rw [Common.grandCanonicalPartitionFunction_eq_shifted]
  rw [Common.coe_eigenbasisPartitionFunction_eq_sum_boltzmannWeight]
  change (∑ n : Occupation Mode,
      Common.boltzmannWeight (fermionEnergy (fun i => ε i - μ)) β n) = _
  rw [← Finset.powerset_univ]
  exact sum_boltzmannWeight_powerset_eq_prod (fun i => ε i - μ) β Finset.univ

end Fermionic
end SecondQuantization
