import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.ConductivityNormalization

set_option linter.style.header false

/-!
# Finite Kubo–Greenwood conductivity input

This module gives a public name to the exact finite spectral conductivity derived upstream from
bounded time-dependent perturbation theory, the causal Kubo theorem, the continuity-derived
Peierls current, the explicit contact variation, the infinite-observation-time limit, and the
finite pure-point Lehmann theorem.

For the source convention `A(t) ∝ exp (ηt) exp (-iωt)`, the result is

```text
σ(ω,η)
  = [Σₘₙ (i/ℏ)(pₘ-pₙ) JₘₙJₙₘ
       / (η - i(ω + (Eₘ-Eₙ)/ℏ)) + ⟨C⟩]
      / [V(-η+iω)].
```

Here `J` is the continuity-derived directional current and `C` is the geometric Peierls contact
operator. Diagonal transitions vanish. Equal-energy off-diagonal transitions remain at finite
`η` unless their probability difference or matrix elements vanish.

This named expression is the input boundary for the later finite-dimensional Kubo–Bastin trace
rewrite. It is not introduced as an independent conductivity definition: the main equality below
identifies it with the conductivity already derived from the Kubo response chain. No ordinary
trace, trace-class extension, disorder average, zero-broadening limit, DC limit, or thermodynamic
limit occurs here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- One finite Kubo–Greenwood current-current transition term. -/
noncomputable def finiteKuboGreenwoodDirectionalCurrentTerm
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (mn : ι × ι) : ℂ :=
  lehmannTerm system.hbar ω η
    (data.energy mn.1 - data.energy mn.2)
    (purePointTransitionWeight system data
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K) mn)

/-- Diagonal Kubo–Greenwood current-current transitions vanish exactly. -/
@[simp]
theorem finiteKuboGreenwoodDirectionalCurrentTerm_diag
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (i : ι) :
    finiteKuboGreenwoodDirectionalCurrentTerm
      system data geometry direction K q ω η (i, i) = 0 := by
  simp [finiteKuboGreenwoodDirectionalCurrentTerm, lehmannTerm]

/-- Equal-energy off-diagonal transitions keep the finite-rate denominator `η - iω`. -/
theorem finiteKuboGreenwoodDirectionalCurrentTerm_of_equal_energy
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) {m n : ι}
    (henergy : data.energy m = data.energy n) :
    finiteKuboGreenwoodDirectionalCurrentTerm
        system data geometry direction K q ω η (m, n) =
      purePointTransitionWeight system data
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K) (m, n) *
        ((η : ℂ) - Complex.I * (ω : ℂ))⁻¹ := by
  unfold finiteKuboGreenwoodDirectionalCurrentTerm
  exact purePointDirectionalCurrentLehmannTerm_of_equal_energy
    system data geometry direction K q ω η henergy

/-- The exact finite Kubo–Greenwood conductivity supplied to the resolvent rewrite.

The current-current sum, Peierls contact expectation, positive finite volume, and electric-field
conversion factor are all explicit in the definition. -/
noncomputable def finiteKuboGreenwoodDirectionalConductivity
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) : ℂ :=
  ((∑ mn : ι × ι,
      finiteKuboGreenwoodDirectionalCurrentTerm
        system data geometry direction K q ω η mn) +
      purePointNormalizedExpectation system data
        (boundedDirectionalContact geometry direction
          (system.hbar : ℂ) (q : ℂ) K)) *
    finiteVolumeConductivityNormalization volume ω η

/-- The named finite Kubo–Greenwood expression is exactly the conductivity derived from the
upstream Kubo response chain, at fixed positive switching rate. -/
theorem infiniteTimeAdiabaticDirectionalConductivity_eq_finiteKuboGreenwood
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    infiniteTimeAdiabaticDirectionalConductivity volume
        system (purePointNormalizedExpectation system data)
          geometry direction K q ω η =
      finiteKuboGreenwoodDirectionalConductivity
        volume system data geometry direction K q ω η := by
  rw [infiniteTimeAdiabaticDirectionalConductivity_purePoint_eq_finite_sum
    volume system data geometry direction K q ω η hη]
  rfl

/-- The contact term remains a separate explicit contribution after conductivity normalization. -/
theorem finiteKuboGreenwoodDirectionalConductivity_eq_current_sum_add_contact
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) :
    finiteKuboGreenwoodDirectionalConductivity
        volume system data geometry direction K q ω η =
      (∑ mn : ι × ι,
          finiteKuboGreenwoodDirectionalCurrentTerm
            system data geometry direction K q ω η mn) *
          finiteVolumeConductivityNormalization volume ω η +
        purePointNormalizedExpectation system data
            (boundedDirectionalContact geometry direction
              (system.hbar : ℂ) (q : ℂ) K) *
          finiteVolumeConductivityNormalization volume ω η := by
  unfold finiteKuboGreenwoodDirectionalConductivity
  ring

end
end Transport
end Fermionic
end SecondQuantization
