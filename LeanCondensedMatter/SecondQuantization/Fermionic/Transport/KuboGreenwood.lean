import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.ConductivityNormalization

set_option linter.style.header false

/-!
# Finite Kubo–Greenwood conductivity input

This module gives a public name to the exact finite spectral conductivity derived upstream from
bounded time-dependent perturbation theory, the causal Kubo theorem, the continuity-derived
Peierls current, the explicit contact variation, the infinite-observation-time limit, and the
finite pure-point Lehmann theorem.

For measured-current direction `i` and source-field direction `j`, the component response has the
form

```text
σ_ij(ω,η)
  = [Σₘₙ (i/ℏ)(pₘ-pₙ) (J_i)ₘₙ(J_j)ₙₘ
       / (η - i(ω + (Eₘ-Eₙ)/ℏ)) + ⟨C_ij⟩]
      / [V(-η+iω)].
```

The historical directional conductivity is the diagonal specialization `i = j`. Diagonal spectral
transitions vanish. Equal-energy off-diagonal transitions remain at finite `η` unless their
probability difference or matrix elements vanish.

This named expression is the input boundary for the later finite-dimensional Kubo–Bastin trace
rewrite. No ordinary trace, trace-class extension, disorder average, zero-broadening limit, DC
limit, or thermodynamic limit occurs here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- One finite Kubo–Greenwood transition for the conductivity component with current measured along
`measuredDirection` and electric field sourced along `sourceDirection`. -/
noncomputable def finiteKuboGreenwoodCurrentComponentTerm
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (mn : ι × ι) : ℂ :=
  lehmannTerm system.hbar ω η
    (data.energy mn.1 - data.energy mn.2)
    (purePointTransitionWeight system data
      (boundedDirectionalCurrent geometry measuredDirection
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry sourceDirection
        (system.hbar : ℂ) (q : ℂ) K) mn)

/-- Diagonal spectral transitions vanish for every conductivity component. -/
@[simp]
theorem finiteKuboGreenwoodCurrentComponentTerm_diag
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (i : ι) :
    finiteKuboGreenwoodCurrentComponentTerm
      system data geometry measuredDirection sourceDirection K q ω η (i, i) = 0 := by
  simp [finiteKuboGreenwoodCurrentComponentTerm, lehmannTerm]

/-- Equal-energy off-diagonal transitions keep the finite-rate denominator `η - iω` for arbitrary
measured/source directions. -/
theorem finiteKuboGreenwoodCurrentComponentTerm_of_equal_energy
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) {m n : ι}
    (henergy : data.energy m = data.energy n) :
    finiteKuboGreenwoodCurrentComponentTerm
        system data geometry measuredDirection sourceDirection K q ω η (m, n) =
      purePointTransitionWeight system data
          (boundedDirectionalCurrent geometry measuredDirection
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry sourceDirection
            (system.hbar : ℂ) (q : ℂ) K) (m, n) *
        ((η : ℂ) - Complex.I * (ω : ℂ))⁻¹ := by
  have hgap : data.energy m - data.energy n = 0 := sub_eq_zero.mpr henergy
  unfold finiteKuboGreenwoodCurrentComponentTerm
  rw [hgap]
  simp [lehmannTerm, lehmannDenominator]

/-- Finite Kubo–Greenwood conductivity component `σ_ij`, with independent measured-current and
source-field directions and the corresponding mixed Peierls contact response. -/
noncomputable def finiteKuboGreenwoodConductivityComponent
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) : ℂ :=
  ((∑ mn : ι × ι,
      finiteKuboGreenwoodCurrentComponentTerm
        system data geometry measuredDirection sourceDirection K q ω η mn) +
      purePointNormalizedExpectation system data
        (boundedMixedDirectionalContact geometry measuredDirection sourceDirection
          (system.hbar : ℂ) (q : ℂ) K)) *
    finiteVolumeConductivityNormalization volume ω η

/-- One finite Kubo–Greenwood current-current transition term in the diagonal directional
specialization. -/
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

/-- The component transition reduces definitionally to the directional transition when the two
directions coincide. -/
@[simp]
theorem finiteKuboGreenwoodCurrentComponentTerm_self
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (mn : ι × ι) :
    finiteKuboGreenwoodCurrentComponentTerm
        system data geometry direction direction K q ω η mn =
      finiteKuboGreenwoodDirectionalCurrentTerm
        system data geometry direction K q ω η mn := by
  rfl

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

/-- The exact finite diagonal Kubo–Greenwood conductivity supplied to the resolvent rewrite. -/
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

/-- The diagonal component API reproduces the historical directional conductivity exactly. -/
@[simp]
theorem finiteKuboGreenwoodConductivityComponent_self
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) :
    finiteKuboGreenwoodConductivityComponent
        volume system data geometry direction direction K q ω η =
      finiteKuboGreenwoodDirectionalConductivity
        volume system data geometry direction K q ω η := by
  unfold finiteKuboGreenwoodConductivityComponent
    finiteKuboGreenwoodDirectionalConductivity
  rw [boundedMixedDirectionalContact_self]
  rfl

/-- The named finite directional Kubo–Greenwood expression is exactly the conductivity derived from
the upstream one-direction Kubo response chain, at fixed positive switching rate. -/
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

/-- The component contact term remains a separate explicit contribution after conductivity
normalization. -/
theorem finiteKuboGreenwoodConductivityComponent_eq_current_sum_add_contact
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) :
    finiteKuboGreenwoodConductivityComponent
        volume system data geometry measuredDirection sourceDirection K q ω η =
      (∑ mn : ι × ι,
          finiteKuboGreenwoodCurrentComponentTerm
            system data geometry measuredDirection sourceDirection K q ω η mn) *
          finiteVolumeConductivityNormalization volume ω η +
        purePointNormalizedExpectation system data
            (boundedMixedDirectionalContact geometry measuredDirection sourceDirection
              (system.hbar : ℂ) (q : ℂ) K) *
          finiteVolumeConductivityNormalization volume ω η := by
  unfold finiteKuboGreenwoodConductivityComponent
  ring

/-- The diagonal contact term remains a separate explicit contribution after conductivity
normalization. -/
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
