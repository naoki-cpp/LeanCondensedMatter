import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# One-dimensional continuum multiplication bridge for fermionic charge density

This module connects the abstract algebraic smeared charge-density interface to the continuum
wavefunction layer without claiming an `L²` operator theorem.

The one-particle space here is the raw complex function space `ℝ → ℂ`. A complex smearing function
`f` acts by pointwise multiplication,

`M_f ψ = f ψ`,

which is an everywhere-defined algebraic linear endomorphism of that function space. Feeding this
family into `chargeDensity` gives the corresponding finite-particle operator `q dΓ(M_f)`.

On the one-particle sector the construction acts exactly as pointwise charge-weighted
multiplication. For real test functions this is the same `q f ψ` factor underlying the continuum
smeared charge density. Identifying the resulting scalar expectation with
`∫ f(x) q |ψ(x)|² dx` is deliberately deferred: that step requires an `L²` inner product and the
appropriate multiplication-operator/domain hypotheses.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

noncomputable section

/-- One-dimensional continuum wavefunctions before any `L²` completion or integrability condition. -/
abbrev ContinuumWavefunction1D := ℝ → ℂ

/-- Pointwise multiplication by one complex-valued continuum test function. -/
noncomputable def continuumMultiplicationOperator1D
    (f : ℝ → ℂ) : ContinuumWavefunction1D →ₗ[ℂ] ContinuumWavefunction1D where
  toFun := fun ψ x => f x * ψ x
  map_add' := by
    intro ψ φ
    funext x
    exact mul_add (f x) (ψ x) (φ x)
  map_smul' := by
    intro c ψ
    funext x
    change f x * (c * ψ x) = c * (f x * ψ x)
    ring

@[simp]
theorem continuumMultiplicationOperator1D_apply
    (f ψ : ContinuumWavefunction1D) (x : ℝ) :
    continuumMultiplicationOperator1D f ψ x = f x * ψ x :=
  rfl

/-- The pointwise multiplication operator depends complex-linearly on the smearing function. -/
noncomputable def continuumMultiplication1D :
    (ℝ → ℂ) →ₗ[ℂ]
      (ContinuumWavefunction1D →ₗ[ℂ] ContinuumWavefunction1D) where
  toFun := continuumMultiplicationOperator1D
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro ψ
    funext x
    simp [continuumMultiplicationOperator1D, add_mul]
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro ψ
    funext x
    change c * f x * ψ x = c * (f x * ψ x)
    exact mul_assoc c (f x) (ψ x)

@[simp]
theorem continuumMultiplication1D_apply
    (f ψ : ContinuumWavefunction1D) (x : ℝ) :
    continuumMultiplication1D f ψ x = f x * ψ x :=
  rfl

/-- The abstract fermionic smeared charge density specialized to continuum multiplication
operators on raw one-dimensional wavefunctions. -/
noncomputable def continuumChargeDensity1D (q : ℂ) :
    (ℝ → ℂ) →ₗ[ℂ]
      (AlgebraicFock ContinuumWavefunction1D →ₗ[ℂ]
        AlgebraicFock ContinuumWavefunction1D) :=
  chargeDensity ContinuumWavefunction1D q continuumMultiplication1D

@[simp]
theorem continuumChargeDensity1D_apply (q : ℂ) (f : ℝ → ℂ) :
    continuumChargeDensity1D q f =
      q • AlgebraicFock.dGamma ContinuumWavefunction1D (continuumMultiplication1D f) :=
  rfl

/-- On the one-particle sector, the continuum charge-density operator is exactly pointwise
charge-weighted multiplication. -/
theorem continuumChargeDensity1D_oneParticle
    (q : ℂ) (f ψ : ContinuumWavefunction1D) :
    continuumChargeDensity1D q f
        (AlgebraicFock.oneParticle ContinuumWavefunction1D ψ) =
      AlgebraicFock.oneParticle ContinuumWavefunction1D (fun x => q * f x * ψ x) := by
  rw [continuumChargeDensity1D_apply]
  simp only [LinearMap.smul_apply, AlgebraicFock.dGamma_oneParticle]
  rw [← map_smul]
  congr 1
  funext x
  simp [continuumMultiplication1D, continuumMultiplicationOperator1D, mul_assoc]

/-- Embed a real continuum test function into the complex smearing space used by the algebraic
many-body charge-density interface. -/
def complexTestOfReal1D (test : ℝ → ℝ) : ℝ → ℂ :=
  fun x => test x

@[simp]
theorem complexTestOfReal1D_apply (test : ℝ → ℝ) (x : ℝ) :
    complexTestOfReal1D test x = (test x : ℂ) :=
  rfl

/-- For real charge and real test function, the algebraic many-body charge density restricts on the
one-particle sector to the same pointwise factor `q * test * ψ` used by the continuum charge
smearing convention. -/
theorem continuumChargeDensity1D_oneParticle_real
    (q : ℝ) (test : ℝ → ℝ) (ψ : ContinuumWavefunction1D) :
    continuumChargeDensity1D (q : ℂ) (complexTestOfReal1D test)
        (AlgebraicFock.oneParticle ContinuumWavefunction1D ψ) =
      AlgebraicFock.oneParticle ContinuumWavefunction1D
        (fun x => ((q * test x : ℝ) : ℂ) * ψ x) := by
  simpa [complexTestOfReal1D] using
    (continuumChargeDensity1D_oneParticle (q : ℂ) (complexTestOfReal1D test) ψ)

end
end Field
end Fermionic
end SecondQuantization
