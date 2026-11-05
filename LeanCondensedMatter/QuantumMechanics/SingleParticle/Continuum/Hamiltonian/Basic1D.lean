import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.L2.Multiplication1D
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.LinearAlgebra.LinearPMap

set_option linter.style.header false

/-!
# Domain-carrying one-dimensional Schrödinger Hamiltonian

Square-integrable wavefunctions are embedded as tempered distributions, and the kinetic domain is
the Bessel-potential Sobolev space `H²`: an `L²` wavefunction belongs to the domain exactly when
its associated tempered distribution has Sobolev regularity two.

On this domain, the distributional Laplacian has Sobolev order zero and therefore a unique `L²`
representative. Combining the kinetic term with bounded multiplication operators gives the partial
linear Schrödinger operator

`H ψ = -κ Δ ψ + V ψ`

for an essentially bounded potential `V`. The real-potential specialization uses the real
`L∞` multiplication embedding.

This module defines the operator and its domain; closedness, symmetry, self-adjointness, generated
unitary evolution, and pointwise twice-differentiable representatives require additional hypotheses
and are treated separately.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory SchwartzMap Laplacian LineDeriv

/-- The canonical embedding of `L²(ℝ, ℂ)` wavefunctions into complex-valued tempered
distributions. -/
noncomputable def l2ToTemperedDistribution1D :
    ContinuumL2Wavefunction1D →L[ℂ] 𝓢'(ℝ, ℂ) :=
  MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2

/-- The canonical `L²(ℝ, ℂ) → 𝓢'(ℝ, ℂ)` embedding is injective. -/
theorem l2ToTemperedDistribution1D_injective :
    Function.Injective l2ToTemperedDistribution1D := by
  change Function.Injective
    (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2)
  apply LinearMap.ker_eq_bot.mp
  exact MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot

/-- The natural `H²(ℝ)` domain for the one-dimensional distributional Laplacian, expressed as a
submodule of the physical `L²` wavefunction space. -/
noncomputable def continuumH2Domain1D :
    Submodule ℂ ContinuumL2Wavefunction1D where
  carrier := {ψ |
    TemperedDistribution.MemSobolev (2 : ℝ) 2 (l2ToTemperedDistribution1D ψ)}
  zero_mem' := by
    change TemperedDistribution.MemSobolev (2 : ℝ) 2 (l2ToTemperedDistribution1D 0)
    rw [map_zero]
    exact TemperedDistribution.memSobolev_fun_zero ℝ ℂ 2 2
  add_mem' := by
    intro ψ φ hψ hφ
    change TemperedDistribution.MemSobolev (2 : ℝ) 2
      (l2ToTemperedDistribution1D (ψ + φ))
    rw [map_add]
    exact TemperedDistribution.MemSobolev.add hψ hφ
  smul_mem' := by
    intro c ψ hψ
    change TemperedDistribution.MemSobolev (2 : ℝ) 2
      (l2ToTemperedDistribution1D (c • ψ))
    rw [map_smul]
    exact TemperedDistribution.MemSobolev.smul c hψ

@[simp]
theorem mem_continuumH2Domain1D_iff (ψ : ContinuumL2Wavefunction1D) :
    ψ ∈ continuumH2Domain1D ↔
      TemperedDistribution.MemSobolev (2 : ℝ) 2 (l2ToTemperedDistribution1D ψ) :=
  Iff.rfl

private theorem continuumH2Laplacian_memSobolev_zero (ψ : continuumH2Domain1D) :
    TemperedDistribution.MemSobolev 0 2
      (Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D))) := by
  simpa using TemperedDistribution.MemSobolev.laplacian
    ((mem_continuumH2Domain1D_iff (ψ : ContinuumL2Wavefunction1D)).mp ψ.property)

/-- The distributional Laplacian on the explicit `H²` domain, returned as an `L²`
wavefunction. Its values lie in the range of the injective `L²` embedding. -/
noncomputable def continuumH2Laplacian1D :
    continuumH2Domain1D →ₗ[ℂ] ContinuumL2Wavefunction1D :=
  (LinearEquiv.ofInjective l2ToTemperedDistribution1D.toLinearMap
    l2ToTemperedDistribution1D_injective).symm.toLinearMap.comp
      (((LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).toLinearMap.comp
        (l2ToTemperedDistribution1D.toLinearMap.comp continuumH2Domain1D.subtype)).codRestrict
          l2ToTemperedDistribution1D.toLinearMap.range (by
            intro ψ
            obtain ⟨φ, hφ⟩ := TemperedDistribution.memSobolev_zero_iff.mp
              (continuumH2Laplacian_memSobolev_zero ψ)
            apply LinearMap.mem_range.mpr
            refine ⟨φ, ?_⟩
            change l2ToTemperedDistribution1D φ =
              (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ))
                (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D))
            rw [TemperedDistribution.laplacianCLM_apply]
            simpa [l2ToTemperedDistribution1D] using hφ.symm)

/-- The `L²` value produced by `continuumH2Laplacian1D` represents exactly the distributional
Laplacian of the original `L²` wavefunction. -/
theorem l2ToTemperedDistribution1D_continuumH2Laplacian1D
    (ψ : continuumH2Domain1D) :
    l2ToTemperedDistribution1D (continuumH2Laplacian1D ψ) =
      Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) := by
  change l2ToTemperedDistribution1D
    ((LinearEquiv.ofInjective l2ToTemperedDistribution1D.toLinearMap
      l2ToTemperedDistribution1D_injective).symm
      ((((LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).toLinearMap.comp
        (l2ToTemperedDistribution1D.toLinearMap.comp continuumH2Domain1D.subtype)).codRestrict
          l2ToTemperedDistribution1D.toLinearMap.range _) ψ)) = _
  rw [LinearEquiv.ofInjective_symm_apply]
  exact TemperedDistribution.laplacianCLM_apply _

/-- Schrödinger action on the explicit `H²` domain for kinetic coefficient `κ` and an essentially
bounded complex potential. -/
noncomputable def continuumSchrodingerHamiltonianOnH2Domain1D
    (κ : ℝ) (potential : ContinuumLInfMultiplier1D) :
    continuumH2Domain1D →ₗ[ℂ] ContinuumL2Wavefunction1D :=
  -(κ : ℂ) • continuumH2Laplacian1D +
    (l2MultiplicationOperator1D potential).toLinearMap.comp continuumH2Domain1D.subtype

/-- The one-dimensional Schrödinger Hamiltonian as a partial linear map on `L²`, with domain
`H²(ℝ)` and bounded multiplication potential. -/
noncomputable def continuumSchrodingerHamiltonian1D
    (κ : ℝ) (potential : ContinuumLInfMultiplier1D) :
    ContinuumL2Wavefunction1D →ₗ.[ℂ] ContinuumL2Wavefunction1D where
  domain := continuumH2Domain1D
  toFun := continuumSchrodingerHamiltonianOnH2Domain1D κ potential

@[simp]
theorem continuumSchrodingerHamiltonian1D_domain
    (κ : ℝ) (potential : ContinuumLInfMultiplier1D) :
    (continuumSchrodingerHamiltonian1D κ potential).domain = continuumH2Domain1D :=
  rfl

@[simp]
theorem continuumSchrodingerHamiltonian1D_apply
    (κ : ℝ) (potential : ContinuumLInfMultiplier1D)
    (ψ : continuumH2Domain1D) :
    continuumSchrodingerHamiltonian1D κ potential ψ =
      -(κ : ℂ) • continuumH2Laplacian1D ψ +
        l2MultiplicationOperator1D potential (ψ : ContinuumL2Wavefunction1D) :=
  rfl

/-- Real scalar-potential specialization of the domain-carrying Schrödinger Hamiltonian. The
`MemLp ... ∞` hypothesis is the explicit boundedness assumption on the potential. -/
noncomputable def continuumRealPotentialSchrodingerHamiltonian1D
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)) :
    ContinuumL2Wavefunction1D →ₗ.[ℂ] ContinuumL2Wavefunction1D :=
  continuumSchrodingerHamiltonian1D κ (realLInfMultiplier1D potential hpotential)

@[simp]
theorem continuumRealPotentialSchrodingerHamiltonian1D_domain
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)) :
    (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential).domain =
      continuumH2Domain1D :=
  rfl

end
end Continuum
end SingleParticle
end QuantumMechanics
