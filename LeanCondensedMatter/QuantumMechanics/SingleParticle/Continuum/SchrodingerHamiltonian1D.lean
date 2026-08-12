import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.L2Multiplication1D
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Domain-carrying one-dimensional Schrödinger Hamiltonian

This module introduces the first genuinely unbounded-operator boundary of the continuum
Schrödinger development. Square-integrable wavefunctions are embedded as tempered distributions,
and the kinetic domain is the Bessel-potential Sobolev space `H²`: an `L²` wavefunction belongs to
the domain exactly when its associated tempered distribution has Sobolev regularity two.

On that explicit domain, Mathlib's distributional Laplacian has Sobolev order zero and therefore
has a unique `L²` representative. Combining this kinetic term with the bounded multiplication
operators from the preceding continuum layer gives a partial linear map representing

`H ψ = -κ Δ ψ + V ψ`

for an essentially bounded potential `V`. The real-potential specialization reuses the generic
real `L∞` embedding owned by the bounded multiplication layer.

No closedness, symmetry, self-adjointness, generated unitary evolution, or identification with a
pointwise twice-differentiable representative is claimed here. Those are later analytic layers.
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

private theorem l2ToTemperedDistribution1D_injective :
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
  have hψ : TemperedDistribution.MemSobolev (2 : ℝ) 2
      (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) :=
    (mem_continuumH2Domain1D_iff (ψ : ContinuumL2Wavefunction1D)).mp ψ.property
  simpa using TemperedDistribution.MemSobolev.laplacian hψ

/-- The unique `L²` representative of the distributional Laplacian of an `H²` wavefunction. -/
private noncomputable def continuumH2LaplacianValue1D
    (ψ : continuumH2Domain1D) : ContinuumL2Wavefunction1D :=
  Classical.choose
    (TemperedDistribution.memSobolev_zero_iff.mp
      (continuumH2Laplacian_memSobolev_zero ψ))

private theorem l2ToTemperedDistribution1D_continuumH2LaplacianValue1D
    (ψ : continuumH2Domain1D) :
    l2ToTemperedDistribution1D (continuumH2LaplacianValue1D ψ) =
      Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) := by
  have hrepr := Classical.choose_spec
    (TemperedDistribution.memSobolev_zero_iff.mp
      (continuumH2Laplacian_memSobolev_zero ψ))
  simpa [l2ToTemperedDistribution1D, continuumH2LaplacianValue1D] using hrepr.symm

/-- The distributional Laplacian on the explicit `H²` domain, returned as an `L²` wavefunction. -/
noncomputable def continuumH2Laplacian1D :
    continuumH2Domain1D →ₗ[ℂ] ContinuumL2Wavefunction1D where
  toFun := continuumH2LaplacianValue1D
  map_add' ψ φ := by
    apply l2ToTemperedDistribution1D_injective
    rw [map_add]
    rw [l2ToTemperedDistribution1D_continuumH2LaplacianValue1D,
      l2ToTemperedDistribution1D_continuumH2LaplacianValue1D,
      l2ToTemperedDistribution1D_continuumH2LaplacianValue1D]
    simp only [Submodule.coe_add, map_add]
    simpa only [TemperedDistribution.laplacianCLM_apply] using
      (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).map_add
        (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D))
        (l2ToTemperedDistribution1D (φ : ContinuumL2Wavefunction1D))
  map_smul' c ψ := by
    apply l2ToTemperedDistribution1D_injective
    rw [map_smul]
    rw [l2ToTemperedDistribution1D_continuumH2LaplacianValue1D,
      l2ToTemperedDistribution1D_continuumH2LaplacianValue1D]
    simp only [Submodule.coe_smul, map_smul]
    simpa only [TemperedDistribution.laplacianCLM_apply, RingHom.id_apply] using
      (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).map_smul c
        (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D))

@[simp]
theorem continuumH2Laplacian1D_apply (ψ : continuumH2Domain1D) :
    continuumH2Laplacian1D ψ = continuumH2LaplacianValue1D ψ :=
  rfl

/-- The `L²` value produced by `continuumH2Laplacian1D` represents exactly the distributional
Laplacian of the original `L²` wavefunction. -/
theorem l2ToTemperedDistribution1D_continuumH2Laplacian1D
    (ψ : continuumH2Domain1D) :
    l2ToTemperedDistribution1D (continuumH2Laplacian1D ψ) =
      Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) :=
  l2ToTemperedDistribution1D_continuumH2LaplacianValue1D ψ

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
