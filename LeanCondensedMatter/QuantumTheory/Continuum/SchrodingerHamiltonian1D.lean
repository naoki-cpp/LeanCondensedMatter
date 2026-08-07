import LeanCondensedMatter.QuantumTheory.Continuum.L2SmearedProbabilityDensity1D
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

On that explicit domain, Mathlib's distributional Laplacian lands back in `L²`. Combining this
kinetic term with the bounded multiplication operators from the preceding continuum layer gives a
partial linear map representing

`H ψ = -κ Δ ψ + V ψ`

for an essentially bounded potential `V`. The real-potential specialization reuses the `L∞`
embedding introduced for smeared probability-density observables.

No closedness, symmetry, self-adjointness, generated unitary evolution, or identification with a
pointwise twice-differentiable representative is claimed here. Those are later analytic layers.
-/

namespace QuantumTheory
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory SchwartzMap Laplacian LineDeriv

/-- The canonical embedding of `L²(ℝ, ℂ)` wavefunctions into complex-valued tempered
distributions. -/
noncomputable def l2ToTemperedDistribution1D :
    ContinuumL2Wavefunction1D →L[ℂ] 𝓢'(ℝ, ℂ) :=
  MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2

/-- The natural `H²(ℝ)` domain for the one-dimensional distributional Laplacian, expressed as a
submodule of the physical `L²` wavefunction space. -/
noncomputable def continuumH2Domain1D :
    Submodule ℂ ContinuumL2Wavefunction1D where
  carrier := {ψ | MemSobolev (2 : ℝ) 2 (l2ToTemperedDistribution1D ψ)}
  zero_mem' := by
    change MemSobolev (2 : ℝ) 2 (l2ToTemperedDistribution1D 0)
    rw [map_zero]
    exact memSobolev_zero ℝ ℂ 2 2
  add_mem' := by
    intro ψ φ hψ hφ
    change MemSobolev (2 : ℝ) 2 (l2ToTemperedDistribution1D (ψ + φ))
    rw [map_add]
    exact memSobolev_add hψ hφ
  smul_mem' := by
    intro c ψ hψ
    change MemSobolev (2 : ℝ) 2 (l2ToTemperedDistribution1D (c • ψ))
    rw [map_smul]
    exact memSobolev_smul c hψ

@[simp]
theorem mem_continuumH2Domain1D_iff (ψ : ContinuumL2Wavefunction1D) :
    ψ ∈ continuumH2Domain1D ↔
      MemSobolev (2 : ℝ) 2 (l2ToTemperedDistribution1D ψ) :=
  Iff.rfl

/-- Bundle an `L²` wavefunction in the explicit `H²` domain as Mathlib's Sobolev object. -/
noncomputable def continuumH2ToSobolev1D :
    continuumH2Domain1D →ₗ[ℂ] Sobolev ℝ ℂ 2 2 where
  toFun ψ :=
    ((mem_continuumH2Domain1D_iff (ψ : ContinuumL2Wavefunction1D)).mp ψ.property).toSobolev
  map_add' ψ φ := by
    apply Sobolev.ext
    simp [l2ToTemperedDistribution1D]
  map_smul' c ψ := by
    apply Sobolev.ext
    simp [l2ToTemperedDistribution1D]

@[simp]
theorem continuumH2ToSobolev1D_toDistr (ψ : continuumH2Domain1D) :
    (continuumH2ToSobolev1D ψ).toDistr =
      l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D) :=
  rfl

/-- The distributional Laplacian on the `H²` domain, returned as an `L²` wavefunction.

This is linear because Mathlib already packages the Laplacian as a linear map
`H² → H⁰`, and `H⁰` carries its canonical `L²` representative. -/
noncomputable def continuumH2Laplacian1D :
    continuumH2Domain1D →ₗ[ℂ] ContinuumL2Wavefunction1D :=
  (Sobolev.toLpₗ ℝ ℂ ((2 : ℝ) - 2) 2).comp
    ((Sobolev.laplacianₗ (E := ℝ) (F := ℂ) (s := (2 : ℝ))).comp
      continuumH2ToSobolev1D)

@[simp]
theorem continuumH2Laplacian1D_apply (ψ : continuumH2Domain1D) :
    continuumH2Laplacian1D ψ =
      (Δ (continuumH2ToSobolev1D ψ) : Sobolev ℝ ℂ ((2 : ℝ) - 2) 2).sobFn :=
  rfl

/-- The `L²` value produced by `continuumH2Laplacian1D` represents exactly the distributional
Laplacian of the original `L²` wavefunction. -/
theorem l2ToTemperedDistribution1D_continuumH2Laplacian1D
    (ψ : continuumH2Domain1D) :
    l2ToTemperedDistribution1D (continuumH2Laplacian1D ψ) =
      Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) := by
  let u : Sobolev ℝ ℂ 2 2 := continuumH2ToSobolev1D ψ
  let Δu : Sobolev ℝ ℂ ((2 : ℝ) - 2) 2 := Δ u
  have hrepr :
      Δu.toDistr = l2ToTemperedDistribution1D Δu.sobFn := by
    have h := Δu.bessel_toDistr_eq_sobFn
    norm_num at h
    simpa [l2ToTemperedDistribution1D] using h
  calc
    l2ToTemperedDistribution1D (continuumH2Laplacian1D ψ) =
        l2ToTemperedDistribution1D Δu.sobFn := by
          rfl
    _ = Δu.toDistr := hrepr.symm
    _ = Δ u.toDistr := by
      exact Sobolev.laplacian_toDistr u
    _ = Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) := by
      rw [continuumH2ToSobolev1D_toDistr]

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
  continuumSchrodingerHamiltonian1D κ (realTestMultiplier1D potential hpotential)

@[simp]
theorem continuumRealPotentialSchrodingerHamiltonian1D_domain
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)) :
    (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential).domain =
      continuumH2Domain1D :=
  rfl

end
end Continuum
end QuantumTheory
