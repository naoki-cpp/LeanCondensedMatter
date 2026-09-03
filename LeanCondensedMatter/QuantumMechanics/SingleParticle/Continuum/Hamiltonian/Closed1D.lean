import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Hamiltonian.Regularity1D
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Closed Schrödinger Hamiltonian on the explicit `H²` domain

The maximal distributional Laplacian is closed, and the preceding regularity layer identifies its
maximal domain with the explicit Bessel-potential `H²` domain. This file transfers closedness to the
`H²` Laplacian and then adds an essentially bounded multiplication potential.

For nonzero kinetic coefficient `κ`, graph membership for

`H = -κ Δ + V`

is characterized entirely in tempered distributions by

`ι(y - Vx) = -κ Δ ι(x)`.

The converse direction uses this equation to exhibit an `L²` representative of the distributional
Laplacian; maximal-domain regularity then recovers `x ∈ H²`. Since both sides of the graph equation
are continuous functions of `(x,y) ∈ L² × L²`, the graph is closed.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory SchwartzMap Laplacian LineDeriv

/-- The `H²` distributional Laplacian packaged as a partial linear map on physical `L²`. -/
noncomputable def continuumH2LaplacianPMap1D :
    ContinuumL2Wavefunction1D →ₗ.[ℂ] ContinuumL2Wavefunction1D where
  domain := continuumH2Domain1D
  toFun := continuumH2Laplacian1D

@[simp]
theorem continuumH2LaplacianPMap1D_domain :
    continuumH2LaplacianPMap1D.domain = continuumH2Domain1D :=
  rfl

/-- After maximal-domain regularity, the explicit `H²` Laplacian is exactly the maximal
 distributional Laplacian. -/
theorem continuumH2LaplacianPMap1D_eq_continuumMaximalLaplacian1D :
    continuumH2LaplacianPMap1D = continuumMaximalLaplacian1D := by
  apply LinearPMap.ext continuumH2Domain1D_eq_continuumMaximalLaplacianDomain1D
  intro x hx hmax
  let ψ : continuumH2Domain1D := ⟨x, hx⟩
  have hagree := continuumMaximalLaplacian1D_agrees_on_H2 ψ
  simpa [continuumH2LaplacianPMap1D, ψ] using hagree.symm

/-- The distributional Laplacian on the explicit `H²` domain is closed. -/
theorem continuumH2LaplacianPMap1D_isClosed : continuumH2LaplacianPMap1D.IsClosed := by
  simpa only [continuumH2LaplacianPMap1D_eq_continuumMaximalLaplacian1D] using
    continuumMaximalLaplacian1D_isClosed

/-- The `L²` Hamiltonian value represents the expected distributional Schrödinger action. -/
theorem l2ToTemperedDistribution1D_continuumSchrodingerHamiltonian1D
    (κ : ℝ) (potential : ContinuumLInfMultiplier1D) (ψ : continuumH2Domain1D) :
    l2ToTemperedDistribution1D (continuumSchrodingerHamiltonian1D κ potential ψ) =
      -(κ : ℂ) • Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) +
        l2ToTemperedDistribution1D
          (l2MultiplicationOperator1D potential (ψ : ContinuumL2Wavefunction1D)) := by
  rw [continuumSchrodingerHamiltonian1D_apply, map_add, map_smul,
    l2ToTemperedDistribution1D_continuumH2Laplacian1D]

/-- For nonzero kinetic coefficient, graph membership is equivalent to the distributional
Schrödinger equation. The equation itself recovers the `H²` domain in the reverse direction. -/
theorem mem_continuumSchrodingerHamiltonian1D_graph_iff
    (κ : ℝ) (potential : ContinuumLInfMultiplier1D) (hκ : κ ≠ 0)
    (z : ContinuumL2Wavefunction1D × ContinuumL2Wavefunction1D) :
    z ∈ (continuumSchrodingerHamiltonian1D κ potential).graph ↔
      l2ToTemperedDistribution1D
          (z.2 - l2MultiplicationOperator1D potential z.1) =
        -(κ : ℂ) • Δ (l2ToTemperedDistribution1D z.1) := by
  constructor
  · intro hz
    rw [LinearPMap.mem_graph_iff] at hz
    obtain ⟨ψ, hx, hy⟩ := hz
    have hH := l2ToTemperedDistribution1D_continuumSchrodingerHamiltonian1D κ potential ψ
    rw [← hx, ← hy, map_sub, hH]
    abel
  · intro hz
    simp only [l2MultiplicationOperator1D_apply] at hz
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
    let φ : ContinuumL2Wavefunction1D :=
      -((κ : ℂ)⁻¹) • (z.2 - l2MultiplicationOperator1D potential z.1)
    have hφ :
        l2ToTemperedDistribution1D φ = Δ (l2ToTemperedDistribution1D z.1) := by
      dsimp [φ]
      rw [map_smul, hz, smul_smul]
      have hcoef : -((κ : ℂ)⁻¹) * -(κ : ℂ) = 1 := by
        field_simp [hκc]
      rw [hcoef, one_smul]
    have hmax : z.1 ∈ continuumMaximalLaplacianDomain1D := ⟨φ, hφ⟩
    have hH2 : z.1 ∈ continuumH2Domain1D :=
      continuumMaximalLaplacianDomain1D_le_continuumH2Domain1D hmax
    rw [LinearPMap.mem_graph_iff]
    let ψ : continuumH2Domain1D := ⟨z.1, hH2⟩
    refine ⟨ψ, rfl, ?_⟩
    apply l2ToTemperedDistribution1D_injective
    change l2ToTemperedDistribution1D
        (continuumSchrodingerHamiltonian1D κ potential ψ) =
      l2ToTemperedDistribution1D z.2
    rw [l2ToTemperedDistribution1D_continuumSchrodingerHamiltonian1D]
    rw [map_sub] at hz
    rw [← hz]
    have hψcoe : (ψ : ContinuumL2Wavefunction1D) = z.1 := rfl
    rw [hψcoe, l2MultiplicationOperator1D_apply]
    abel

/-- The one-dimensional Schrödinger Hamiltonian with an essentially bounded potential is closed on
`H²(ℝ)` whenever the kinetic coefficient is nonzero. -/
theorem continuumSchrodingerHamiltonian1D_isClosed
    (κ : ℝ) (potential : ContinuumLInfMultiplier1D) (hκ : κ ≠ 0) :
    (continuumSchrodingerHamiltonian1D κ potential).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph :
      ((continuumSchrodingerHamiltonian1D κ potential).graph :
        Set (ContinuumL2Wavefunction1D × ContinuumL2Wavefunction1D)) =
        {z |
          l2ToTemperedDistribution1D
              (z.2 - l2MultiplicationOperator1D potential z.1) =
            -(κ : ℂ) • Δ (l2ToTemperedDistribution1D z.1)} := by
    ext z
    exact mem_continuumSchrodingerHamiltonian1D_graph_iff κ potential hκ z
  rw [hgraph]
  apply isClosed_eq
  · exact l2ToTemperedDistribution1D.continuous.comp (by fun_prop)
  · have hcont :
        Continuous (fun z : ContinuumL2Wavefunction1D × ContinuumL2Wavefunction1D =>
          -(κ : ℂ) •
            (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ))
              (l2ToTemperedDistribution1D z.1)) := by
      fun_prop
    simpa only [TemperedDistribution.laplacianCLM_apply] using hcont

/-- Real bounded scalar-potential specialization of closedness. -/
theorem continuumRealPotentialSchrodingerHamiltonian1D_isClosed
    (κ : ℝ) (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ))
    (hκ : κ ≠ 0) :
    (continuumRealPotentialSchrodingerHamiltonian1D κ potential hpotential).IsClosed :=
  continuumSchrodingerHamiltonian1D_isClosed
    κ (realLInfMultiplier1D potential hpotential) hκ

end
end Continuum
end SingleParticle
end QuantumMechanics
