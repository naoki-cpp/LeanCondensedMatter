import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonianAnalytic1D
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Closed maximal distributional Laplacian on `L²(ℝ, ℂ)`

The `H²` Schrödinger domain introduced earlier is a natural analytic domain, but Mathlib 4.31.0
currently exposes only the predicate-level Bessel-potential Sobolev API. In particular, the released
API does not yet provide the converse regularity statement identifying `H²` with the set of
`L²` functions whose distributional Laplacian has an `L²` representative.

This file therefore isolates the closed-operator statement at the maximal distributional level.
The domain consists exactly of `L²` wavefunctions whose distributional Laplacian is represented by
another `L²` function. The resulting partial linear map is closed because its graph is the equality
locus of two continuous maps into tempered distributions.

The existing `H²` Laplacian is proved to lie inside this maximal domain and to agree with the
maximal operator there. Thus the remaining regularity problem is cleanly separated as the reverse
domain inclusion `continuumMaximalLaplacianDomain1D ≤ continuumH2Domain1D`.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory SchwartzMap Laplacian LineDeriv

private theorem l2ToTemperedDistribution1D_injective_closed :
    Function.Injective l2ToTemperedDistribution1D := by
  change Function.Injective
    (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2)
  apply LinearMap.ker_eq_bot.mp
  exact MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot

/-- The maximal distributional Laplacian domain in `L²(ℝ, ℂ)`: a wavefunction belongs to the
 domain exactly when its distributional Laplacian has an `L²` representative. -/
noncomputable def continuumMaximalLaplacianDomain1D :
    Submodule ℂ ContinuumL2Wavefunction1D where
  carrier := {ψ | ∃ φ : ContinuumL2Wavefunction1D,
    l2ToTemperedDistribution1D φ = Δ (l2ToTemperedDistribution1D ψ)}
  zero_mem' := by
    refine ⟨0, ?_⟩
    rw [map_zero]
    simpa only [TemperedDistribution.laplacianCLM_apply] using
      (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).map_zero.symm
  add_mem' := by
    rintro ψ φ ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    calc
      l2ToTemperedDistribution1D (u + v) =
          l2ToTemperedDistribution1D u + l2ToTemperedDistribution1D v := by rw [map_add]
      _ = Δ (l2ToTemperedDistribution1D ψ) + Δ (l2ToTemperedDistribution1D φ) := by
        rw [hu, hv]
      _ = Δ (l2ToTemperedDistribution1D ψ + l2ToTemperedDistribution1D φ) := by
        symm
        simpa only [TemperedDistribution.laplacianCLM_apply] using
          (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).map_add
            (l2ToTemperedDistribution1D ψ) (l2ToTemperedDistribution1D φ)
      _ = Δ (l2ToTemperedDistribution1D (ψ + φ)) := by rw [map_add]
  smul_mem' := by
    rintro c ψ ⟨u, hu⟩
    refine ⟨c • u, ?_⟩
    calc
      l2ToTemperedDistribution1D (c • u) = c • l2ToTemperedDistribution1D u := by rw [map_smul]
      _ = c • Δ (l2ToTemperedDistribution1D ψ) := by rw [hu]
      _ = Δ (c • l2ToTemperedDistribution1D ψ) := by
        symm
        simpa only [TemperedDistribution.laplacianCLM_apply, RingHom.id_apply] using
          (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).map_smul c
            (l2ToTemperedDistribution1D ψ)
      _ = Δ (l2ToTemperedDistribution1D (c • ψ)) := by rw [map_smul]

@[simp]
theorem mem_continuumMaximalLaplacianDomain1D_iff (ψ : ContinuumL2Wavefunction1D) :
    ψ ∈ continuumMaximalLaplacianDomain1D ↔
      ∃ φ : ContinuumL2Wavefunction1D,
        l2ToTemperedDistribution1D φ = Δ (l2ToTemperedDistribution1D ψ) :=
  Iff.rfl

/-- Every `H²` wavefunction belongs to the maximal distributional Laplacian domain. -/
theorem continuumH2Domain1D_le_continuumMaximalLaplacianDomain1D :
    continuumH2Domain1D ≤ continuumMaximalLaplacianDomain1D := by
  intro ψ hψ
  let ψH2 : continuumH2Domain1D := ⟨ψ, hψ⟩
  refine ⟨continuumH2Laplacian1D ψH2, ?_⟩
  exact l2ToTemperedDistribution1D_continuumH2Laplacian1D ψH2

/-- The unique `L²` representative of the distributional Laplacian on the maximal domain. -/
private noncomputable def continuumMaximalLaplacianValue1D
    (ψ : continuumMaximalLaplacianDomain1D) : ContinuumL2Wavefunction1D :=
  Classical.choose ψ.property

private theorem l2ToTemperedDistribution1D_continuumMaximalLaplacianValue1D
    (ψ : continuumMaximalLaplacianDomain1D) :
    l2ToTemperedDistribution1D (continuumMaximalLaplacianValue1D ψ) =
      Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) :=
  Classical.choose_spec ψ.property

/-- The maximal distributional Laplacian, as a linear map from its explicit domain to `L²`. -/
noncomputable def continuumMaximalLaplacianOnDomain1D :
    continuumMaximalLaplacianDomain1D →ₗ[ℂ] ContinuumL2Wavefunction1D where
  toFun := continuumMaximalLaplacianValue1D
  map_add' ψ φ := by
    apply l2ToTemperedDistribution1D_injective_closed
    rw [map_add]
    rw [l2ToTemperedDistribution1D_continuumMaximalLaplacianValue1D,
      l2ToTemperedDistribution1D_continuumMaximalLaplacianValue1D,
      l2ToTemperedDistribution1D_continuumMaximalLaplacianValue1D]
    simp only [Submodule.coe_add, map_add]
    simpa only [TemperedDistribution.laplacianCLM_apply] using
      (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).map_add
        (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D))
        (l2ToTemperedDistribution1D (φ : ContinuumL2Wavefunction1D))
  map_smul' c ψ := by
    apply l2ToTemperedDistribution1D_injective_closed
    rw [map_smul]
    rw [l2ToTemperedDistribution1D_continuumMaximalLaplacianValue1D,
      l2ToTemperedDistribution1D_continuumMaximalLaplacianValue1D]
    simp only [Submodule.coe_smul, map_smul]
    simpa only [TemperedDistribution.laplacianCLM_apply, RingHom.id_apply] using
      (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).map_smul c
        (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D))

/-- The maximal distributional Laplacian as a partial linear map on physical `L²`. -/
noncomputable def continuumMaximalLaplacian1D :
    ContinuumL2Wavefunction1D →ₗ.[ℂ] ContinuumL2Wavefunction1D where
  domain := continuumMaximalLaplacianDomain1D
  toFun := continuumMaximalLaplacianOnDomain1D

@[simp]
theorem continuumMaximalLaplacian1D_domain :
    continuumMaximalLaplacian1D.domain = continuumMaximalLaplacianDomain1D :=
  rfl

@[simp]
theorem l2ToTemperedDistribution1D_continuumMaximalLaplacian1D
    (ψ : continuumMaximalLaplacianDomain1D) :
    l2ToTemperedDistribution1D (continuumMaximalLaplacian1D ψ) =
      Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) :=
  l2ToTemperedDistribution1D_continuumMaximalLaplacianValue1D ψ

/-- The maximal Laplacian agrees with the previously constructed `H²` Laplacian on `H²`. -/
theorem continuumMaximalLaplacian1D_agrees_on_H2 (ψ : continuumH2Domain1D) :
    continuumMaximalLaplacian1D
        ⟨(ψ : ContinuumL2Wavefunction1D),
          continuumH2Domain1D_le_continuumMaximalLaplacianDomain1D ψ.property⟩ =
      continuumH2Laplacian1D ψ := by
  apply l2ToTemperedDistribution1D_injective_closed
  rw [l2ToTemperedDistribution1D_continuumMaximalLaplacian1D,
    l2ToTemperedDistribution1D_continuumH2Laplacian1D]

/-- Graph membership in the maximal Laplacian is exactly the distributional Laplacian equation. -/
theorem mem_continuumMaximalLaplacian1D_graph_iff
    (z : ContinuumL2Wavefunction1D × ContinuumL2Wavefunction1D) :
    z ∈ continuumMaximalLaplacian1D.graph ↔
      l2ToTemperedDistribution1D z.2 = Δ (l2ToTemperedDistribution1D z.1) := by
  constructor
  · intro hz
    rw [LinearPMap.mem_graph_iff] at hz
    obtain ⟨ψ, hψ, hΔψ⟩ := hz
    calc
      l2ToTemperedDistribution1D z.2 =
          l2ToTemperedDistribution1D (continuumMaximalLaplacian1D ψ) := by
            rw [hΔψ]
      _ = Δ (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) :=
        l2ToTemperedDistribution1D_continuumMaximalLaplacian1D ψ
      _ = Δ (l2ToTemperedDistribution1D z.1) := by rw [hψ]
  · intro hz
    have hdomain : z.1 ∈ continuumMaximalLaplacianDomain1D := ⟨z.2, hz⟩
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨z.1, hdomain⟩, rfl, ?_⟩
    apply l2ToTemperedDistribution1D_injective_closed
    rw [l2ToTemperedDistribution1D_continuumMaximalLaplacian1D]
    exact hz.symm

/-- The maximal distributional Laplacian is a closed unbounded operator on `L²(ℝ, ℂ)`. -/
theorem continuumMaximalLaplacian1D_isClosed : continuumMaximalLaplacian1D.IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph :
      (continuumMaximalLaplacian1D.graph :
        Set (ContinuumL2Wavefunction1D × ContinuumL2Wavefunction1D)) =
        {z | l2ToTemperedDistribution1D z.2 = Δ (l2ToTemperedDistribution1D z.1)} := by
    ext z
    exact mem_continuumMaximalLaplacian1D_graph_iff z
  rw [hgraph]
  apply isClosed_eq
  · exact l2ToTemperedDistribution1D.continuous.comp
      (continuous_snd : Continuous
        (fun z : ContinuumL2Wavefunction1D × ContinuumL2Wavefunction1D => z.2))
  · have hcont :
        Continuous (fun z : ContinuumL2Wavefunction1D × ContinuumL2Wavefunction1D =>
          (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ))
            (l2ToTemperedDistribution1D z.1)) := by
      exact (LineDeriv.laplacianCLM ℂ ℝ 𝓢'(ℝ, ℂ)).continuous.comp
        (l2ToTemperedDistribution1D.continuous.comp
          (continuous_fst : Continuous
            (fun z : ContinuumL2Wavefunction1D × ContinuumL2Wavefunction1D => z.1)))
    simpa only [TemperedDistribution.laplacianCLM_apply] using hcont

/-- The maximal distributional Laplacian is densely defined because it contains the dense `H²`
domain. -/
theorem continuumMaximalLaplacian1D_denseDomain :
    Dense ((continuumMaximalLaplacian1D.domain : Submodule ℂ ContinuumL2Wavefunction1D) :
      Set ContinuumL2Wavefunction1D) := by
  rw [continuumMaximalLaplacian1D_domain]
  exact Dense.mono continuumH2Domain1D_le_continuumMaximalLaplacianDomain1D
    continuumH2Domain1D_dense

/-- In particular, the maximal distributional Laplacian is closable. -/
theorem continuumMaximalLaplacian1D_isClosable : continuumMaximalLaplacian1D.IsClosable :=
  continuumMaximalLaplacian1D_isClosed.isClosable

end
end Continuum
end SingleParticle
end QuantumMechanics
