import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonianSelfAdjointCriterion1D
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Self-adjointness of the one-dimensional free Laplacian

This file proves the reverse adjoint-domain inclusion isolated by the preceding criterion layer.
For a vector in the adjoint domain of the `H²` Laplacian, the adjoint relation is tested against
complex-conjugated Schwartz functions. This identifies the adjoint value as the distributional
Laplacian of the original vector. Maximal-domain regularity then forces the vector back into `H²`.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace SchwartzMap Laplacian LineDeriv

/-- Complex conjugation preserves the Schwartz class. -/
private noncomputable def schwartzConj1D (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  f.postcompCLM
    ((RCLike.conjCLE (K := ℂ)).toContinuousLinearMap : ℂ →L[ℝ] ℂ)

@[simp]
private theorem schwartzConj1D_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzConj1D f x = star (f x) :=
  rfl

private theorem deriv_schwartzConj1D (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (schwartzConj1D f) x = star (deriv f x) := by
  change deriv (fun y : ℝ => star (f y)) x = star (deriv (f : ℝ → ℂ) x)
  exact (SchwartzMap.hasDerivAt f x).star.deriv

private theorem derivCLM_schwartzConj1D (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (schwartzConj1D f) =
      schwartzConj1D (SchwartzMap.derivCLM ℂ ℂ f) := by
  ext x
  simpa using deriv_schwartzConj1D f x

private theorem schwartz_laplacian_eq_second_deriv (f : SchwartzMap ℝ ℂ) :
    Δ f = SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f) := by
  ext x
  rw [SchwartzMap.laplacian_apply, InnerProductSpace.laplacian_eq_iteratedDeriv_real]
  change iteratedDeriv 2 (f : ℝ → ℂ) x = deriv (SchwartzMap.derivCLM ℂ ℂ f) x
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ', iteratedDeriv_one]
  rfl

private theorem laplacian_schwartzConj1D (f : SchwartzMap ℝ ℂ) :
    Δ (schwartzConj1D f) = schwartzConj1D (Δ f) := by
  rw [schwartz_laplacian_eq_second_deriv, schwartz_laplacian_eq_second_deriv]
  rw [derivCLM_schwartzConj1D, derivCLM_schwartzConj1D]

/-- On a Schwartz core vector, the explicit `H²` Laplacian is represented by the classical
Schwartz Laplacian. -/
theorem continuumH2Laplacian1D_schwartz_toLp (f : SchwartzMap ℝ ℂ) :
    continuumH2Laplacian1D
        ⟨f.toLp 2 (volume : Measure ℝ), schwartz_toLp_mem_continuumH2Domain1D f⟩ =
      (Δ f).toLp 2 (volume : Measure ℝ) := by
  apply l2ToTemperedDistribution1D_injective
  rw [l2ToTemperedDistribution1D_continuumH2Laplacian1D]
  simp [l2ToTemperedDistribution1D]

/-- Every vector in the adjoint domain of the free `H²` Laplacian already belongs to `H²`. -/
theorem continuumH2LaplacianPMap1D_adjoint_domain_le :
    continuumH2LaplacianPMap1D.adjoint.domain ≤ continuumH2Domain1D := by
  intro u hu
  rw [continuumH2Domain1D_eq_continuumMaximalLaplacianDomain1D]
  rw [mem_continuumMaximalLaplacianDomain1D_iff]
  let uAdj : continuumH2LaplacianPMap1D.adjoint.domain := ⟨u, hu⟩
  let w : ContinuumL2Wavefunction1D := continuumH2LaplacianPMap1D.adjoint uAdj
  refine ⟨w, ?_⟩
  ext g
  have hinner (f : SchwartzMap ℝ ℂ) :
      inner ℂ (f.toLp 2 (volume : Measure ℝ)) w =
        inner ℂ
          (continuumH2Laplacian1D
            ⟨f.toLp 2 (volume : Measure ℝ), schwartz_toLp_mem_continuumH2Domain1D f⟩)
          u := by
    let fH2 : continuumH2Domain1D :=
      ⟨f.toLp 2 (volume : Measure ℝ), schwartz_toLp_mem_continuumH2Domain1D f⟩
    have hadj :=
      LinearPMap.adjoint_isFormalAdjoint continuumH2Domain1D_dense uAdj fH2
    have hswap :
        inner ℂ (f.toLp 2 (volume : Measure ℝ)) w =
          inner ℂ (continuumH2Laplacian1D fH2) u := by
      calc
        inner ℂ (f.toLp 2 (volume : Measure ℝ)) w =
            (starRingEnd ℂ) (inner ℂ w (f.toLp 2 (volume : Measure ℝ))) := by
              exact (inner_conj_symm (f.toLp 2 (volume : Measure ℝ)) w).symm
        _ = (starRingEnd ℂ) (inner ℂ u (continuumH2Laplacian1D fH2)) := by
              rw [show inner ℂ w (f.toLp 2 (volume : Measure ℝ)) =
                inner ℂ u (continuumH2Laplacian1D fH2) by
                  simpa [w, uAdj, fH2, continuumH2LaplacianPMap1D] using hadj]
        _ = inner ℂ (continuumH2Laplacian1D fH2) u := by
              exact inner_conj_symm (continuumH2Laplacian1D fH2) u
    simpa [fH2] using hswap
  have hcore := hinner (schwartzConj1D g)
  rw [continuumH2Laplacian1D_schwartz_toLp] at hcore
  simp only [l2ToTemperedDistribution1D,
    MeasureTheory.Lp.toTemperedDistributionCLM_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply,
    TemperedDistribution.laplacian_apply_apply]
  change (∫ x, g x * w x) = ∫ x, (Δ g) x * u x
  calc
    (∫ x, g x * w x) =
        inner ℂ ((schwartzConj1D g).toLp 2 (volume : Measure ℝ)) w := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(schwartzConj1D g).coeFn_toLp 2 (volume : Measure ℝ)] with x hx
      rw [hx]
      simp [RCLike.inner_apply, mul_comm]
    _ = inner ℂ ((Δ (schwartzConj1D g)).toLp 2 (volume : Measure ℝ)) u := hcore
    _ = inner ℂ ((schwartzConj1D (Δ g)).toLp 2 (volume : Measure ℝ)) u := by
      rw [laplacian_schwartzConj1D]
    _ = ∫ x, (Δ g) x * u x := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(schwartzConj1D (Δ g)).coeFn_toLp 2 (volume : Measure ℝ)] with x hx
      rw [hx]
      simp [RCLike.inner_apply, mul_comm]
  all_goals rfl

/-- The free distributional Laplacian on `H²(ℝ)` is self-adjoint on physical `L²(ℝ, ℂ)`. -/
theorem continuumH2LaplacianPMap1D_isSelfAdjoint :
    IsSelfAdjoint continuumH2LaplacianPMap1D :=
  continuumH2LaplacianPMap1D_isSelfAdjoint_iff_adjoint_domain_le.mpr
    continuumH2LaplacianPMap1D_adjoint_domain_le

end
end Continuum
end SingleParticle
end QuantumMechanics
