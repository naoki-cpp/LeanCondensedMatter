/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Brillouin
import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Complex.Module

set_option linter.style.header false

/-!
# Periodic Bloch data

This module provides the global covering-space data used by clean topological transport.

The momentum dependence lives on a real normed vector space and is periodic under a reciprocal
lattice. Hamiltonians are smooth self-adjoint bounded operators. Projector families are smooth
star projections, so self-adjointness and idempotence reuse Mathlib's `IsStarProjection` rather
than being duplicated as project-local fields.

No spectral-calculus construction of the occupied projector is assumed here. A later gapped
Hamiltonian bridge can prove that a concrete periodic projector is the occupied spectral projector.
-/

namespace QuantumTheory.Transport.Topology

noncomputable section

variable {K H : Type*}
variable [NormedAddCommGroup K] [NormedSpace ℝ K]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A smooth self-adjoint Bloch Hamiltonian on the covering momentum space, periodic under the
reciprocal lattice `Lstar`. -/
structure PeriodicBlochHamiltonian (Lstar : Submodule ℤ K) where
  /-- Momentum-dependent single-particle Hamiltonian. -/
  hamiltonian : K → H →L[ℂ] H
  /-- Self-adjointness at every momentum. -/
  selfAdjoint : ∀ k, IsSelfAdjoint (hamiltonian k)
  /-- Reciprocal-lattice periodicity on the covering momentum space. -/
  periodic : ∀ (G : Lstar) (k : K), hamiltonian (G +ᵥ k) = hamiltonian k
  /-- Smooth momentum dependence. -/
  smooth : ContDiff ℝ ⊤ hamiltonian

namespace PeriodicBlochHamiltonian

/-- The Fermi level lies outside the spectrum at every momentum. This is the clean band-gap
condition used by the TKNN construction; no uniform numerical gap size is imposed until a
downstream analytic argument requires one. -/
def IsFermiGapped {Lstar : Submodule ℤ K}
    (data : PeriodicBlochHamiltonian (H := H) Lstar) (fermiLevel : ℝ) : Prop :=
  ∀ k, (fermiLevel : ℂ) ∉ spectrum ℂ (data.hamiltonian k)

end PeriodicBlochHamiltonian

/-- A smooth periodic family of orthogonal projectors on the covering momentum space.

The projector property is represented by Mathlib's `IsStarProjection`, which packages
self-adjointness and idempotence. This is the gauge-invariant global datum consumed by projector
Berry curvature and Chern integration. -/
structure PeriodicBlochProjector (Lstar : Submodule ℤ K) where
  /-- Momentum-dependent orthogonal projector. -/
  projector : K → H →L[ℂ] H
  /-- Each operator is a self-adjoint idempotent. -/
  isStarProjection : ∀ k, IsStarProjection (projector k)
  /-- Reciprocal-lattice periodicity on the covering momentum space. -/
  periodic : ∀ (G : Lstar) (k : K), projector (G +ᵥ k) = projector k
  /-- Smooth momentum dependence. -/
  smooth : ContDiff ℝ ⊤ projector

/-- Finite-band clean Bloch data with an explicitly supplied occupied spectral projector.

The projector is characterized without a global eigenvector gauge: on every Hamiltonian
eigenvector it acts as the identity below the Fermi level and as zero above it. The separate
Fermi-gap field excludes the boundary case. This is the first vertical-slice boundary; constructing
the projector from functional calculus can be added later without changing downstream topology. -/
structure GappedBlochSystem (Lstar : Submodule ℤ K) [FiniteDimensional ℂ H] where
  /-- Smooth periodic self-adjoint Bloch Hamiltonian. -/
  blochHamiltonian : PeriodicBlochHamiltonian (H := H) Lstar
  /-- Fermi energy separating occupied and unoccupied bands. -/
  fermiLevel : ℝ
  /-- The Fermi level lies in the resolvent set at every momentum. -/
  fermiGap : blochHamiltonian.IsFermiGapped fermiLevel
  /-- Smooth periodic occupied projector. -/
  occupiedProjector : PeriodicBlochProjector (H := H) Lstar
  /-- Spectral characterization of the occupied projector on Hamiltonian eigenvectors. -/
  occupiedProjector_apply_eigenvector :
    ∀ (k : K) (energy : ℝ) (x : H),
      blochHamiltonian.hamiltonian k x = (energy : ℂ) • x →
        occupiedProjector.projector k x =
          if energy < fermiLevel then x else 0

namespace PeriodicBlochProjector

variable [FiniteDimensional ℂ H]

/-- Directional derivative of a smooth projector family on the covering momentum space. -/
noncomputable def directionalDerivative {Lstar : Submodule ℤ K}
    (data : PeriodicBlochProjector (H := H) Lstar) (k direction : K) :
    H →L[ℂ] H :=
  (fderiv ℝ data.projector k) direction

/-- Directional derivatives of a smooth orthogonal-projector family remain
self-adjoint. This follows by differentiating the pointwise identity `P⋆ = P` over the real
momentum space. -/
theorem directionalDerivative_isSelfAdjoint {Lstar : Submodule ℤ K}
    (data : PeriodicBlochProjector (H := H) Lstar) (k direction : K) :
    IsSelfAdjoint (data.directionalDerivative k direction) := by
  have hstar :
      (fun q : K => star (data.projector q)) = data.projector := by
    funext q
    exact (data.isStarProjection q).isSelfAdjoint
  have hderiv :=
    congrArg (fun f : K → H →L[ℂ] H => fderiv ℝ f k) hstar
  rw [fderiv_star] at hderiv
  have hdir := congrArg
    (fun D : K →L[ℝ] (H →L[ℂ] H) => D direction) hderiv
  simpa [directionalDerivative] using hdir

/-- Complex projector-curvature expression
`i Tr(P [∂_u P, ∂_v P])`.

The later real-valued Berry-curvature API will identify this scalar as real. Keeping the complex
expression explicit here avoids silently projecting with `.re`. -/
noncomputable def berryCurvatureComplex {Lstar : Submodule ℤ K}
    (data : PeriodicBlochProjector (H := H) Lstar) (k u v : K) : ℂ :=
  Complex.I * ContinuousLinearMap.finiteDimensionalOperatorTrace
    (data.projector k *
      (data.directionalDerivative k u * data.directionalDerivative k v -
        data.directionalDerivative k v * data.directionalDerivative k u))

/-- Projector curvature is antisymmetric in its two momentum directions. -/
theorem berryCurvatureComplex_swap {Lstar : Submodule ℤ K}
    (data : PeriodicBlochProjector (H := H) Lstar) (k u v : K) :
    data.berryCurvatureComplex k v u = -data.berryCurvatureComplex k u v := by
  have hcomm :
      data.projector k *
          (data.directionalDerivative k v * data.directionalDerivative k u -
            data.directionalDerivative k u * data.directionalDerivative k v) =
        -(data.projector k *
          (data.directionalDerivative k u * data.directionalDerivative k v -
            data.directionalDerivative k v * data.directionalDerivative k u)) := by
    noncomm_ring
  simp [berryCurvatureComplex, hcomm]

/-- The complex projector-curvature expression is self-adjoint as a complex scalar, hence real.

The proof uses self-adjointness of the projector and its directional derivatives, the resulting
skew-adjointness of their commutator, cyclicity of the finite-dimensional trace, and
`Tr(A⋆) = star (Tr A)`. -/
theorem berryCurvatureComplex_isSelfAdjoint {Lstar : Submodule ℤ K}
    (data : PeriodicBlochProjector (H := H) Lstar) (k u v : K) :
    IsSelfAdjoint (data.berryCurvatureComplex k u v) := by
  let P := data.projector k
  let A := data.directionalDerivative k u
  let B := data.directionalDerivative k v
  let C := A * B - B * A
  have hP : IsSelfAdjoint P := (data.isStarProjection k).isSelfAdjoint
  have hA : IsSelfAdjoint A := data.directionalDerivative_isSelfAdjoint k u
  have hB : IsSelfAdjoint B := data.directionalDerivative_isSelfAdjoint k v
  have hC : star C = -C := by
    dsimp [C]
    rw [map_sub, star_mul, star_mul, hA, hB]
    noncomm_ring
  have hstarPC : star (P * C) = -(C * P) := by
    rw [star_mul, hC, hP]
    simp
  have htrace :
      star (ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H) (P * C)) =
        -ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H) (P * C) := by
    calc
      star (ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H) (P * C)) =
          ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H) (star (P * C)) :=
        (ContinuousLinearMap.finiteDimensionalOperatorTrace_star (P * C)).symm
      _ = ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H) (-(C * P)) := by
        rw [hstarPC]
      _ = -ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H) (C * P) := by
        simp
      _ = -ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H) (P * C) := by
        rw [ContinuousLinearMap.finiteDimensionalOperatorTrace_mul_comm C P]
  change star
      (Complex.I * ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H) (P * C)) =
    Complex.I * ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H) (P * C)
  simp [map_mul, htrace]

/-- Projector Berry curvature, transported losslessly from its self-adjoint complex expression to
a real scalar. -/
noncomputable def berryCurvatureSelfAdjoint {Lstar : Submodule ℤ K}
    (data : PeriodicBlochProjector (H := H) Lstar) (k u v : K) : selfAdjoint ℂ :=
  ⟨data.berryCurvatureComplex k u v, data.berryCurvatureComplex_isSelfAdjoint k u v⟩

/-- Real-valued gauge-invariant projector Berry curvature. -/
noncomputable def berryCurvature {Lstar : Submodule ℤ K}
    (data : PeriodicBlochProjector (H := H) Lstar) (k u v : K) : ℝ :=
  Complex.selfAdjointEquiv (data.berryCurvatureSelfAdjoint k u v)

/-- Coercing the real projector curvature back to `ℂ` recovers the complex trace formula exactly. -/
theorem coe_berryCurvature {Lstar : Submodule ℤ K}
    (data : PeriodicBlochProjector (H := H) Lstar) (k u v : K) :
    (data.berryCurvature k u v : ℂ) = data.berryCurvatureComplex k u v := by
  exact Complex.coe_selfAdjointEquiv (data.berryCurvatureSelfAdjoint k u v)

/-- Real projector Berry curvature is antisymmetric in its momentum directions. -/
theorem berryCurvature_swap {Lstar : Submodule ℤ K}
    (data : PeriodicBlochProjector (H := H) Lstar) (k u v : K) :
    data.berryCurvature k v u = -data.berryCurvature k u v := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg, coe_berryCurvature, coe_berryCurvature,
    data.berryCurvatureComplex_swap]

end PeriodicBlochProjector

end

end QuantumTheory.Transport.Topology
