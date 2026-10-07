/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Brillouin
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

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
  smooth : ContDiff ℝ ∞ hamiltonian

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
  smooth : ContDiff ℝ ∞ projector

end

end QuantumTheory.Transport.Topology
