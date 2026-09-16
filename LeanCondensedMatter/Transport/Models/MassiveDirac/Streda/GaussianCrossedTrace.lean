import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Gaussian crossed Hall trace topologies

This module records the finite two-band trace structure of the leading crossed Gaussian impurity
contractions in the massive-Dirac Hall problem. It is the real-space Středa trace boundary
corresponding to Ado et al., EPL 111, 37004 (2015), Eq. (13a,b), before any real-space integration,
conductivity prefactor, or Bessel-function evaluation is introduced.

The two crossed topologies are kept in one indexed API. They remain separate from the non-crossing
ladder abstraction and from any later non-Gaussian `C3` contribution. The trace topology is
parameterized by an arbitrary negatable separation type, so Cartesian real-space and radial
specializations share the same canonical `X` / `Psi` construction.

For a real-space separation `r`, the `realSpaceCurrentBlock` input represents Ado et al. Eq. (14),
namely the Fourier-transformed current block `J_r` built from a current vertex between advanced and
retarded Green functions. It is therefore not the repository's algebraic RA dressed source-current
vertex `Γ`; constructing the massive-Dirac realization of `J_r` is a separate downstream step. The
`psi` branch writes the `h.c.` term at trace level as `z + conj z`.

No claim about the continuum integral, weak-disorder scaling, or the eventual massive-Dirac
cancellation of the `psi` contribution is made here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- The two single-crossing Gaussian impurity topologies contributing at leading order to the
massive-Dirac anomalous Hall response. -/
inductive GaussianCrossedDiagram where
  | x
  | psi
  deriving DecidableEq

instance : Fintype GaussianCrossedDiagram where
  elems := {.x, .psi}
  complete := by
    intro diagram
    cases diagram <;> simp

/-- A finite sum over the two Gaussian crossed topologies is the `X` contribution plus the `Psi`
contribution. -/
theorem sum_gaussianCrossedDiagram {M : Type*} [AddCommMonoid M]
    (f : GaussianCrossedDiagram → M) :
    ∑ diagram : GaussianCrossedDiagram, f diagram = f .x + f .psi := by
  change ∑ diagram ∈ ({.x, .psi} : Finset GaussianCrossedDiagram), f diagram = _
  simp

/-- Pointwise trace kernel for the two leading crossed Gaussian Hall topologies.

The separation type is required only to support `r ↦ -r`, allowing the same topology to be reused
for Cartesian real-space vectors and scalar radial coordinates.

The `realSpaceCurrentBlock` argument is Ado's `J_r` block from Eq. (14), not the local dressed vertex
`Γ`. For `x` this is
`Tr(Jˣ(r) Gᴿ(-r) Jʸ(r) Gᴬ(-r))`.

For `psi` the traced amplitude is
`Tr(Jˣ(r) Gᴿ(-r) Gᴿ(r) Jʸ(-r)) + h.c.`;
the Hermitian-conjugate contribution is represented after taking the trace as complex conjugation.
-/
def gaussianCrossedTraceKernel {R : Type*} [Neg R]
    (diagram : GaussianCrossedDiagram)
    (greenRetarded greenAdvanced : R → Matrix2)
    (realSpaceCurrentBlock : Fin 2 → R → Matrix2)
    (r : R) : ℂ :=
  match diagram with
  | .x =>
      Matrix.trace
        (realSpaceCurrentBlock 0 r * greenRetarded (-r) *
          realSpaceCurrentBlock 1 r * greenAdvanced (-r))
  | .psi =>
      let amplitude :=
        Matrix.trace
          (realSpaceCurrentBlock 0 r * greenRetarded (-r) * greenRetarded r *
            realSpaceCurrentBlock 1 (-r))
      amplitude + (starRingEnd ℂ) amplitude

/-- The trace-level `Psi` kernel is real by construction of its Hermitian-conjugate pair. -/
@[simp] theorem gaussianCrossedTraceKernel_psi_im {R : Type*} [Neg R]
    (greenRetarded greenAdvanced : R → Matrix2)
    (realSpaceCurrentBlock : Fin 2 → R → Matrix2)
    (r : R) :
    (gaussianCrossedTraceKernel .psi greenRetarded greenAdvanced realSpaceCurrentBlock r).im = 0 := by
  simp [gaussianCrossedTraceKernel]

end

end QuantumTheory.Transport.Models.MassiveDirac
