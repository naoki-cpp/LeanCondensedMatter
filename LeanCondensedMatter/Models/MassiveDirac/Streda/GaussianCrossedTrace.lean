import LeanCondensedMatter.Models.MassiveDirac.Model.Basic
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

namespace QuantumTheory.Models.MassiveDirac

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

/-- The four-matrix trace is bilinear in the two current insertions.
Rotating these two source currents by opposite plane-vector axes produces a
constant antisymmetric term and the two traceless second harmonics. This
algebraic fact applies to both crossed topologies before complex conjugation. -/
private theorem trace_four_rotated_currents
    (A B C D G H : Matrix2) (c s : ℝ) :
    Matrix.trace
      ((((c : ℂ) • A - (s : ℂ) • B) * G) *
        ((s : ℂ) • C + (c : ℂ) • D) * H) =
      (c : ℂ) ^ 2 * Matrix.trace (A * G * D * H) -
        (s : ℂ) ^ 2 * Matrix.trace (B * G * C * H) +
        ((c : ℂ) * (s : ℂ)) *
          (Matrix.trace (A * G * C * H) -
            Matrix.trace (B * G * D * H)) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- The four-current tensor values that enter a rotated crossed source pair.
In the `Psi` branch the Hermitian-conjugate trace is included exactly as in
the canonical crossed topology, so the rotation coefficients must be real. -/
theorem gaussianCrossedTraceKernel_rotated_sources
    {R : Type*} [Neg R] (diagram : GaussianCrossedDiagram)
    (greenRetarded greenAdvanced : R → Matrix2)
    (current : Fin 2 → R → Matrix2) (r : R) (c s : ℝ) :
    gaussianCrossedTraceKernel diagram greenRetarded greenAdvanced
        (fun axis ρ =>
          if axis = 0 then
            (c : ℂ) • current 0 ρ - (s : ℂ) • current 1 ρ
          else
            (s : ℂ) • current 0 ρ + (c : ℂ) • current 1 ρ) r =
      (c : ℂ) ^ 2 *
        gaussianCrossedTraceKernel diagram greenRetarded greenAdvanced current r -
      (s : ℂ) ^ 2 *
        gaussianCrossedTraceKernel diagram greenRetarded greenAdvanced
          (fun axis ρ => if axis = 0 then current 1 ρ else current 0 ρ) r +
      (c : ℂ) * (s : ℂ) *
        (gaussianCrossedTraceKernel diagram greenRetarded greenAdvanced
            (fun _ ρ => current 0 ρ) r -
          gaussianCrossedTraceKernel diagram greenRetarded greenAdvanced
            (fun _ ρ => current 1 ρ) r) := by
  cases diagram with
  | x =>
      simp only [gaussianCrossedTraceKernel, ↓reduceIte]
      exact trace_four_rotated_currents
        (current 0 r) (current 1 r) (current 0 r) (current 1 r)
        (greenRetarded (-r)) (greenAdvanced (-r)) c s
  | psi =>
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      have hamplitude := trace_four_rotated_currents
        (current 0 r) (current 1 r)
        (current 0 (-r)) (current 1 (-r))
        (greenRetarded (-r) * greenRetarded r) (1 : Matrix2) c s
      simp only [Matrix.mul_assoc, Matrix.mul_one] at hamplitude
      have hconj := congrArg (starRingEnd ℂ) hamplitude
      simp only [map_add, map_sub, map_mul, map_pow] at hconj
      have hc : (starRingEnd ℂ) (c : ℂ) = (c : ℂ) := by simp
      have hs : (starRingEnd ℂ) (s : ℂ) = (s : ℂ) := by simp
      rw [hc, hs] at hconj
      simp only [gaussianCrossedTraceKernel, ↓reduceIte,
        if_neg h10, Matrix.mul_assoc]
      rw [hamplitude, hconj]
      ring

/-- The trace-level `Psi` kernel is real by construction of its Hermitian-conjugate pair. -/
@[simp] theorem gaussianCrossedTraceKernel_psi_im {R : Type*} [Neg R]
    (greenRetarded greenAdvanced : R → Matrix2)
    (realSpaceCurrentBlock : Fin 2 → R → Matrix2)
    (r : R) :
    (gaussianCrossedTraceKernel .psi greenRetarded greenAdvanced realSpaceCurrentBlock r).im = 0 := by
  simp [gaussianCrossedTraceKernel]

end

end QuantumTheory.Models.MassiveDirac
