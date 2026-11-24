import LeanCondensedMatter.Models.RashbaExchange.Model
import LeanCondensedMatter.QuantumTheory.SpinfulLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedMatrixUnitAdjoint

set_option linter.style.header false

/-!
# Open-boundary finite real-space Rashba-exchange hopping

Use a rectangular subset of the square lattice with spacing `a`, real
physical momentum convention and the same `HamiltonianParameters` as the
clean two-band model. Put `t = ℏ²/(2 m_eff a²)` and
`λ = ℏ α_R/(2a)`. For matrix elements with target one site forward of
the source, the hopping blocks are

```text
T_x = -t I - i λ σ_y
T_y = -t I + i λ σ_x
H_onsite = 4t I + Δ σ_z.
```

The reverse blocks are their adjoints. The sign convention corresponds to
the plane-wave convention exp(i p · r / ℏ); no Fourier or continuum-limit
equivalence theorem is asserted here. The rectangular boundary is open:
there is no wraparound hopping. Physical applications take positive
spacing, mass and ℏ; the algebraic Hermiticity theorem needs none of
these inequalities.

The existing finite-amplitude hopping constructor, site geometry, and
bounded Fock lift are used without adding a second lattice/current API.
-/

namespace QuantumTheory.Models.RashbaExchange

open QuantumTheory.SpinfulLattice
open SecondQuantization.Fermionic.Lattice

noncomputable section

/-- Spatial labels of a finite open rectangle, with lexicographic order. -/
abbrev RectangularSite (nx ny : ℕ) := Fin nx ×ₗ Fin ny

/-- Integer-valued square-lattice coordinates of a spatial site. -/
def rectangularCoordinates {nx ny : ℕ} (x : RectangularSite nx ny) : ℕ × ℕ :=
  ((ofLex x).1.val, (ofLex x).2.val)

/-- Both internal spin components at a spatial site share the same physical position. -/
def realSpaceRashbaGeometry (nx ny : ℕ) (spacing : ℝ) :
    LatticeGeometry (SpinfulSite (RectangularSite nx ny)) (ℝ × ℝ) where
  position x :=
    let r := rectangularCoordinates (ofLex x).1
    (spacing * (r.1 : ℝ), spacing * (r.2 : ℝ))

/-- Positive-direction nearest-neighbor hopping block, in target/source convention. -/
def realSpaceRashbaForwardBlock
    (params : HamiltonianParameters) (hbar spacing : ℝ) (direction : Fin 2) :
    InternalSpace.PauliMatrix :=
  let t := (hbar ^ 2 / (2 * params.effectiveMass * spacing ^ 2) : ℝ)
  let λ := (hbar * params.rashbaVelocity / (2 * spacing) : ℝ)
  (-(t : ℂ)) • (1 : InternalSpace.PauliMatrix) +
    if direction = 0 then
      (-(Complex.I * (λ : ℂ))) • InternalSpace.pauliY
    else (Complex.I * (λ : ℂ)) • InternalSpace.pauliX

/-- Forward part of the amplitude table, including half of the onsite term.
Using natural-coordinate adjacency imposes open boundaries. -/
def realSpaceRashbaForwardAmplitude {nx ny : ℕ}
    (params : HamiltonianParameters) (hbar spacing : ℝ)
    (x y : SpinfulSite (RectangularSite nx ny)) : ℂ :=
  let rx := rectangularCoordinates (ofLex x).1
  let ry := rectangularCoordinates (ofLex y).1
  let a := (ofLex x).2
  let b := (ofLex y).2
  if rx = ry then
    (((hbar ^ 2 / (params.effectiveMass * spacing ^ 2) : ℝ) : ℂ) •
      (1 : InternalSpace.PauliMatrix) +
      (((params.exchangeSplitting / 2 : ℝ) : ℂ)) • InternalSpace.pauliZ) a b
  else if rx.1 = ry.1 + 1 ∧ rx.2 = ry.2 then
    realSpaceRashbaForwardBlock params hbar spacing 0 a b
  else if rx.1 = ry.1 ∧ rx.2 = ry.2 + 1 then
    realSpaceRashbaForwardBlock params hbar spacing 1 a b
  else 0

/-- The full Hermitian hopping table is the forward table plus its adjoint. -/
def realSpaceRashbaAmplitude {nx ny : ℕ}
    (params : HamiltonianParameters) (hbar spacing : ℝ)
    (x y : SpinfulSite (RectangularSite nx ny)) : ℂ :=
  realSpaceRashbaForwardAmplitude params hbar spacing x y +
    star (realSpaceRashbaForwardAmplitude params hbar spacing y x)

/-- The full amplitude table is Hermitian by construction. -/
theorem star_realSpaceRashbaAmplitude {nx ny : ℕ}
    (params : HamiltonianParameters) (hbar spacing : ℝ)
    (x y : SpinfulSite (RectangularSite nx ny)) :
    star (realSpaceRashbaAmplitude params hbar spacing x y) =
      realSpaceRashbaAmplitude params hbar spacing y x := by
  simp only [realSpaceRashbaAmplitude, star_add, star_star, add_comm]

/-- The existing hopping abstraction with actual finite incident support. -/
noncomputable def realSpaceRashbaHopping (nx ny : ℕ)
    (params : HamiltonianParameters) (hbar spacing : ℝ) :
    LocallyFiniteHopping (SpinfulSite (RectangularSite nx ny)) :=
  LocallyFiniteHopping.ofFiniteAmplitudes (realSpaceRashbaAmplitude params hbar spacing)

/-- The actual finite Rashba hopping amplitudes satisfy the existing Hermiticity contract. -/
theorem realSpaceRashbaHopping_hasHermitianAmplitudes (nx ny : ℕ)
    (params : HamiltonianParameters) (hbar spacing : ℝ) :
    (realSpaceRashbaHopping nx ny params hbar spacing).HasHermitianAmplitudes := by
  intro x y
  simpa only [realSpaceRashbaHopping, LocallyFiniteHopping.ofFiniteAmplitudes_amplitude]
    using star_realSpaceRashbaAmplitude params hbar spacing x y

/-- The full finite Fock Hamiltonian of the real-space model is self-adjoint. -/
theorem realSpaceRashbaHamiltonian_isSelfAdjoint (nx ny : ℕ)
    (params : HamiltonianParameters) (hbar spacing : ℝ) :
    IsSelfAdjoint (boundedHoppingHamiltonian (realSpaceRashbaHopping nx ny params hbar spacing)) :=
  isSelfAdjoint_boundedHoppingHamiltonian _
    (realSpaceRashbaHopping_hasHermitianAmplitudes nx ny params hbar spacing)

end
end QuantumTheory.Models.RashbaExchange
