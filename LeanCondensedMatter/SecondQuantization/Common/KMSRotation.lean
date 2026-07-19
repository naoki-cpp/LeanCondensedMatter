import LeanCondensedMatter.SecondQuantization.Common.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# The KMS-type trace rotation, combining trace cyclicity and the KMS-type relation

Phase 9, step 4 of Track D's finite-mode fermionic primary line
(`notes/roadmaps/second-quantization.md`), step 3 of the plan (discussed with the user) toward a
common `Common/`-level Bloch–de Dominicis induction interface usable by both statistics: combines
`Common.traceFock_comp_comm`/`Common.tsumTrace_comp_comm` (trace cyclicity, finite and `tsum`) with
`Common.diagonalEvolution_comp_eq_smul_comp_diagonalEvolution` (the KMS-type relation) into the
single identity the theorem's induction actually uses to move a ladder operator from the end of an
operator product to its front, picking up an eigenvalue-dependent weight:

`Tr[e^{-βH₀} (A C)] = e^{qβ} Tr[e^{-βH₀} (C A)]`

matching the physics reference notes' derivation (`quantum-statistical-mechanics.tex`, the
`⟨Ĉ₂⋯Ĉ_{2n}Ĉ₁⟩ = w₁⟨Ĉ₁Ĉ₂⋯Ĉ_{2n}⟩` step inside the Bloch–de Dominicis theorem's proof) exactly:
`A` plays the role of `Ĉ₂⋯Ĉ_{2n}`, `C` plays the role of `Ĉ₁`, and `w₁ = e^{qβ}` is `C`'s
eigenvalue-shift weight (`q = -εᵢ` for `annihilate i`, `q = εᵢ` for `create i`).

Both a `[Fintype Config]` version (`traceFock_diagonalEvolution_comp_rotate`) and a `tsum`,
summability-hypothesis-gated version usable on an infinite `Config`
(`tsumTrace_diagonalEvolution_comp_rotate`) are proved below, the latter built from
`Common.tsumTrace_comp_comm` in place of `traceFock_comp_comm`. This rotation identity is reusable
infrastructure beyond Bloch–de Dominicis; the theorem that specifically packages it into the
Bloch–de Dominicis 2-point base case lives in `Common/BlochDeDominicis/TwoPoint.lean`.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **`C e^{τH₀} = e^{-qτ} e^{τH₀} C`**, the KMS-type relation with `C` on the left — the algebraic
rearrangement of `diagonalEvolution_comp_eq_smul_comp_diagonalEvolution` needed by the rotation
theorems below, obtained by multiplying both sides of that lemma by the (nonzero) reciprocal
exponential factor. Config-general — no `[Fintype Config]` needed. -/
theorem comp_diagonalEvolution_eq_smul_diagonalEvolution_comp
    (energy : Config → ℝ) (τ q : ℝ) (C : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC : heisenbergEvolve energy τ C = Complex.exp ((q * τ : ℝ) : ℂ) • C) :
    C.comp (diagonalEvolution energy τ) =
      Complex.exp ((-(q * τ) : ℝ) : ℂ) • ((diagonalEvolution energy τ).comp C) := by
  have hKMS := diagonalEvolution_comp_eq_smul_comp_diagonalEvolution energy τ q C hC
  have h2 := congrArg (fun x => Complex.exp ((-(q * τ) : ℝ) : ℂ) • x) hKMS
  simp only [smul_smul] at h2
  rw [show Complex.exp ((-(q * τ) : ℝ) : ℂ) * Complex.exp ((q * τ : ℝ) : ℂ) = 1 by
    rw [← Complex.exp_add, ← Complex.ofReal_add]; norm_num, one_smul] at h2
  exact h2.symm

/-- **The KMS-type trace rotation**: `Tr[e^{-βH₀} (A C)] = e^{qβ} Tr[e^{-βH₀} (C A)]`, for any
operator `A` and any operator `C` with eigenvalue-shift `q` under `heisenbergEvolve`. Combines
`traceFock_comp_comm` (cyclicity) with `comp_diagonalEvolution_eq_smul_diagonalEvolution_comp` (the
KMS-type relation) exactly as the physics reference notes' `⟨Ĉ₂⋯Ĉ_{2n}Ĉ₁⟩ = w₁⟨Ĉ₁Ĉ₂⋯Ĉ_{2n}⟩` step
does. -/
theorem traceFock_diagonalEvolution_comp_rotate [Fintype Config]
    (energy : Config → ℝ) (β q : ℝ) (A C : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC : heisenbergEvolve energy (-β) C = Complex.exp ((q * (-β) : ℝ) : ℂ) • C) :
    traceFock ((diagonalEvolution energy (-β)).comp (A.comp C)) =
      Complex.exp ((q * β : ℝ) : ℂ) •
        traceFock ((diagonalEvolution energy (-β)).comp (C.comp A)) := by
  have hKMS' := comp_diagonalEvolution_eq_smul_diagonalEvolution_comp energy (-β) q C hC
  rw [show ((-(q * -β) : ℝ) : ℂ) = ((q * β : ℝ) : ℂ) by push_cast; ring] at hKMS'
  calc traceFock ((diagonalEvolution energy (-β)).comp (A.comp C))
      = traceFock (((diagonalEvolution energy (-β)).comp A).comp C) := by
        rw [LinearMap.comp_assoc]
    _ = traceFock (C.comp ((diagonalEvolution energy (-β)).comp A)) := traceFock_comp_comm _ _
    _ = traceFock ((C.comp (diagonalEvolution energy (-β))).comp A) := by
        rw [LinearMap.comp_assoc]
    _ = traceFock ((Complex.exp ((q * β : ℝ) : ℂ) •
          ((diagonalEvolution energy (-β)).comp C)).comp A) := by rw [hKMS']
    _ = traceFock (Complex.exp ((q * β : ℝ) : ℂ) •
          (((diagonalEvolution energy (-β)).comp C).comp A)) := by rw [LinearMap.smul_comp]
    _ = Complex.exp ((q * β : ℝ) : ℂ) •
          traceFock (((diagonalEvolution energy (-β)).comp C).comp A) := by
        rw [traceFock_smul, smul_eq_mul]
    _ = Complex.exp ((q * β : ℝ) : ℂ) •
          traceFock ((diagonalEvolution energy (-β)).comp (C.comp A)) := by
        rw [LinearMap.comp_assoc]

/-- **The `tsum` KMS-type trace rotation**: the `[Fintype Config]`-free analogue of
`traceFock_diagonalEvolution_comp_rotate`, built from `Common.tsumTrace_comp_comm` instead of
`traceFock_comp_comm`. This is the piece that lets the rotation step — hence, eventually, the
2-point base case and the general induction — reach a genuine bosonic occupation type, at the cost
of the explicit double-summability hypothesis `h` (unlike the `[Fintype Config]` case, where it is
automatic). -/
theorem tsumTrace_diagonalEvolution_comp_rotate
    (energy : Config → ℝ) (β q : ℝ) (A C : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC : heisenbergEvolve energy (-β) C = Complex.exp ((q * (-β) : ℝ) : ℂ) • C)
    (h : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp A) n k * matrixCoeff C k n))) :
    tsumTrace ((diagonalEvolution energy (-β)).comp (A.comp C)) =
      Complex.exp ((q * β : ℝ) : ℂ) •
        tsumTrace ((diagonalEvolution energy (-β)).comp (C.comp A)) := by
  have hKMS' := comp_diagonalEvolution_eq_smul_diagonalEvolution_comp energy (-β) q C hC
  rw [show ((-(q * -β) : ℝ) : ℂ) = ((q * β : ℝ) : ℂ) by push_cast; ring] at hKMS'
  calc tsumTrace ((diagonalEvolution energy (-β)).comp (A.comp C))
      = tsumTrace (((diagonalEvolution energy (-β)).comp A).comp C) := by
        rw [LinearMap.comp_assoc]
    _ = tsumTrace (C.comp ((diagonalEvolution energy (-β)).comp A)) := tsumTrace_comp_comm _ _ h
    _ = tsumTrace ((C.comp (diagonalEvolution energy (-β))).comp A) := by
        rw [LinearMap.comp_assoc]
    _ = tsumTrace ((Complex.exp ((q * β : ℝ) : ℂ) •
          ((diagonalEvolution energy (-β)).comp C)).comp A) := by rw [hKMS']
    _ = tsumTrace (Complex.exp ((q * β : ℝ) : ℂ) •
          (((diagonalEvolution energy (-β)).comp C).comp A)) := by rw [LinearMap.smul_comp]
    _ = Complex.exp ((q * β : ℝ) : ℂ) •
          tsumTrace (((diagonalEvolution energy (-β)).comp C).comp A) := by
        rw [tsumTrace_smul, smul_eq_mul]
    _ = Complex.exp ((q * β : ℝ) : ℂ) •
          tsumTrace ((diagonalEvolution energy (-β)).comp (C.comp A)) := by
        rw [LinearMap.comp_assoc]

end Common
end SecondQuantization
