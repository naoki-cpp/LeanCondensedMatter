import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.Algebra.DiagonalTrace

set_option linter.style.header false

/-!
# The KMS-type trace rotation, combining trace cyclicity and the KMS-type relation

The common Bloch–de Dominicis induction uses trace cyclicity together with the KMS-type relation to
move a ladder operator from the end of an operator product to its front while picking up an
eigenvalue-dependent weight. This file packages that statistics-independent step by combining
`Common.tsumTrace_comp_comm` with
`Common.diagonalEvolution_comp_eq_smul_comp_diagonalEvolution`:

`Tr[e^{-βH₀} (A C)] = e^{qβ} Tr[e^{-βH₀} (C A)]`.

This matches the physics reference notes' derivation (`quantum-statistical-mechanics.tex`, the
`⟨Ĉ₂⋯Ĉ_{2n}Ĉ₁⟩ = w₁⟨Ĉ₁Ĉ₂⋯Ĉ_{2n}⟩` step inside the Bloch–de Dominicis theorem's proof): `A` plays
the role of `Ĉ₂⋯Ĉ_{2n}`, `C` plays the role of `Ĉ₁`, and `w₁ = e^{qβ}` is `C`'s eigenvalue-shift
weight (`q = -εᵢ` for `annihilate i`, `q = εᵢ` for `create i`).

The configuration-general `tsumTrace_diagonalEvolution_comp_rotate` theorem takes the necessary
double-series summability condition explicitly. In finite configurations it is automatic. The
trace peel identity combining this rotation with scalar exchange lives in
`Common/Thermal/BlochDeDominicis/Unnormalized/PeelFirstTrace.lean`.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- The KMS-type trace rotation on any configuration type, obtained from
`Common.tsumTrace_comp_comm`. The double-series summability hypothesis `h` is explicit; finite
configuration spaces discharge it automatically, while infinite bosonic occupation spaces require
analytic estimates. -/
theorem tsumTrace_diagonalEvolution_comp_rotate
    (energy : Config → ℝ) (β q : ℝ) (A C : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC : heisenbergEvolve energy (-β) C = Complex.exp ((q * (-β) : ℝ) : ℂ) • C)
    (h : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp A) n k * matrixCoeff C k n))) :
    tsumTrace ((diagonalEvolution energy (-β)).comp (A.comp C)) =
      Complex.exp ((q * β : ℝ) : ℂ) •
        tsumTrace ((diagonalEvolution energy (-β)).comp (C.comp A)) := by
  have hKMS := diagonalEvolution_comp_eq_smul_comp_diagonalEvolution energy (-β) q C hC
  have hKMS' : C.comp (diagonalEvolution energy (-β)) =
      Complex.exp ((q * β : ℝ) : ℂ) • ((diagonalEvolution energy (-β)).comp C) := by
    rw [show ((q * β : ℝ) : ℂ) = -((q * -β : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_neg]
    exact (eq_inv_smul_iff₀ (Complex.exp_ne_zero _)).2 hKMS.symm
  rw [← LinearMap.comp_assoc, tsumTrace_comp_comm _ _ h,
    ← LinearMap.comp_assoc, hKMS', LinearMap.smul_comp,
    tsumTrace_smul, LinearMap.comp_assoc, smul_eq_mul]

end Common
end SecondQuantization
