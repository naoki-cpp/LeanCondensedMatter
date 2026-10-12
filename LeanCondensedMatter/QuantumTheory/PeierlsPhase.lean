import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.style.header false

/-!
# Statistics-independent Peierls link phases

The forward and reverse complex Peierls phases and their zero-source derivatives depend only on
the coupling parameters, not on fermionic/bosonic occupation or a chosen lattice representation.
The corresponding one-particle link Hamiltonians live in `QuantumTheory.PeierlsLattice`,
with their second-quantized realizations downstream.
-/

namespace QuantumTheory
namespace PeierlsPhase

/-- The coefficient `i q / ℏ` fixed by the charge and phase convention. -/
noncomputable def peierlsCoupling (ℏ q : ℂ) : ℂ :=
  (Complex.I * q) / ℏ

/-- Peierls phase on the oriented hopping term `h_xy |x><y|`. -/
noncomputable def peierlsForwardPhase (ℏ q A : ℂ) : ℂ :=
  Complex.exp (-(peierlsCoupling ℏ q) * A)

/-- Peierls phase on the oppositely oriented hopping term `h_yx |y><x|`. -/
noncomputable def peierlsReversePhase (ℏ q A : ℂ) : ℂ :=
  Complex.exp (peierlsCoupling ℏ q * A)

@[simp]
theorem peierlsForwardPhase_zero (ℏ q : ℂ) :
    peierlsForwardPhase ℏ q 0 = 1 := by
  simp [peierlsForwardPhase]

@[simp]
theorem peierlsReversePhase_zero (ℏ q : ℂ) :
    peierlsReversePhase ℏ q 0 = 1 := by
  simp [peierlsReversePhase]

private theorem hasDerivAt_exp_const_mul_zero (c : ℂ) :
    HasDerivAt (fun A : ℂ => Complex.exp (c * A)) c 0 := by
  simpa using (hasDerivAt_const_mul (x := (0 : ℂ)) c).cexp

/-- The forward Peierls phase has derivative `-i q / ℏ` at zero. -/
theorem hasDerivAt_peierlsForwardPhase_zero (ℏ q : ℂ) :
    HasDerivAt (peierlsForwardPhase ℏ q) (-(peierlsCoupling ℏ q)) 0 := by
  change HasDerivAt
    (fun A : ℂ => Complex.exp (-(peierlsCoupling ℏ q) * A))
    (-(peierlsCoupling ℏ q)) 0
  exact hasDerivAt_exp_const_mul_zero (-(peierlsCoupling ℏ q))

/-- The reverse Peierls phase has derivative `i q / ℏ` at zero. -/
theorem hasDerivAt_peierlsReversePhase_zero (ℏ q : ℂ) :
    HasDerivAt (peierlsReversePhase ℏ q) (peierlsCoupling ℏ q) 0 := by
  change HasDerivAt
    (fun A : ℂ => Complex.exp (peierlsCoupling ℏ q * A))
    (peierlsCoupling ℏ q) 0
  exact hasDerivAt_exp_const_mul_zero (peierlsCoupling ℏ q)

end PeierlsPhase
end QuantumTheory
