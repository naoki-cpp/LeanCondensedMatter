import LeanCondensedMatter.Combinatorics.SetPartition.Refinement
import LeanCondensedMatter.Combinatorics.IncidenceAlgebra.Mobius
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

set_option linter.style.header false

/-!
# Möbius factorization on the partition lattice

The Möbius function of an interval in the finite set-partition lattice factors over the blocks of
the coarser partition. The coefficient ring is arbitrary.
-/

open IncidenceAlgebra

variable {α : Type*} [DecidableEq α]

namespace Finpartition

variable {a : Finset α}

/-- The partition-lattice Möbius function factors over the blocks of the coarser partition. -/
theorem mu_eq_prod_restrict {R : Type*} [CommRing R]
    {π σ : Finpartition a} (h : π ≤ σ) :
    mu R π σ = ∏ B : σ.parts, mu R (π.restrict (σ.le B.2))
      (⊤ : Finpartition (B : Finset α)) := by
  classical
  have hstep1 : mu R π σ =
      mu R (⟨π, h⟩ : {τ : Finpartition a // τ ≤ σ}) ⟨σ, le_refl σ⟩ :=
    (mu_subtype_le_apply (R := R)
      (⟨π, h⟩ : {τ : Finpartition a // τ ≤ σ}) ⟨σ, le_refl σ⟩).symm
  have hstep2 :
      mu R (⟨π, h⟩ : {τ : Finpartition a // τ ≤ σ}) ⟨σ, le_refl σ⟩ =
        mu R (refinementsOrderIsoFiberPartitions σ ⟨π, h⟩)
          (refinementsOrderIsoFiberPartitions σ ⟨σ, le_refl σ⟩) :=
    (mu_orderIso_apply (R := R) _ _ _).symm
  have hstep3 := mu_pi_finset_apply (R := R)
    (fun B : Finset α => Finpartition B) σ.parts
    (refinementsOrderIsoFiberPartitions σ ⟨π, h⟩)
    (refinementsOrderIsoFiberPartitions σ ⟨σ, le_refl σ⟩)
  rw [hstep1, hstep2, hstep3]
  refine Finset.prod_congr rfl fun B _ => ?_
  change mu R (π.restrict (σ.le B.2)) (σ.restrict (σ.le B.2)) =
    mu R (π.restrict (σ.le B.2)) ⊤
  rw [restrict_self_part_eq_top σ B.2]

end Finpartition
