import LeanCondensedMatter.Combinatorics.SetPartition.Coarsening
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

/-- The Möbius function from a partition to the top depends only on its block set. -/
theorem mu_to_top_eq_mu_bot_top_parts {R : Type*} [CommRing R] (π : Finpartition a) :
    mu R π ⊤ = mu R (⊥ : Finpartition π.parts) ⊤ := by
  classical
  let e := coarseningsOrderIsoBlockPartitions π
  let x : {σ : Finpartition a // π ≤ σ} := ⟨π, le_rfl⟩
  let y : {σ : Finpartition a // π ≤ σ} := ⟨⊤, le_top⟩
  have hex : e x = (⊥ : Finpartition π.parts) := by
    apply le_antisymm
    · have hxy : x ≤ e.symm (⊥ : Finpartition π.parts) := (e.symm ⊥).2
      simpa using e.monotone hxy
    · exact bot_le
  have hey : e y = (⊤ : Finpartition π.parts) := by
    apply le_antisymm
    · exact le_top
    · have hxy : e.symm (⊤ : Finpartition π.parts) ≤ y := by
        change (e.symm (⊤ : Finpartition π.parts)).1 ≤ (⊤ : Finpartition a)
        exact le_top
      simpa using e.monotone hxy
  have hiso := IncidenceAlgebra.mu_orderIso_apply (R := R) e x y
  have hambient := IncidenceAlgebra.mu_subtype_ge_apply (R := R) x y
  rw [hex, hey] at hiso
  exact (hiso.trans hambient).symm


end Finpartition
