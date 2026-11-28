import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Uniqueness of finite increasing enumerations
-/

/-- Increasing maps from the same finite index type coincide if the second map's
range is contained in the first map's range. -/
theorem StrictMono.eq_of_fin_range_subset {α : Type*} [LinearOrder α]
    {n : ℕ} {f g : Fin n → α} (hf : StrictMono f) (hg : StrictMono g)
    (h : ∀ i, ∃ j, f j = g i) : f = g := by
  classical
  let s := Finset.univ.image f
  have hs : s.card = n := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hf.injective]
    simp
  exact (Finset.orderEmbOfFin_unique hs
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) hf).trans
    (Finset.orderEmbOfFin_unique hs (fun i => by
      obtain ⟨j, hj⟩ := h i
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩) hg).symm
