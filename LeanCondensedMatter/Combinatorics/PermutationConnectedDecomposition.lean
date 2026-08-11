import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition
import LeanCondensedMatter.Combinatorics.PermutationOrbitPartition
import Mathlib.GroupTheory.Perm.Cycle.Factors

set_option linter.style.header false

/-!
# Connected decomposition of finite permutations

A permutation supported on a finite set decomposes uniquely into its orbit partition and one
single-orbit permutation on every block. This file is deliberately independent of exchange
weights: the decomposition is the structural input used later for arbitrary-`ζ` multiplicative
weights.

Only `permutationConnectedDecomposition` is public. Support wrappers, block restrictions,
assembly, and round-trip lemmas are implementation details.
-/

namespace Combinatorics

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

private abbrev SupportedPerm (S : Finset α) :=
  {σ : Equiv.Perm α // σ.support ⊆ S}

private abbrev SingleOrbitPerm (S : Finset α) :=
  {σ : Equiv.Perm S // σ.IsCycleOn Set.univ}

/-- The `SameCycle` partition restricted to a finite support set. -/
private noncomputable def orbitFinpartitionOn (S : Finset α) (σ : Equiv.Perm α) : Finpartition S := by
  classical
  exact Finpartition.ofSetSetoid (Equiv.Perm.SameCycle.setoid σ) S

omit [Fintype α] in
private theorem mem_part_orbitFinpartitionOn_iff (S : Finset α) (σ : Equiv.Perm α)
    (a b : α) :
    b ∈ (orbitFinpartitionOn S σ).part a ↔
      a ∈ S ∧ b ∈ S ∧ σ.SameCycle a b := by
  classical
  change b ∈ (Finpartition.ofSetSetoid (Equiv.Perm.SameCycle.setoid σ) S).part a ↔
    a ∈ S ∧ b ∈ S ∧ (Equiv.Perm.SameCycle.setoid σ) a b
  exact Finpartition.mem_part_ofSetSetoid_iff_rel S

private theorem SupportedPerm.apply_mem {S : Finset α} (σ : SupportedPerm S)
    {x : α} (hx : x ∈ S) : σ.1 x ∈ S := by
  by_cases hfix : σ.1 x = x
  · simpa [hfix] using hx
  · have hxSupp : x ∈ σ.1.support := Equiv.Perm.mem_support.mpr hfix
    have hσxSupp : σ.1 x ∈ σ.1.support := by simpa using hxSupp
    exact σ.2 hσxSupp

private theorem SupportedPerm.apply_eq_self_of_not_mem {S : Finset α} (σ : SupportedPerm S)
    {x : α} (hx : x ∉ S) : σ.1 x = x := by
  by_contra h
  exact hx (σ.2 (Equiv.Perm.mem_support.mpr h))

private theorem apply_mem_orbitBlock {S : Finset α} (σ : SupportedPerm S)
    (B : (orbitFinpartitionOn S σ.1).parts) {_x : α} (hx : _x ∈ B.1) :
    σ.1 _x ∈ B.1 := by
  let π := orbitFinpartitionOn S σ.1
  have hxS : _x ∈ S := π.subset B.2 hx
  have hσxS : σ.1 _x ∈ S := σ.apply_mem hxS
  have hpart : π.part _x = B.1 := π.part_eq_of_mem B.2 hx
  rw [← hpart]
  exact (mem_part_orbitFinpartitionOn_iff S σ.1 _x (σ.1 _x)).2
    ⟨hxS, hσxS, ⟨1, by simp⟩⟩

private noncomputable def restrictOrbitBlock {S : Finset α} (σ : SupportedPerm S)
    (B : (orbitFinpartitionOn S σ.1).parts) : Equiv.Perm B.1 :=
  Equiv.Perm.subtypePermOfFintype σ.1 (fun _ hx => apply_mem_orbitBlock σ B hx)

@[simp]
private theorem restrictOrbitBlock_apply {S : Finset α} (σ : SupportedPerm S)
    (B : (orbitFinpartitionOn S σ.1).parts) (_x : B.1) :
    ((restrictOrbitBlock σ B _x : B.1) : α) = σ.1 _x :=
  rfl

private theorem restrictOrbitBlock_isCycleOn {S : Finset α} (σ : SupportedPerm S)
    (B : (orbitFinpartitionOn S σ.1).parts) :
    (restrictOrbitBlock σ B).IsCycleOn Set.univ := by
  constructor
  · exact (restrictOrbitBlock σ B).bijOn (fun _ => by simp)
  · intro x _ y _
    have hpart : (orbitFinpartitionOn S σ.1).part (x : α) = B.1 :=
      (orbitFinpartitionOn S σ.1).part_eq_of_mem B.2 x.2
    have hyPart : (y : α) ∈ (orbitFinpartitionOn S σ.1).part (x : α) := by
      simpa [hpart] using y.2
    have hsame : σ.1.SameCycle (x : α) (y : α) :=
      (mem_part_orbitFinpartitionOn_iff S σ.1 x y).1 hyPart |>.2.2
    simpa [restrictOrbitBlock, Equiv.Perm.subtypePermOfFintype] using hsame

private noncomputable def decomposePermutation (S : Finset α) (σ : SupportedPerm S) :
    Σ π : Finpartition S, ∀ B : π.parts, SingleOrbitPerm B.1 :=
  ⟨orbitFinpartitionOn S σ.1,
    fun B => ⟨restrictOrbitBlock σ B, restrictOrbitBlock_isCycleOn σ B⟩⟩

private noncomputable def assembleSubtypePermutation {S : Finset α} (π : Finpartition S)
    (c : ∀ B : π.parts, SingleOrbitPerm B.1) : Equiv.Perm S :=
  π.equivSigmaParts.symm.permCongr
    (Equiv.Perm.sigmaCongrRight fun B => (c B).1)

private noncomputable def assemblePermutation {S : Finset α} (π : Finpartition S)
    (c : ∀ B : π.parts, SingleOrbitPerm B.1) : SupportedPerm S := by
  let τS := assembleSubtypePermutation π c
  refine ⟨τS.extendDomain (Equiv.refl S), ?_⟩
  intro x hx
  by_contra hxS
  have hfix : τS.extendDomain (Equiv.refl S) x = x :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hxS
  exact (Equiv.Perm.mem_support.mp hx) hfix

omit [DecidableEq α] [Fintype α] in
private theorem sameCycle_permCongr_iff {β : Type*} (e : α ≃ β) (σ : Equiv.Perm α)
    (x y : α) :
    (e.permCongr σ).SameCycle (e x) (e y) ↔ σ.SameCycle x y := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hpow : e.permCongr (σ ^ z) = (e.permCongr σ) ^ z := by
      simpa using map_zpow e.permCongrHom σ z
    have hz' := hz
    rw [← hpow] at hz'
    exact e.injective (by simpa [Equiv.permCongr_apply] using hz')
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hpow : e.permCongr (σ ^ z) = (e.permCongr σ) ^ z := by
      simpa using map_zpow e.permCongrHom σ z
    rw [← hpow]
    simpa [Equiv.permCongr_apply, hz]

private theorem sigmaCongrRight_zpow_fst {ι : Type*} {β : ι → Type*}
    (c : ∀ i, Equiv.Perm (β i)) (z : ℤ) (x : Σ i, β i) :
    (((Equiv.Perm.sigmaCongrRight c) ^ z) x).1 = x.1 := by
  have hpow :
      Equiv.Perm.sigmaCongrRight (c ^ z) = (Equiv.Perm.sigmaCongrRight c) ^ z := by
    simpa using map_zpow (Equiv.Perm.sigmaCongrRightHom β) c z
  rw [← hpow]
  rfl

private theorem sameCycle_sigmaCongrRight_iff_fst_eq {ι : Type*} {β : ι → Type*}
    (c : ∀ i, {σ : Equiv.Perm (β i) // σ.IsCycleOn Set.univ})
    (x y : Σ i, β i) :
    (Equiv.Perm.sigmaCongrRight (fun i => (c i).1)).SameCycle x y ↔ x.1 = y.1 := by
  constructor
  · rintro ⟨z, hz⟩
    calc
      x.1 = (((Equiv.Perm.sigmaCongrRight (fun i => (c i).1)) ^ z) x).1 :=
        (sigmaCongrRight_zpow_fst (fun i => (c i).1) z x).symm
      _ = y.1 := congrArg Sigma.fst hz
  · rcases x with ⟨i, x⟩
    rcases y with ⟨j, y⟩
    intro hij
    cases hij
    have hsame : (c i).1.SameCycle x y := (c i).2.2 (by simp) (by simp)
    rcases hsame with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hpow :
        Equiv.Perm.sigmaCongrRight ((fun i => (c i).1) ^ z) =
          (Equiv.Perm.sigmaCongrRight fun i => (c i).1) ^ z := by
      simpa using map_zpow (Equiv.Perm.sigmaCongrRightHom β) (fun i => (c i).1) z
    rw [← hpow]
    change (⟨i, ((c i).1 ^ z) x⟩ : Σ i, β i) = ⟨i, y⟩
    simpa [hz]

omit [Fintype α] in
private theorem assembleSubtype_sameCycle_iff {S : Finset α} (π : Finpartition S)
    (c : ∀ B : π.parts, SingleOrbitPerm B.1) (x y : S) :
    (assembleSubtypePermutation π c).SameCycle x y ↔
      π.part x.1 = π.part y.1 := by
  let e := π.equivSigmaParts
  have hcongr := sameCycle_permCongr_iff e.symm
    (Equiv.Perm.sigmaCongrRight fun B => (c B).1) (e x) (e y)
  have hsigma := sameCycle_sigmaCongrRight_iff_fst_eq c (e x) (e y)
  simpa [assembleSubtypePermutation, e, Finpartition.equivSigmaParts] using hcongr.trans hsigma

private theorem assemble_sameCycle_iff {S : Finset α} (π : Finpartition S)
    (c : ∀ B : π.parts, SingleOrbitPerm B.1) {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) :
    (assemblePermutation π c).1.SameCycle x y ↔ π.part x = π.part y := by
  let xs : S := ⟨x, hx⟩
  let ys : S := ⟨y, hy⟩
  have hext := Equiv.Perm.sameCycle_extendDomain
    (g := assembleSubtypePermutation π c) (f := Equiv.refl S) (x := xs) (y := ys)
  simpa [assemblePermutation, xs, ys] using
    hext.trans (assembleSubtype_sameCycle_iff π c xs ys)

private theorem assemble_part_eq {S : Finset α} (π : Finpartition S)
    (c : ∀ B : π.parts, SingleOrbitPerm B.1) {x : α} (hx : x ∈ S) :
    (orbitFinpartitionOn S (assemblePermutation π c).1).part x = π.part x := by
  ext y
  rw [mem_part_orbitFinpartitionOn_iff]
  constructor
  · rintro ⟨_, hy, hxy⟩
    have hp := (assemble_sameCycle_iff π c hx hy).1 hxy
    have hymem : y ∈ π.part y := π.mem_part hy
    rwa [← hp] at hymem
  · intro hyPart
    have hy : y ∈ S := π.part_subset x hyPart
    refine ⟨hx, hy, (assemble_sameCycle_iff π c hx hy).2 ?_⟩
    exact (π.part_eq_of_mem (π.part_mem.2 hx) hyPart).symm

private theorem orbitFinpartitionOn_assemble {S : Finset α} (π : Finpartition S)
    (c : ∀ B : π.parts, SingleOrbitPerm B.1) :
    orbitFinpartitionOn S (assemblePermutation π c).1 = π := by
  let P := orbitFinpartitionOn S (assemblePermutation π c).1
  apply Finpartition.ext
  apply Finset.ext
  intro B
  constructor
  · intro hB
    obtain ⟨x, hxB⟩ := P.nonempty_of_mem_parts hB
    have hx : x ∈ S := P.subset hB hxB
    have hPB : P.part x = B := P.part_eq_of_mem hB hxB
    have hp := assemble_part_eq π c hx
    have hEq : B = π.part x := by rw [← hp, hPB]
    rw [hEq]
    exact π.part_mem.2 hx
  · intro hB
    obtain ⟨x, hxB⟩ := π.nonempty_of_mem_parts hB
    have hx : x ∈ S := π.subset hB hxB
    have hπB : π.part x = B := π.part_eq_of_mem hB hxB
    have hp := assemble_part_eq π c hx
    have hEq : B = P.part x := by rw [← hπB, ← hp]
    rw [hEq]
    exact P.part_mem.2 hx

private theorem assemblePermutation_apply_mem {S : Finset α} (π : Finpartition S)
    (c : ∀ B : π.parts, SingleOrbitPerm B.1) {x : α} (hx : x ∈ S) :
    (assemblePermutation π c).1 x =
      ((c ⟨π.part x, π.part_mem.2 hx⟩).1
        ⟨x, π.mem_part hx⟩ : α) := by
  change (assembleSubtypePermutation π c).extendDomain (Equiv.refl S) x = _
  rw [Equiv.Perm.extendDomain_apply_subtype _ _ hx]
  rfl

private theorem assemble_decompose {S : Finset α} (σ : SupportedPerm S) :
    assemblePermutation (decomposePermutation S σ).1 (decomposePermutation S σ).2 = σ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ S
  · rw [assemblePermutation_apply_mem _ _ hx]
    rfl
  · rw [SupportedPerm.apply_eq_self_of_not_mem σ hx]
    simp [assemblePermutation, Equiv.Perm.extendDomain_apply_not_subtype, hx]

private theorem decompose_assemble {S : Finset α} (π : Finpartition S)
    (c : ∀ B : π.parts, SingleOrbitPerm B.1) :
    decomposePermutation S (assemblePermutation π c) = ⟨π, c⟩ := by
  let P := orbitFinpartitionOn S (assemblePermutation π c).1
  have hπ : P = π := orbitFinpartitionOn_assemble π c
  unfold decomposePermutation
  apply Sigma.ext hπ
  have hparts : (P.parts : Type _) = (π.parts : Type _) :=
    congrArg (fun q : Finpartition S => (q.parts : Type _)) hπ
  apply Function.hfunext hparts
  intro B B' hBB
  have hBval : B.1 = B'.1 := by
    exact dcongr_heq
      (f₁ := fun B : P.parts => (B : Finset α))
      (f₂ := fun B : π.parts => (B : Finset α))
      hBB
      (fun _ _ _ => rfl)
      (by
        intro hdom _
        cases hdom
        rfl)
  cases hBval
  rw [heq_iff_eq]
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change (assemblePermutation π c).1 x = (c B').1 x
  have hxS : (x : α) ∈ S := π.subset B'.2 x.2
  rw [assemblePermutation_apply_mem π c hxS]
  have hpart : ⟨π.part (x : α), π.part_mem.2 hxS⟩ = B' :=
    Subtype.ext (π.part_eq_of_mem B'.2 x.2)
  cases hpart
  rfl

/-- The canonical connected decomposition of finite permutations by their orbit blocks.

Objects on `S` are ambient permutations supported in `S`; connected objects on a block are
permutations of that block with one orbit (with the identity allowed on singleton blocks, as in
Mathlib's `IsCycleOn`). -/
noncomputable def permutationConnectedDecomposition (α : Type*) [DecidableEq α] [Fintype α] :
    ConnectedDecomposition α where
  Object := SupportedPerm
  ConnectedObject := SingleOrbitPerm
  fintypeObject := fun _ => Fintype.ofFinite _
  fintypeConnectedObject := fun _ => Fintype.ofFinite _
  decompose := fun S =>
    { toFun := decomposePermutation S
      invFun := fun x => assemblePermutation x.1 x.2
      left_inv := assemble_decompose
      right_inv := fun x => decompose_assemble x.1 x.2 }

end Combinatorics
