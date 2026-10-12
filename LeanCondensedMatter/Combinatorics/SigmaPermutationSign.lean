import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Perm.Sign

set_option linter.style.header false

/-!
# Permutation signs on dependent disjoint unions

A family of permutations on the fibers of a dependent sum acts on the total space through
`Equiv.sigmaCongrRight`. Its sign is the product of the fiberwise signs, generalizing the
homogeneous `Equiv.Perm.sign_prodCongrRight` theorem.
-/

namespace Equiv.Perm

private noncomputable def sigmaFiberEquiv
    {ι : Type*} {β : ι → Type*} (i : ι) :
    β i ≃ {x : Σ j, β j // x.1 = i} where
  toFun x := ⟨⟨i, x⟩, rfl⟩
  invFun x := by
    rcases x with ⟨⟨j, x⟩, h⟩
    have hji : j = i := h
    subst j
    exact x
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨j, x⟩, h⟩
    have hji : j = i := h
    subst j
    rfl

private theorem sign_sigmaCongrRight_mulSingle
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (i : ι) (p : Equiv.Perm (β i)) :
    Equiv.Perm.sign (Equiv.sigmaCongrRight (Pi.mulSingle (M := fun i => Equiv.Perm (β i)) i p)) =
      Equiv.Perm.sign p := by
  classical
  have hperm :
      Equiv.sigmaCongrRight (Pi.mulSingle (M := fun i => Equiv.Perm (β i)) i p) =
        p.extendDomain (sigmaFiberEquiv i) := by
    apply Equiv.ext
    rintro ⟨j, x⟩
    by_cases hji : j = i
    · subst j
      change
        ⟨i, (Pi.mulSingle (M := fun i => Equiv.Perm (β i)) i p) i x⟩ =
          (p.extendDomain (sigmaFiberEquiv i)) ((sigmaFiberEquiv i x).1)
      rw [Equiv.Perm.extendDomain_apply_image]
      simp [sigmaFiberEquiv]
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simpa using hji)]
      simp [hji]
  rw [hperm, Equiv.Perm.sign_extendDomain]

/-- For a finite family of finite types, the sign of the fiberwise permutation is the
product of the signs of its component permutations. -/
theorem sign_sigmaCongrRight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (p : ∀ i, Equiv.Perm (β i)) :
    Equiv.Perm.sign (Equiv.sigmaCongrRight p) =
      ∏ i, Equiv.Perm.sign (p i) := by
  classical
  let hcomm :
      Pairwise fun i j : ι =>
        ∀ (x : Equiv.Perm (β i)) (y : Equiv.Perm (β j)),
          Commute (Equiv.Perm.sign x) (Equiv.Perm.sign y) :=
    fun _ _ _ _ _ => Commute.all _ _
  let rhs : (∀ i, Equiv.Perm (β i)) →* ℤˣ :=
    MonoidHom.noncommPiCoprod (fun i => Equiv.Perm.sign) hcomm
  have hhom :
      Equiv.Perm.sign.comp (Equiv.Perm.sigmaCongrRightHom β) = rhs := by
    apply MonoidHom.pi_ext
    intro i q
    change Equiv.Perm.sign (Equiv.sigmaCongrRight (Pi.mulSingle (M := fun i => Equiv.Perm (β i)) i q)) =
      rhs (Pi.mulSingle (M := fun i => Equiv.Perm (β i)) i q)
    rw [sign_sigmaCongrRight_mulSingle i q]
    simp [rhs, MonoidHom.noncommPiCoprod_mulSingle]
  have hp := congrArg (fun h : (∀ i, Equiv.Perm (β i)) →* ℤˣ => h p) hhom
  change Equiv.Perm.sign (Equiv.sigmaCongrRight p) = rhs p at hp
  dsimp [rhs] at hp
  rw [MonoidHom.noncommPiCoprod_apply, Finset.noncommProd_eq_prod] at hp
  exact hp

end Equiv.Perm
