import Mathlib.LinearAlgebra.LinearPMap

set_option linter.style.header false

/-!
# Natural-domain composition of partially defined linear maps

For partially defined linear maps `f : E →ₗ.[R] F` and `g : F →ₗ.[R] G`, the natural
composition domain consists exactly of those `x` in the domain of `f` whose image `f x`
lies in the domain of `g`.

Mathlib's `LinearPMap.comp` composes two partial maps when the whole domain of the inner map is
already mapped into the outer domain.  The construction here instead restricts to the maximal
natural operator-product domain.
-/

namespace LinearPMap

variable {R E F G : Type*} [Ring R]
variable [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]
variable [AddCommGroup G] [Module R G]

/-- Natural domain of the composition `g ∘ f`: points in `f.domain` whose image lies in
`g.domain`. -/
def naturalCompDomain (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) : Submodule R E :=
  (g.domain.comap f.toFun).map f.domain.subtype

/-- Membership in the natural composition domain. -/
theorem mem_naturalCompDomain_iff (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) (x : E) :
    x ∈ naturalCompDomain g f ↔
      ∃ hx : x ∈ f.domain, f ⟨x, hx⟩ ∈ g.domain := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hg⟩
    exact ⟨⟨x, hx⟩, hg, rfl⟩

private theorem naturalCompDomain_le_right (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) :
    naturalCompDomain g f ≤ f.domain := by
  intro x hx
  rcases (mem_naturalCompDomain_iff g f x).1 hx with ⟨hxf, _⟩
  exact hxf

/-- Compose two partially defined linear maps on their natural operator-product domain. -/
def compOnDomain (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) : E →ₗ.[R] G where
  domain := naturalCompDomain g f
  toFun :=
    g.toFun.comp <|
      LinearMap.codRestrict g.domain
        (f.toFun.comp (Submodule.inclusion (naturalCompDomain_le_right g f)))
        (fun x => by
          rcases (mem_naturalCompDomain_iff g f x).1 x.2 with ⟨hx, hg⟩
          change f ⟨(x : E), naturalCompDomain_le_right g f x.2⟩ ∈ g.domain
          simpa only using hg)

@[simp]
theorem compOnDomain_domain (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) :
    (g.compOnDomain f).domain = naturalCompDomain g f :=
  rfl

/-- Evaluation of a natural-domain composition on any witnesses of the two domain conditions. -/
theorem compOnDomain_apply (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) {x : E}
    (hx : x ∈ (g.compOnDomain f).domain) (hxf : x ∈ f.domain)
    (hgf : f ⟨x, hxf⟩ ∈ g.domain) :
    g.compOnDomain f ⟨x, hx⟩ = g ⟨f ⟨x, hxf⟩, hgf⟩ := by
  rfl

/-- Membership in the domain of natural-domain composition is exactly the usual operator-product
condition. -/
theorem mem_compOnDomain_domain_iff (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) (x : E) :
    x ∈ (g.compOnDomain f).domain ↔
      ∃ hx : x ∈ f.domain, f ⟨x, hx⟩ ∈ g.domain :=
  mem_naturalCompDomain_iff g f x

end LinearPMap
