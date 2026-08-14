import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedOrder

set_option linter.style.header false

/-!
# Restricting the mixed event order along a monotone family of interaction slots

A connected piece of a two-point diagram carries only some of the ambient interaction vertices, so
its own mixed event order is computed from its own slot indices while the ambient order uses the
ambient ones. At equal times the stable rank is monotone in the interaction slot, so a strictly
monotone slot reindexing preserves the mixed event order exactly. This layer is statistics-independent.
-/

namespace SecondQuantization
namespace Common

variable {m n : ℕ} {f : Fin m → Fin n}

/-- Transport a mixed event along a reindexing of the interaction slots, fixing the two external
events. -/
def twoPointTimedEventMap (f : Fin m → Fin n) : TwoPointTimedEvent m → TwoPointTimedEvent n
  | .inl e => .inl e
  | .inr v => .inr (f v)

@[simp]
theorem twoPointTimedEventMap_inl (f : Fin m → Fin n) (e : Fin 2) :
    twoPointTimedEventMap f (Sum.inl e) = Sum.inl e := rfl

@[simp]
theorem twoPointTimedEventMap_inr (f : Fin m → Fin n) (v : Fin m) :
    twoPointTimedEventMap f (Sum.inr v) = Sum.inr (f v) := rfl

theorem twoPointTimedEventMap_injective (hf : Function.Injective f) :
    Function.Injective (twoPointTimedEventMap f) := by
  intro a b hab
  cases a with
  | inl a =>
      cases b with
      | inl b => simpa using hab
      | inr w => simp at hab
  | inr v =>
      cases b with
      | inl b => simp at hab
      | inr w =>
          simp only [twoPointTimedEventMap_inr, Sum.inr.injEq] at hab
          exact congrArg Sum.inr (hf hab)

@[simp]
theorem twoPointTimedEventTime_map (f : Fin m → Fin n) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a : TwoPointTimedEvent m) :
    twoPointTimedEventTime τ τ' σ (twoPointTimedEventMap f a) =
      twoPointTimedEventTime τ τ' (σ ∘ f) a := by
  cases a <;> rfl

theorem twoPointTimedEventRank_map_le_iff (hf : StrictMono f) (a b : TwoPointTimedEvent m) :
    twoPointTimedEventRank (twoPointTimedEventMap f a) ≤
        twoPointTimedEventRank (twoPointTimedEventMap f b) ↔
      twoPointTimedEventRank a ≤ twoPointTimedEventRank b := by
  have hfle : ∀ x y : Fin m, ((f x : ℕ) ≤ (f y : ℕ)) ↔ ((x : ℕ) ≤ (y : ℕ)) := by
    intro x y
    rw [← Fin.le_def, ← Fin.le_def]
    exact hf.le_iff_le
  cases a with
  | inl a =>
      cases b with
      | inl b => exact Iff.rfl
      | inr w =>
          have ha := a.isLt
          simp only [twoPointTimedEventMap_inl, twoPointTimedEventMap_inr,
            twoPointTimedEventRank]
          omega
  | inr v =>
      cases b with
      | inl b =>
          have hb := b.isLt
          simp only [twoPointTimedEventMap_inl, twoPointTimedEventMap_inr,
            twoPointTimedEventRank]
          omega
      | inr w =>
          have h := hfle v w
          simp only [twoPointTimedEventMap_inr, twoPointTimedEventRank]
          omega

theorem twoPointTimedEventBeforeOrEqual_map_iff (hf : StrictMono f) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent m) :
    twoPointTimedEventBeforeOrEqual τ τ' σ
        (twoPointTimedEventMap f a) (twoPointTimedEventMap f b) ↔
      twoPointTimedEventBeforeOrEqual τ τ' (σ ∘ f) a b := by
  simp only [twoPointTimedEventBeforeOrEqual, twoPointTimedEventTime_map]
  rw [twoPointTimedEventRank_map_le_iff hf]

theorem twoPointTimedEventBefore_map_iff (hf : StrictMono f) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent m) :
    twoPointTimedEventBefore τ τ' σ (twoPointTimedEventMap f a) (twoPointTimedEventMap f b) ↔
      twoPointTimedEventBefore τ τ' (σ ∘ f) a b := by
  simp only [twoPointTimedEventBefore]
  rw [twoPointTimedEventBeforeOrEqual_map_iff hf]
  constructor
  · rintro ⟨h, hne⟩
    exact ⟨h, fun hab => hne (congrArg (twoPointTimedEventMap f) hab)⟩
  · rintro ⟨h, hne⟩
    exact ⟨h, fun hab => hne (twoPointTimedEventMap_injective hf.injective hab)⟩

theorem orderedTwoPointTimedEventPosition_map_lt_iff (hf : StrictMono f) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (a b : TwoPointTimedEvent m) :
    orderedTwoPointTimedEventPosition τ τ' σ (twoPointTimedEventMap f a) <
        orderedTwoPointTimedEventPosition τ τ' σ (twoPointTimedEventMap f b) ↔
      orderedTwoPointTimedEventPosition τ τ' (σ ∘ f) a <
        orderedTwoPointTimedEventPosition τ τ' (σ ∘ f) b := by
  rw [orderedTwoPointTimedEventPosition_lt_iff, orderedTwoPointTimedEventPosition_lt_iff,
    twoPointTimedEventBefore_map_iff hf]

theorem orderedTwoPointTimedEventPosition_orderEmbOfFin_lt_iff {k : ℕ} (T : Finset (Fin n))
    (hT : T.card = k) (τ τ' : ℝ) (σ : Fin n → ℝ) (a b : TwoPointTimedEvent k) :
    orderedTwoPointTimedEventPosition τ τ' σ (twoPointTimedEventMap ⇑(T.orderEmbOfFin hT) a) <
        orderedTwoPointTimedEventPosition τ τ' σ
          (twoPointTimedEventMap ⇑(T.orderEmbOfFin hT) b) ↔
      orderedTwoPointTimedEventPosition τ τ' (σ ∘ ⇑(T.orderEmbOfFin hT)) a <
        orderedTwoPointTimedEventPosition τ τ' (σ ∘ ⇑(T.orderEmbOfFin hT)) b :=
  orderedTwoPointTimedEventPosition_map_lt_iff (T.orderEmbOfFin hT).strictMono τ τ' σ a b

end Common
end SecondQuantization
