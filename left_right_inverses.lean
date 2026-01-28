import Mathlib

set_option linter.style.emptyLine false

/- obtain ⟨a, h⟩ := surj b -/
/-
  the goal isn't Prop, so we can't "eliminate"/match on with cases by obtain
  because of proof irrelevance.
-/

theorem surjective_iff_exists_right_inverse {α β} (f : α → β)
    : Function.Surjective f ↔ ∃g : β → α, f ∘ g = id := by

  constructor
  · intro surj
    use fun b => (surj b).choose

    funext a
    rw [Function.comp_apply, id_eq]
    rw [(surj a).choose_spec]

  · intro h b
    obtain ⟨g, hg⟩ := h
    use g b

    rw [← Function.comp_apply (f := f) (g := g), hg]
    rfl

theorem injective_iff_exists_left_inverse {α β} [Nonempty α] (f : α → β)
    : Function.Injective f ↔ ∃g : β → α, g ∘ f = id := by

  constructor
  · intro inj

    use fun b => by
      open Classical in
      exact if h : ∃a, f a = b then h.choose else Classical.arbitrary α

    funext a; simp only [Function.comp_apply, exists_apply_eq_apply, ↓reduceDIte, id_eq]
    have t : ∃ a_1, f a_1 = f a := by
      use a

    have : t.choose = a := by
      obtain ⟨a₁, h⟩ := t
      apply inj at h
      conv => rhs; rw [← h]
      grind

    -- proof irrelevance go!!
    conv => rhs; rw [← this]

  · intro h a₁ a₂
    obtain ⟨g, hg⟩ := h
    intro hf

    rw [← id_eq a₁, ← id_eq a₂, ← hg]
    rw [Function.comp_apply, Function.comp_apply]
    rw [hf]

