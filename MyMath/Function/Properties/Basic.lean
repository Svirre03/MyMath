--Imports
import MyMath.Function.Properties.def


namespace MyMath.Function

section Jections

variable {α β γ : Type}

--theorems for injecive, surjective, bijective

--Compositions
theorem Injective.comp {α β γ : Type} (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) :=
  by
  intro a a' h
  rw[Function.comp, Function.comp] at h
  apply hf
  apply hg
  exact h

theorem Surjective.comp {α β γ : Type} (f : α → β) (g : β → γ) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) :=
  by
  intro c
  obtain ⟨b, hb⟩ := hg c
  obtain ⟨a , ha⟩ := hf b
  exists a
  rw[Function.comp, ha, hb]

theorem Bijective.comp {α β γ : Type} (f : α → β) (g : β → γ) (hf : Bijective f) (hg : Bijective g) : Bijective (g ∘ f) :=
  by
  rw[Bijective]
  rw[Bijective] at hf
  rw[Bijective] at hg
  exact ⟨Injective.comp f g hf.left hg.left, Surjective.comp f g hf.right hg.right⟩

--Identity function
theorem Surjective.id : Surjective (@id α) :=
  by
  rw[Surjective]
  intro b
  exists b

theorem Injective.id : Injective (@id α) :=
  by
  rw[Injective]
  intro a a' h_eq
  rw[id_def, id_def] at h_eq
  exact h_eq

theorem Bijective.id : Bijective (@id α) :=
  by
  rw[Bijective]
  exact ⟨Injective.id, Surjective.id⟩

theorem inj_eq_of_ne (a b : α) (f : α → β) (h_inj : Injective f) (h_ne : ¬a=b) : ¬f a = f b :=
  by
  intro h_f_eq

  have h_eq : a = b := h_inj a b h_f_eq

  contradiction


end Jections


--Functions to and from empty types
section InversesEmpty

variable {α β : Type} (f : α → β)

--Function from emptytype is injective
theorem inj_from_empty (h_empty_α : ¬Nonempty α) : Injective f :=
  by
  intro a
  have h' := h_empty_α ⟨a⟩
  contradiction

--Function to emptytype is surjective
theorem surj_to_empty (h_empty_β : ¬Nonempty β) : Surjective f :=
  by
  intro b
  have h' := h_empty_β ⟨b⟩
  contradiction

--Function to and from emptytype is bij
theorem bij_to_from_empty (h_empty_α : ¬Nonempty α) (h_empty_β : ¬Nonempty β) : Bijective f :=
  by
  apply And.intro
  --Injective
  · exact inj_from_empty f h_empty_α

  --Surjective
  · exact surj_to_empty f h_empty_β


end InversesEmpty


--Weak inverse theorems
section WeakInverse

variable {α β : Type} [Nonempty α] (f : α → β) (g : β → α)


theorem weakInverse_of_eq (b : β) (h : ∃a : α, f a = b) : f (weakInverse f b) = b :=
  by
  rw[weakInverse]
  simp [h]

  exact h.choose_spec

--Weak inverse left inverse of injective
theorem weakInverse_of_inj (h_inj : Injective f) : isLeftInverse f (weakInverse f) :=
  by
  intro a
  have h_ext : ∃a' : α, f a' = f a := by exists a

  apply h_inj

  exact weakInverse_of_eq f (f a) h_ext


theorem weakInverse_of_surj (h_surj : Surjective f) : isRightInverse f (weakInverse f) :=
  by
  intro b

  rw[Surjective] at h_surj

  exact weakInverse_of_eq f b (h_surj b)

theorem weakInverse_of_bij (h_bij : Bijective f) : isInverse f (weakInverse f) :=
  by
  rw[isInverse]

  apply And.intro
  --Left Inverse
  · exact weakInverse_of_inj f h_bij.left
  · exact weakInverse_of_surj f h_bij.right



--Injective iff leftinverse
theorem inj_iff_hasLeftInverse : (Function.Injective f) ↔ (hasLeftInverse f) :=
  by
  apply Iff.intro
  --Left Implication
  · intro h_inj
    exists weakInverse f
    exact weakInverse_of_inj f h_inj

  --Right Implication
  · intro h_has_left_inv
    let g : β → α := LeftInverse f h_has_left_inv
    have g_left_inv : isLeftInverse f g := Classical.choose_spec h_has_left_inv
    rw[isLeftInverse] at g_left_inv

    intro a a' h_eq
    have h_comp_eq : g (f a) = g (f a') := congrArg g h_eq
    rw[g_left_inv, g_left_inv] at h_comp_eq

    exact h_comp_eq


--surjective iff rightinverse
theorem surj_iff_hasRightInverse : (Surjective f) ↔ (hasRightInverse f) :=
  by
  apply Iff.intro

  --Left Implication
  · intro h_surj
    exists (weakInverse f)
    exact weakInverse_of_surj f h_surj

  --Right Implication
  · intro h_has_right_inv
    let g : β → α := RightInverse f h_has_right_inv
    have g_right_inverse : isRightInverse f g := Classical.choose_spec h_has_right_inv

    intro b

    exists g b
    exact g_right_inverse b

end WeakInverse


section Inverses

variable {α β : Type} (f : α → β) (g : β → α) (h : β → α)


--LeftInverse isLeftInverse
theorem isLeftInverse_of_LeftInverse (h_hasLeftInverse : hasLeftInverse f) : isLeftInverse f (LeftInverse f h_hasLeftInverse) :=
  by
  exact Classical.choose_spec h_hasLeftInverse

theorem isRightInverse_of_RightInverse (h_hasRightInverse : hasRightInverse f) : isRightInverse f (RightInverse f h_hasRightInverse) :=
  by
  exact Classical.choose_spec h_hasRightInverse

theorem isInverse_of_Inverse (h_hasInverse : hasInverse f) : isInverse f (Inverse f h_hasInverse) :=
  by
  exact Classical.choose_spec h_hasInverse


--Inverse is left inverse
theorem isLeftInverse_of_isInverse (h_isInverse : isInverse f g) : isLeftInverse f g :=
  by
  exact h_isInverse.left

theorem hasLeftInverse_of_hasInverse (h_hasInverse : hasInverse f) : hasLeftInverse f :=
  by
  let g : β → α := Inverse f h_hasInverse
  have g_inv : isInverse f g := isInverse_of_Inverse f h_hasInverse
  exists g
  exact g_inv.left


--Inverse is Right Inverse
theorem isRightInverse_of_isInverse (h_isInverse : isInverse f g) : isRightInverse f g :=
  by
  exact h_isInverse.right

theorem hasRightInverse_of_hasInverse (h_hasInverse : hasInverse f) : hasRightInverse f :=
  by
  let g : β → α := Inverse f h_hasInverse
  have g_inv : isInverse f g := isInverse_of_Inverse f h_hasInverse
  exists g
  exact g_inv.right


--bijective iff inverse
theorem bij_iff_hasInverse [Nonempty α] : (Bijective f) ↔ (hasInverse f) :=
  by
  apply Iff.intro

  --Left Implication
  · intro h_bij
    exists (weakInverse f)
    exact weakInverse_of_bij f h_bij

  --Right Implication
  · intro h_has_inv

    apply And.intro
    --Injective
    · have h_hasLeftInverse : hasLeftInverse f := hasLeftInverse_of_hasInverse f h_has_inv
      exact (inj_iff_hasLeftInverse f).mpr h_hasLeftInverse

    --Surjective
    · have h_hasRightInverse : hasRightInverse f := hasRightInverse_of_hasInverse f h_has_inv
      exact (surj_iff_hasRightInverse f).mpr h_hasRightInverse


--If f has left and right inverse, f has inverse
theorem hasInverse_of_hasLeftRightInverse [Nonempty α] (h_hasLeftInverse : hasLeftInverse f) (h_hasRightInverse : hasRightInverse f) : hasInverse f :=
  by
  have h_inj : Injective f := (inj_iff_hasLeftInverse f).mpr h_hasLeftInverse
  have h_surj : Surjective f := (surj_iff_hasRightInverse f).mpr h_hasRightInverse
  have h_bij : Bijective f := And.intro h_inj h_surj

  exact (bij_iff_hasInverse f).mp h_bij


--unique inverse
theorem unique_Inverse [Nonempty α] (h_g_isInverse : isInverse f g) (h_h_isInverse : isInverse f h) : g = h :=
  by
  apply funext
  intro b

  have h_inv : hasInverse f := by exists g
  have h_bij : Bijective f := (bij_iff_hasInverse f).mpr h_inv

  let a : α := Classical.choose (h_bij.right b)
  have h_preimg : f a = b := Classical.choose_spec (h_bij.right b)

  rw[←h_preimg, h_g_isInverse.left, h_h_isInverse.left]


--rightinverse of leftinverse
theorem isRightInverse_of_isLeftInverse (h_isLeftInverse : isLeftInverse f g) : isRightInverse g f :=
  by
  exact h_isLeftInverse


--LeftInverse of RightInverse
theorem isLeftInverse_of_isRightInverse (h_isRightInverse : isRightInverse f g) : isLeftInverse g f :=
  by
  exact h_isRightInverse


--Inverse is inverse
theorem isInverse_of_isInverse (h_isInverse : isInverse f g) : isInverse g f :=
  by
  apply And.intro
  --left inverse
  · exact h_isInverse.right

  --right inverse
  · exact h_isInverse.left


--LeftInverse is surjective
theorem surj_of_isLeftInverse [Nonempty β] (h_isLeftInverse : isLeftInverse f g) : Surjective g :=
  by
  have g_hasRightInverse : hasRightInverse g := by exists f

  exact (surj_iff_hasRightInverse g).mpr g_hasRightInverse


--RightInverse is Injective
theorem inj_of_isRightInverse [Nonempty β] (h_isRightInverse : isRightInverse f g) : Injective g :=
  by
  have g_hasLeftInverse : hasLeftInverse g := by exists f

  exact (inj_iff_hasLeftInverse g).mpr g_hasLeftInverse

--Inverse is Bijective
theorem bij_of_isInverse [Nonempty β] (h_isInverse : isInverse f g) : Bijective g :=
  by
  have g_hasInverse : hasInverse g :=
    by
    exists f
    exact isInverse_of_isInverse f g h_isInverse

  exact (bij_iff_hasInverse g).mpr g_hasInverse

  theorem isInverse_of_isRightInverse_of_surj [Nonempty α] [Nonempty β](h_isRightInverse : isRightInverse f g) (h_g_surj : Surjective g) : isInverse f g :=
    by

    have h_g_inj : Injective g := inj_of_isRightInverse f g h_isRightInverse

    have h_g_bij : Bijective g := ⟨h_g_inj, h_g_surj⟩

    have h_g_hasInverse : hasInverse g := (bij_iff_hasInverse g).mp h_g_bij

    let h : α → β := Classical.choose h_g_hasInverse
    have h_h_isInverse : isInverse g h := Classical.choose_spec h_g_hasInverse
    have h_h_bij : Bijective h := bij_of_isInverse g h h_h_isInverse

    have h_f_h_eq : f = h :=
      by
      apply funext

      intro a

      let b : β := Classical.choose (h_g_surj a)
      have h_b : g b = a := Classical.choose_spec (h_g_surj a)

      have h_h_a_eq : h a = b :=
        by
        rw[←h_b]
        exact h_h_isInverse.left b

      rw[h_h_a_eq, ←h_b]

      exact h_isRightInverse b

    apply (isInverse_of_isInverse g f)

    rw[←h_f_h_eq] at h_h_isInverse

    exact h_h_isInverse

  theorem isInverse_of_isLeftInverse_of_inj [Nonempty α] [Nonempty β] (h_isLeftInverse : isLeftInverse f g) (h_g_inj : Injective g) : isInverse f g :=
    by

    have h_isRightInverse : isRightInverse g f := isRightInverse_of_isLeftInverse f g h_isLeftInverse
    have h_hasRightInverse : hasRightInverse g := ⟨f, h_isRightInverse⟩
    have h_g_surj : Surjective g := (surj_iff_hasRightInverse g).mpr h_hasRightInverse

    have h_g_bij : Bijective g := ⟨h_g_inj, h_g_surj⟩

    have h_g_hasInverse : hasInverse g := (bij_iff_hasInverse g).mp h_g_bij

    let h : α → β := Classical.choose h_g_hasInverse
    have h_h_isInverse : isInverse g h := Classical.choose_spec h_g_hasInverse
    have h_h_bij : Bijective h := bij_of_isInverse g h h_h_isInverse

    have h_f_surj : Surjective f :=
      by

      intro b

      let a : α := Classical.choose (h_h_bij.right b)
      have h_a : h a = b := Classical.choose_spec (h_h_bij.right b)

      rw[←(h_isLeftInverse a)] at h_a

      rw[h_h_isInverse.left] at h_a

      exists a

    have h_isInverse : isInverse g f := isInverse_of_isRightInverse_of_surj g f h_isRightInverse h_f_surj

    apply (isInverse_of_isInverse g f)

    exact h_isInverse


end Inverses

end MyMath.Function
