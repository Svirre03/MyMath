--Imports
import MyMath.SetTheory.Indexedset.def

namespace MyMath.SetTheory.Indexedset

open MyMath.Function


--Show that ∼ is an equivalence relation
section EqvEqivalenceRel

variable {α : Type} (s t r : Indexedset α)

--eqv is equivalence relation

--reflexivity
theorem eqv_refl : s ∼ s :=
  by
  rw[←eqv_eq_sim]
  rw[eqv]

  exists id

  apply And.intro
  · exact Function.Bijective.id
  · intro b
    rw[id]

--symmetry
theorem eqv_symm [Nonempty s.index] [Nonempty t.index] (h_eqv : s ∼ t) : t ∼ s :=
  by
  --Unfold defs
  rw[←eqv_eq_sim]
  rw[eqv]

  rw[←eqv_eq_sim] at h_eqv
  rw[eqv] at h_eqv

  --Get φ permutation from hypothesis
  let φ := Classical.choose h_eqv
  have h_phi_bij : Function.Bijective φ := (Classical.choose_spec h_eqv).left
  have h_hasInverse : hasInverse φ := (bij_iff_hasInverse φ).mp h_phi_bij
  have h_phi_perm : ∀i : s.index, s.elems i = t.elems (φ i) := (Classical.choose_spec h_eqv).right

  --Get φ⁻¹ = ψ
  let ψ := Function.Inverse φ h_hasInverse

  --ψ is bijective
  have h_isInverse : isInverse φ ψ := isInverse_of_Inverse φ h_hasInverse
  have h_psi_bij : Bijective ψ := bij_of_isInverse φ ψ h_isInverse

  --ψ satisfies condition
  have h_psi_perm : ∀j : t.index, t.elems j = s.elems (ψ j) :=
    by
    intro j
    rw[h_phi_perm, h_isInverse.right]

  --ψ is the correct permutation
  exists ψ


theorem eqv_trans (h_eqv_s_t : s ∼ t) (h_eqv_t_r : t ∼ r) : s ∼ r :=
  by
  --Get bijective functions and their properties
  let φ : s.index → t.index := Classical.choose h_eqv_s_t
  let ψ : t.index → r.index := Classical.choose h_eqv_t_r

  have h_phi_bij := (Classical.choose_spec h_eqv_s_t).left
  have h_psi_bij := (Classical.choose_spec h_eqv_t_r).left

  have h_phi_perm : ∀i : s.index, s.elems i = t.elems (φ i) := (Classical.choose_spec h_eqv_s_t).right
  have h_psi_perm : ∀j : t.index, t.elems j = r.elems (ψ j) := (Classical.choose_spec h_eqv_t_r).right

  --Get composition
  let χ : s.index → r.index := ψ ∘ φ

  have h_chi_bij : Bijective χ := Bijective.comp φ ψ  h_phi_bij h_psi_bij

  have h_chi_perm : ∀i : s.index, s.elems i = r.elems (χ i) :=
    by
    intro i
    rw[h_phi_perm, h_psi_perm]
    rfl

  --χ is the correct permutation
  exists χ


end EqvEqivalenceRel


--Theorems for subsets
section SubsetRel

variable {α : Type} (s t r : Indexedset α)


--Subset of self
theorem subset_of_eqv (h_eqv : s ∼ t): s ⊆ t :=
  by

  --Get bijective permutation
  let φ : s.index → t.index := Classical.choose h_eqv
  have h_phi_bij : Bijective φ := (Classical.choose_spec h_eqv).left
  have h_phi_perm : ∀i : s.index, s.elems i = t.elems (φ i) := (Classical.choose_spec h_eqv).right

  --φ is the right perm
  exists φ

  apply And.intro
  --Injective
  · exact h_phi_bij.left

  --Permutation
  · exact h_phi_perm


theorem subset_of_self : s ⊆ s :=
  by
  --Eqv to self
  have h_eqv : s ∼ s := eqv_refl s

  exact subset_of_eqv s s h_eqv


--Subsets are transitive
theorem subset_trans (h_subs_s_t : s ⊆ t) (h_subs_t_r : t ⊆ r) : s ⊆ r :=
  by
  --Get surjective functions and their properties
  let φ : s.index → t.index := Classical.choose h_subs_s_t
  let ψ : t.index → r.index := Classical.choose h_subs_t_r

  have h_phi_inj : Injective φ := (Classical.choose_spec h_subs_s_t).left
  have h_psi_inj : Injective ψ := (Classical.choose_spec h_subs_t_r).left

  have h_phi_perm : ∀i : s.index, s.elems i = t.elems (φ i) := (Classical.choose_spec h_subs_s_t).right
  have h_psi_perm : ∀j : t.index, t.elems j = r.elems (ψ j) := (Classical.choose_spec h_subs_t_r).right

  --Get composition
  let χ : s.index → r.index := ψ ∘ φ

  have h_chi_inj : Injective χ := Injective.comp φ ψ  h_phi_inj h_psi_inj

  have h_chi_perm : ∀i : s.index, s.elems i = r.elems (χ i) :=
    by
    intro i
    rw[h_phi_perm, h_psi_perm]
    rfl

  --χ is the correct permutation
  exists χ


end SubsetRel


end MyMath.SetTheory.Indexedset
