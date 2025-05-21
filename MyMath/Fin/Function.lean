--Imports
import MyMath.Fin.Cast.Cast
import MyMath.Function.Function
import MyMath.Nat.Basic

--Theorems for functions between Fin's

namespace MyMath.Fin

open MyMath.Function

open MyMath.Nat

section Jections

variable (n m k : Nat)

attribute [local instance] Classical.propDecidable

--Define function used in theorems below
def downCastFunc (h_pos : n > 0) (f : Fin (n+1) → Fin (n+1)) : Fin n → Fin n :=
  fun i =>
    have h_succ_n_pos : n+1 > 0 := Nat.zero_lt_succ n
    let i_up : Fin (n+1) := @cast (n) (n+1) h_succ_n_pos i
        if _ : (f i_up) < (n) then
          @cast (n+1) (n) h_pos (f i_up)
        else
          @cast (n+1) (n) h_pos (f ⟨(n), Nat.lt_succ_self n⟩)

theorem dcf_of_lt (h_pos : n > 0) (a : Fin n) (f : Fin (n+1) → Fin (n+1))
(h_f_a_lt : f (@cast n (n+1) (Nat.zero_lt_succ n) a) < n) :
downCastFunc n h_pos f a = @cast (n+1) n h_pos (f (@cast n (n+1) (Nat.zero_lt_succ n) a)) :=
  by

  rw[downCastFunc]
  simp [h_f_a_lt]

theorem dcf_of_not_lt (h_pos : n > 0) (a : Fin n) (f : Fin (n+1) → Fin (n+1))
(h_f_a_not_lt : ¬ f (@cast n (n+1) (Nat.zero_lt_succ n) a) < n) :
downCastFunc n h_pos f a = @cast (n+1) n h_pos (f ⟨n, Nat.lt_succ_self n⟩) :=
  by

  rw[downCastFunc]
  simp [h_f_a_not_lt]


--if g a = g a' and f a_up < n then f a'_up < n
theorem lt_of_dcf_eq_of_lt (h_pos : n > 0) (a a' : Fin n) (f : Fin (n+1) → Fin (n+1))
(h_f_inj : Injective f)
(h_dcf_eq : downCastFunc n h_pos f a = downCastFunc n h_pos f a')
(h_f_a_up_lt : f (@cast n (n+1) (Nat.zero_lt_succ n) a) < n) :
f (@cast n (n+1) (Nat.zero_lt_succ n) a') < n :=
  by

  let g := downCastFunc n h_pos f
  have h_g : g = downCastFunc n h_pos f := by rfl

  let a_up := @cast n (n+1) (Nat.zero_lt_succ n) a
  let a'_up := @cast n (n+1) (Nat.zero_lt_succ n) a'
  have h_a_up : a_up = @cast n (n+1) (Nat.zero_lt_succ n) a := by rfl
  have h_a'_up : a'_up = @cast n (n+1) (Nat.zero_lt_succ n) a' := by rfl

  --Rewrite g a_up and a'_up in all locations
  rw[←h_a_up] at h_f_a_up_lt
  rw[←h_a'_up]


  --Rw with h_f_a_up_lt
  rw[downCastFunc] at h_dcf_eq
  simp [h_f_a_up_lt] at h_dcf_eq

  rw[←h_a_up] at h_dcf_eq

  --Argue by contradiction
  by_cases h_f_a'_up_lt : f (@cast n (n+1) (Nat.zero_lt_succ n) a') < n
  --If true
  · exact h_f_a'_up_lt

  --If not then contradiction
  · --Equality from symmetric ineqs
    have h_f_a'_up_vals_eq : f a'_up = n := val_eq_of_val_not_lt (f a'_up) h_f_a'_up_lt

    --Simplify downCastFunc
    rw[downCastFunc] at h_dcf_eq
    simp [h_f_a'_up_vals_eq] at h_dcf_eq

    --f(n) < n since f injective
    have h_f_n_lt : f ⟨n, Nat.lt_succ_self n⟩ < n :=
      by

      by_cases h_f_n_lt : f ⟨n, Nat.lt_succ_self n⟩ < n
      · exact h_f_n_lt

      --Contradiction
      · -- f(n) = n from symmetric ineqs
        have h_f_n_eq : f ⟨n, Nat.lt_succ_self n⟩ = n := val_eq_of_val_not_lt (f ⟨n, Nat.lt_succ_self n⟩) h_f_n_lt

        --↑f(n) = ↑f(a'_up) since both equal n
        have h_f_n_a'_up_vals_eq : (f a'_up).val = (f ⟨n, Nat.lt_succ_self n⟩).val :=
          by
          rw[h_f_a'_up_vals_eq, h_f_n_eq]

        --f (a'_up) = f (n) from values being equal
        have h_f_n_a'_up_eq : f a'_up = f ⟨n, Nat.lt_succ_self n⟩ := Fin.eq_of_val_eq h_f_n_a'_up_vals_eq

        --a'_up = n by injectivity of f
        have h_a'_up_n_eq : a'_up = ⟨n, Nat.lt_succ_self n⟩ := h_f_inj a'_up ⟨n, Nat.lt_succ_self n⟩ h_f_n_a'_up_eq

        --Have ↑a'_up.val = n from equal
        have h_a'_up_n_vals_eq : ↑a'_up = n := Fin.val_eq_of_eq h_a'_up_n_eq

        --Contradiction since a'_up.val < n
        have h_a'_up_a'_vals_eq : a'.val = a'_up.val := val_eq_of_cast (Nat.zero_lt_succ n) a' (Nat.lt_succ_of_lt a'.isLt)

        rw[h_a'_up_n_vals_eq] at h_a'_up_a'_vals_eq

        symm at h_a'_up_a'_vals_eq
        have h_a'_ge : ↑a' ≥ n := Nat.le_of_eq h_a'_up_a'_vals_eq
        have h_a'_not_lt : ¬↑a' < n := Nat.not_lt_of_ge h_a'_ge

        have h_a'_lt : a'.val < n := a'.isLt

        contradiction

    --f(a_up) = f(n) since casts are equal
    have h_f_a_up_eq_f_n : f a_up = f ⟨n, Nat.lt_succ_self n⟩ := cast_of_le_eq (f a_up) (f ⟨n, Nat.lt_succ_self n⟩) h_f_a_up_lt h_f_n_lt h_dcf_eq

    --a_up = n since f is injective
    have h_a_up_eq_n : a_up = ⟨n, Nat.lt_succ_self n⟩ := h_f_inj a_up ⟨n, Nat.lt_succ_self n⟩ h_f_a_up_eq_f_n


    --↑a = ↑a_up by val_eq_of_cast
    have h_vals_cast_eq : a.val = a_up.val := val_eq_of_cast (Nat.zero_lt_succ n) a (Nat.lt_succ_of_lt a.isLt)

    rw[h_a_up_eq_n] at h_vals_cast_eq
    symm at h_vals_cast_eq

    --↑a < n
    have h_a_val_lt : a.val < n := a.isLt

    --¬↑a < n
    have h_a_val_not_lt : ¬a.val < n := Nat.not_lt_of_ge (Nat.le_of_eq h_vals_cast_eq)

    contradiction


theorem eq_of_dcf_eq_of_eq (h_pos : n > 0) (a a' : Fin n) (f : Fin (n+1) → Fin (n+1))
(h_f_inj : Injective f)
(h_dcf_eq : downCastFunc n h_pos f a = downCastFunc n h_pos f a')
(h_f_a_up_eq : f (@cast n (n+1) (Nat.zero_lt_succ n) a) = n) :
f (@cast n (n+1) (Nat.zero_lt_succ n) a') = n :=
  by

  let g := downCastFunc n h_pos f
  have h_g : g = downCastFunc n h_pos f := by rfl

  let a_up := @cast n (n+1) (Nat.zero_lt_succ n) a
  let a'_up := @cast n (n+1) (Nat.zero_lt_succ n) a'
  have h_a_up : a_up = @cast n (n+1) (Nat.zero_lt_succ n) a := by rfl
  have h_a'_up : a'_up = @cast n (n+1) (Nat.zero_lt_succ n) a' := by rfl

  --Rewrite g a_up and a'_up in all locations
  rw[←h_a_up] at h_f_a_up_eq
  rw[←h_a'_up]

  --Argue by contradiction
  by_cases h_f_a'_up_lt : f a'_up < n
  · symm at h_dcf_eq
    have h_f_a_up_lt : f a_up < n := lt_of_dcf_eq_of_lt n h_pos a' a f h_f_inj h_dcf_eq h_f_a'_up_lt

    --Contradiction f(a_up) < n and f(a_up) = n
    symm at h_f_a_up_eq
    have h_f_a_up_ge : f a_up ≥ n := Nat.le_of_eq h_f_a_up_eq
    have h_f_a_up_not_le : ¬f a_up < n := Nat.not_lt_of_ge h_f_a_up_ge

    contradiction

  · exact val_eq_of_val_not_lt (f a'_up) h_f_a'_up_lt


--downCastFunc is injective if f is injective
theorem dcf_inj_of_inj (h_pos : n > 0) (f : Fin (n+1) → Fin (n+1)) (h_f_inj : Injective f) : Injective (downCastFunc n h_pos f) :=
  by
  --Intro for injective
  intro a a' h_a_eq_a'

  --Rewrite dcf
  let g : Fin n → Fin n := downCastFunc n h_pos f
  have h_g : g = downCastFunc n h_pos f := by rfl
  rw[←h_g] at h_a_eq_a'

  --Rewrite up_casted a a'
  let a_up : Fin (n+1) := @cast n (n+1) (Nat.zero_lt_succ n) a
  let a'_up : Fin (n+1) := @cast n (n+1) (Nat.zero_lt_succ n) a'

  by_cases h_f_a_up : f (a_up) < n
  --If f (a_up) < n
  · --Both f(a) and f(a') < n
    have h_f_a'_up : f (a'_up) < n := lt_of_dcf_eq_of_lt n h_pos a a' f h_f_inj h_a_eq_a' h_f_a_up

    simp [h_g, downCastFunc, h_f_a_up, h_f_a'_up] at h_a_eq_a'

    --f(a) = f(a') since casts are equal
    have h_f_a_f_a'_eq : f a_up = f a'_up := cast_of_le_eq (f a_up) (f a'_up) h_f_a_up h_f_a'_up h_a_eq_a'

    --a_up = a'_up since f is injective
    have h_a_up_a'_up_eq : a_up = a'_up := h_f_inj a_up a'_up h_f_a_f_a'_eq

    exact (@cast_le (n) (n+1) (Nat.zero_lt_succ n) (Nat.le_of_lt (Nat.lt_succ_self n))) a a' h_a_up_a'_up_eq

  --If f (a_up) = n
  · have h_f_a_up_eq : f a_up = n := val_eq_of_val_not_lt (f a_up) h_f_a_up

    --both f(a_up) = n and f(a'_up) = n
    have h_f_a'_up_eq : f a'_up = n := eq_of_dcf_eq_of_eq n h_pos a a' f h_f_inj h_a_eq_a' h_f_a_up_eq

    --↑f(a_up) = ↑f(a'_up)
    have h_f_a_up_f_a'_up_vals_eq : (f a_up).val = (f a'_up).val := by rw[h_f_a_up_eq, h_f_a'_up_eq]

    --f(a_up) = f(a'_up)
    have h_f_a_up_f_a'_up_eq : f a_up = f a'_up := Fin.eq_of_val_eq h_f_a_up_f_a'_up_vals_eq

    --a_up = a'_up since f is injective
    have h_a_up_a'_up_eq : a_up = a'_up := h_f_inj a_up a'_up h_f_a_up_f_a'_up_eq

    exact (@cast_le (n) (n+1) (Nat.zero_lt_succ n) (Nat.le_of_lt (Nat.lt_succ_self n))) a a' h_a_up_a'_up_eq

--if b < n then b is in the image of f
theorem surj_of_lt_of_dcf_surj (n : Nat) (h_pos : n > 0) (b : Fin (n+1)) (h_b_lt : ↑b < n)
(f : Fin (n+1) → Fin (n+1)) (h_f_inj : Injective f) (h_dcf_surj : Surjective (downCastFunc n h_pos f)) :
∃a : Fin (n+1), f a = b :=
  by

  let g : Fin n → Fin n := downCastFunc n h_pos f
  have h_g : g = downCastFunc n h_pos f := by rfl

  --cast b down
  let b_dwn : Fin n := @cast (n+1) n h_pos b

  --Get a_dwn such that g(a_dwn) = b_dwn
  let a_dwn : Fin n := Classical.choose (h_dcf_surj b_dwn)
  have h_g_a_dwn : g a_dwn = b_dwn := Classical.choose_spec (h_dcf_surj b_dwn)

  --Get n as fin (n+1)
  let n_fin : Fin (n+1) := ⟨n, Nat.lt_succ_self n⟩

  --Show that f(a) < n
  let a : Fin (n+1) := @cast n (n+1) (Nat.zero_lt_succ n) a_dwn

  have h_a_a_dwn_vals_eq : a_dwn.val = a.val := val_eq_of_cast (Nat.zero_lt_succ n) a_dwn (Nat.lt_succ_of_lt a_dwn.isLt)
  have h_a_val_lt : a.val < n :=
    by
    rw[←h_a_a_dwn_vals_eq]
    exact a_dwn.isLt

  have h_a_val_ne : ¬a.val = n := not_eq_of_lt a.val n h_a_val_lt
  have h_a_ne : ¬a = n_fin :=
    by

    by_cases h_a_eq : a = n_fin
    · have h_a_vals_eq : a.val = n := Fin.val_eq_of_eq h_a_eq
      contradiction

    · exact h_a_eq

  --Cases if f(a) = n or less
  by_cases h_f_a_eq : f a = n_fin
  --if f(a) = n
  · have h_f_n_ne : ¬f a = f n_fin :=
      by
      apply (inj_eq_of_ne a n_fin f h_f_inj h_a_ne)

    rw[h_f_a_eq] at h_f_n_ne

    have h_f_n_vals_ne : ¬n = f n_fin := val_ne_of_ne n_fin (f n_fin) h_f_n_ne

    have h_f_n_vals_ne_symm : ¬f n_fin = n :=
      by
      intro h
      symm at h
      exact h_f_n_vals_ne h

    have h_f_n_lt : f n_fin < n := val_lt_of_val_not_eq (f n_fin) h_f_n_vals_ne_symm

    have h_f_a_vals_eq : ↑(f a) = n := Fin.val_eq_of_eq h_f_a_eq

    have h_f_a_not_lt : ¬f a < n := not_lt_of_eq h_f_a_vals_eq

    simp [h_g, downCastFunc, h_f_a_not_lt] at h_g_a_dwn

    have h_f_n_eq_b : f n_fin = b := cast_of_le_eq (f n_fin) b h_f_n_lt h_b_lt h_g_a_dwn

    exists n_fin

  · have h_f_a_vals_ne : ¬↑(f a) = n := val_ne_of_ne (f a) n_fin h_f_a_eq

    have h_f_a_lt : f a < n := val_lt_of_val_not_eq (f a) h_f_a_vals_ne

    simp [h_g, downCastFunc, h_f_a_lt] at h_g_a_dwn

    have h_f_a_eq_b : f a = b := cast_of_le_eq (f a) b h_f_a_lt h_b_lt h_g_a_dwn

    exists a

--if b = n then b is in the image of f
theorem surj_of_eq_of_dcf_surj (n : Nat) (h_pos : n > 0) (b : Fin (n+1)) (h_b_eq : ↑b = n)
(f : Fin (n+1) → Fin (n+1)) (h_f_inj : Injective f) (h_dcf_surj : Surjective (downCastFunc n h_pos f)) :
∃a : Fin (n+1), f a = b :=
  by

  let g : Fin n → Fin n := downCastFunc n h_pos f
  have h_g : g = downCastFunc n h_pos f := by rfl

  let a : Fin (n+1) := f b
  have h_a : a = f b := by rfl

  let n_fin : Fin (n+1) := ⟨n, Nat.lt_succ_self n⟩
  have h_n_fin : n_fin = ⟨n, Nat.lt_succ_self n⟩ := by rfl
  have h_b_n_eq : b = n_fin := Fin.eq_of_val_eq h_b_eq

  --cases if a = n of a < n
  by_cases h_a_eq : a = n
  --if a = n then f (b) = b = n so b works
  · have h_a_n_eq : a = n_fin := Fin.eq_of_val_eq h_a_eq
    rw[h_a_n_eq] at h_a
    rw[←h_b_n_eq] at h_a
    symm at h_a
    exists b

  --if a < n then use def of g
  · have f_a_ne : a < n := val_lt_of_val_not_eq a h_a_eq

    --define down cast of a
    let a_dwn : Fin n := @cast (n+1) n h_pos a

    --choose i in preimage of g
    let i_dwn : Fin n := Classical.choose (h_dcf_surj a_dwn)
    have h_g_i_dwn : g i_dwn = a_dwn := Classical.choose_spec (h_dcf_surj a_dwn)

    --let i be upcast of i_dwn
    let i : Fin (n+1) := @cast n (n+1) (Nat.zero_lt_succ n) i_dwn


    --Argue by contradiction for f (i) = n
    by_cases h_f_i_eq : f i = n_fin
    · rw[←h_b_n_eq] at h_f_i_eq
      exists i

    · have h_f_i_lt : f i < n := val_lt_of_val_not_eq (f i) (val_ne_of_ne (f i) n_fin h_f_i_eq)
      simp [h_g, downCastFunc, h_f_i_lt] at h_g_i_dwn

      have h_f_i_n_eq : f i = a := cast_of_le_eq (f i) a h_f_i_lt f_a_ne h_g_i_dwn

      rw[h_a, h_b_n_eq] at h_f_i_n_eq

      have h_i_dwn_n_vals_ne : ¬↑i_dwn = n := not_eq_of_lt i_dwn.val n i_dwn.isLt

      have h_i_n_vals_ne : ¬↑i = n :=
        by
        rw[@val_eq_of_cast n (n+1) (Nat.zero_lt_succ n) i_dwn (Nat.lt_succ_of_lt i_dwn.isLt)] at h_i_dwn_n_vals_ne
        exact h_i_dwn_n_vals_ne

      have h_i_n_ne : ¬i = n_fin := Fin.ne_of_val_ne h_i_n_vals_ne

      have h_false : False := (inj_eq_of_ne i n_fin f h_f_inj h_i_n_ne) h_f_i_n_eq

      contradiction


--if f : Fin n → Fin n is injective then it is surjective
theorem surj_of_inj_fin (f : Fin n → Fin n) (h_inj : Injective f) : Surjective f :=
  by

  induction n with
  --n == 0 is true by default
  |zero =>
    --Fin 0 is empty
    have h_empty_fin_0 : ¬Nonempty (Fin 0) :=
      by
      intro h
      have a : Fin 0 := Classical.choice h
      have h : a.val < 0 := a.isLt
      contradiction
    --Function to empty type is surjective
    exact surj_to_empty f h_empty_fin_0

  --Construct g : Fin n' → Fin n'
  |succ n'  ih =>
    --Depends on if n' == 0 ↔ n = 1
    cases n' with
    --If n' == 0 f is surjective
    |zero =>
    --If a : Fin 1 then a = 0
      have h_zero_only (a : Fin 1) : a = ⟨0, Nat.zero_lt_one⟩ :=
        by
        have h_a_lt_one : a.val < 1 := a.isLt
        have h_a_ge_zero : 0 ≤ a.val := Nat.zero_le a.val
        have h_a_le_zero : a.val ≤ 0 := Nat.le_of_lt_succ h_a_lt_one
        have h_a_val_eq : a.val = 0 := Nat.le_antisymm h_a_le_zero h_a_ge_zero
        apply Fin.eq_of_val_eq
        rw[Fin.val_mk Nat.zero_lt_one]
        exact h_a_val_eq

      intro a
      have h_a_eq_zero : a = ⟨0, Nat.zero_lt_one⟩ := h_zero_only a

      exists ⟨0, Nat.zero_lt_one⟩

      have h_f_eq_zero : (f ⟨0, Nat.zero_lt_one⟩) = ⟨0, Nat.zero_lt_one⟩ := h_zero_only (f ⟨0, Nat.zero_lt_one⟩)

      rw[h_a_eq_zero, h_f_eq_zero]

    --If n' ≠ 0 then construct g
    |succ a =>
      have h_succ_a_pos : 0 < (a+1) := Nat.zero_lt_succ a

      let g : Fin (a+1) → Fin (a+1) := downCastFunc (a+1) h_succ_a_pos f

      --g is injective as proven above
      have h_g_inj : Injective g := dcf_inj_of_inj (a+1) h_succ_a_pos f h_inj

      --g is surjective by induction hypothesis
      have h_g_surj : Surjective g := ih g h_g_inj

      --Prove that f is surjective
      intro b

      let a_succ_fin : Fin (a+2) := ⟨(a+1), Nat.lt_succ_self (a+1)⟩

      by_cases h_b_eq : b = a_succ_fin
      · have h_b_vals_eq : ↑b = (a+1) := Fin.val_eq_of_eq h_b_eq
        exact surj_of_eq_of_dcf_surj (a+1) h_succ_a_pos b h_b_vals_eq f h_inj h_g_surj

      · have h_b_lt : b.val < (a+1) := val_lt_of_val_not_eq b (val_ne_of_ne b a_succ_fin h_b_eq)
        exact surj_of_lt_of_dcf_surj (a+1) h_succ_a_pos b h_b_lt f h_inj h_g_surj

--if f : Fin n → Fin n is surjective then it is injective
theorem inj_of_surj_fin (f : Fin n → Fin n) (h_surj : Surjective f) : Injective f :=
  by
  by_cases h_nonempty : Nonempty (Fin n)
  · have h_hasRightInverse : hasRightInverse f := (surj_iff_hasRightInverse f).mp h_surj

    let g : Fin n → Fin n := Classical.choose h_hasRightInverse
    have h_g_isRightInverse : isRightInverse f g := Classical.choose_spec h_hasRightInverse

    have h_g_inj : Injective g := inj_of_isRightInverse f g h_g_isRightInverse

    have h_g_surj : Surjective g := surj_of_inj_fin n g h_g_inj

    have h_isInverse : isInverse f g := isInverse_of_isRightInverse_of_surj f g h_g_isRightInverse h_g_surj

    have h_f_bij : Bijective f := (bij_iff_hasInverse f).mpr (⟨g, h_isInverse⟩)

    exact h_f_bij.left

  · exact inj_from_empty f h_nonempty


--Big theorem !!!!!!!
theorem inj_iff_surj_of_fin (f : Fin n → Fin n) : Injective f ↔ Surjective f :=
  by

  apply Iff.intro
  · exact surj_of_inj_fin n f

  · exact inj_of_surj_fin n f


--Injection between fin's
theorem le_of_inj (f : Fin n → Fin m) (h_f_inj : Injective f) : n ≤ m :=
  by

  by_cases h_m_lt : m < n
  · have h_n_pos : n > 0 := Nat.zero_lt_of_lt h_m_lt

    let h : Fin m → Fin n := @cast m n h_n_pos
    have h_h_inj : Injective h := cast_le h_n_pos (Nat.le_of_lt h_m_lt)

    let g : Fin m → Fin m := f ∘ h
    have h_g : g = f ∘ h := by rfl
    have h_g_inj : Injective g := Injective.comp h f h_h_inj h_f_inj

    --g is surjective by theorem
    have h_g_surj : Surjective g := surj_of_inj_fin m g h_g_inj

    let n_pred : Nat := n-1
    have h_n_pred_lt : n_pred < n := Nat.pred_lt_self h_n_pos

    have h_n_pred_m_ge : n_pred ≥ m := Nat.le_pred_of_lt h_m_lt

    let n_fin : Fin n := ⟨n_pred, h_n_pred_lt⟩

    let b : Fin m :=  f n_fin
    have h_b : b = f n_fin := by rfl

    let a : Fin m := Classical.choose (h_g_surj b)
    have h_a : g a = b := Classical.choose_spec (h_g_surj b)

    rw[h_g, Function.comp] at h_a

    have h_a_val_lt : a.val < n_pred := Nat.lt_of_lt_of_le a.isLt h_n_pred_m_ge

    have h_h_a_val : a.val = (h a).val := val_eq_of_cast h_n_pos a (lt_of_lt_of_lt a.isLt h_m_lt)

    rw[h_h_a_val] at h_a_val_lt

    have h_h_a_val_ne : ¬(h a).val = n_pred := not_eq_of_lt (h a) n_pred h_a_val_lt

    have h_h_a_ne : ¬h a = n_fin := Fin.ne_of_val_ne h_h_a_val_ne

    rw[h_b] at h_a

    have h_false : False := inj_eq_of_ne (h a) n_fin f h_f_inj h_h_a_ne h_a

    contradiction


  · exact Nat.not_lt.mp h_m_lt


--Surjection between fin's
theorem ge_of_surj (f : Fin n → Fin m) (h_f_surj : Surjective f) : n ≥ m :=
  by

  --Argue by contradiction
  by_cases h_n_lt : n < m
  · --if n = 0 or not
    by_cases h_n_pos : n > 0
    · have h_nonempty_n : Nonempty (Fin n) := ⟨⟨0, h_n_pos⟩⟩
      have h_nonempty_m : Nonempty (Fin m) := ⟨⟨0, lt_of_lt_of_lt h_n_pos h_n_lt⟩⟩

      have h_hasRightInverse : hasRightInverse f := (surj_iff_hasRightInverse f).mp h_f_surj
      let g : Fin m → Fin n := Classical.choose h_hasRightInverse
      have h_g : isRightInverse f g := Classical.choose_spec h_hasRightInverse
      have h_isLeftInverse : isLeftInverse g f := isLeftInverse_of_isRightInverse f g h_g
      have h_hasLeftInverse : hasLeftInverse g := ⟨f, h_isLeftInverse⟩

      have h_g_inj : Injective g := (inj_iff_hasLeftInverse g).mpr h_hasLeftInverse

      have h_m_n_le : m ≤ n := le_of_inj m n g h_g_inj

      have h_not_n_lt : ¬n < m := Nat.not_lt.mpr h_m_n_le

      contradiction

    · have h_n_le_zero : n ≤ 0 := Nat.not_lt.mp h_n_pos
      have h_n_eq_zero : n = 0 := Nat.le_zero.mp h_n_le_zero

      let zero_fin : Fin m := ⟨n, h_n_lt⟩

      let n_fin : Fin n := Classical.choose (h_f_surj zero_fin)

      have h_n_fin_lt_zero : n_fin.val < 0 := Nat.lt_of_lt_of_eq n_fin.isLt h_n_eq_zero

      contradiction

  · exact Nat.not_lt.mp h_n_lt


--Bijection between fin's
theorem eq_of_bij (f : Fin n → Fin m) (h_bij : Bijective f) : n = m :=
  by
  have h_le : n ≤ m := le_of_inj n m f h_bij.left
  have h_ge : n ≥ m := ge_of_surj n m f h_bij.right

  exact Nat.le_antisymm h_le h_ge

end Jections
