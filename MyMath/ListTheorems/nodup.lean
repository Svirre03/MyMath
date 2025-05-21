
namespace MyMath.ListTheorems

theorem nodups_eraseDups [DecidableEq α] (l : List α) : (l.eraseDups).Nodup :=
  by
  induction l with
  |nil => exact List.nodup_nil
  |cons x xs ih =>
    if h : x ∈ xs.eraseDups then
      have h2 : (x :: xs).eraseDups = xs.eraseDups :=
        by
        rw[List.eraseDups]
        unfold List.eraseDups
        sorry

      rw[h2]
      exact ih
    else
      have h2 : (x :: xs).eraseDups = x :: xs.eraseDups := by sorry
      rw[h2]
      apply Iff.mpr List.nodup_cons (And.intro h ih)
