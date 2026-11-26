/-
  Ordinal rank definition `r_i = 1 + #{j : w_j > w_i}`, bounds, and tie invariance.
-/

import RST.Foundations.Normalization

namespace RST

/-- Competition ordinal rank of individual `i`: `1` plus the number of strictly higher weights. -/
def ordinalRank {n : Nat} (w : Fin n → Rat) (i : Fin n) : Nat :=
  1 + countFin (fun j => decide (w i < w j))

theorem ordinalRank_ge_one {n : Nat} (w : Fin n → Rat) (i : Fin n) :
    1 ≤ ordinalRank w i := by
  unfold ordinalRank
  omega

theorem ordinalRank_le_n {n : Nat} (w : Fin n → Rat) (i : Fin n) :
    ordinalRank w i ≤ n := by
  unfold ordinalRank
  -- `j = i` satisfies `¬ (w i < w i)`, so count is at most `n - 1`.
  have aux : ∀ {m : Nat} (f : Fin m → Rat) (k : Fin m),
      countFin (fun j => decide (f k < f j)) + 1 ≤ m := by
    intro m f k
    induction m with
    | zero => exact Fin.elim0 k
    | succ d ih =>
        refine Fin.cases ?_ ?_ k
        · simp only [countFin_succ]
          have hfalse : decide (f 0 < f 0) = false := by
            simp only [decide_eq_false_iff_not]
            grind
          rw [hfalse]
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
          have hle := countFin_le_len (fun j : Fin d => decide (f 0 < f j.succ))
          omega
        · intro k'
          simp only [countFin_succ]
          have ihk := ih (fun j => f j.succ) k'
          cases hb : decide (f k'.succ < f 0)
          · simp; omega
          · simp; omega
  have h := aux w i
  omega

theorem ordinalRank_eq_of_eq {n : Nat} (w : Fin n → Rat) {i j : Fin n} (h : w i = w j) :
    ordinalRank w i = ordinalRank w j := by
  unfold ordinalRank
  have hfun : (fun k : Fin n => decide (w i < w k)) = (fun k => decide (w j < w k)) := by
    funext k
    rw [h]
  rw [hfun]

end RST
