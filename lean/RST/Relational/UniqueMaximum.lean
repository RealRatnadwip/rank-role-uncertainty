/-
  Unique maximum predicate, uniqueness of the maximizer, and rank-1 characterization.
-/

import RST.Relational.Ranking

namespace RST

/-- Individual `k` holds a unique maximum if its weight strictly exceeds every other weight. -/
def UniqueMaximum {n : Nat} (W : Weights n) (k : Fin n) : Prop :=
  ∀ j : Fin n, j ≠ k → W.w j < W.w k

theorem unique_max_unique {n : Nat} (W : Weights n) {k₁ k₂ : Fin n}
    (h1 : UniqueMaximum W k₁) (h2 : UniqueMaximum W k₂) : k₁ = k₂ := by
  by_cases h : k₁ = k₂
  · exact h
  · have hlt1 := h1 k₂ (Ne.symm h)
    have hlt2 := h2 k₁ h
    grind

theorem unique_max_rank_one {n : Nat} (W : Weights n) {k : Fin n}
    (h : UniqueMaximum W k) :
    ordinalRank W.w k = 1 := by
  unfold ordinalRank
  have hzero : ∀ {m : Nat} (f : Fin m → Bool), (∀ j, f j = false) → countFin f = 0 := by
    intro m f hf
    induction m with
    | zero => rfl
    | succ d ih =>
        simp only [countFin_succ, hf 0, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact ih (fun j => f j.succ) (fun j => hf j.succ)
  have hall : ∀ j : Fin n, decide (W.w k < W.w j) = false := by
    intro j
    simp only [decide_eq_false_iff_not]
    by_cases hjk : j = k
    · rw [hjk]; grind
    · have hlt := h j hjk
      grind
  rw [hzero _ hall]

theorem unique_max_tail_ge_two {n : Nat} (W : Weights n) {k : Fin n}
    (h : UniqueMaximum W k) :
    ∀ j : Fin n, j ≠ k → 2 ≤ ordinalRank W.w j := by
  intro j hjk
  unfold ordinalRank
  have hlt := h j hjk
  have htrue : decide (W.w j < W.w k) = true := by
    simp only [decide_eq_true_eq]
    exact hlt
  have hpos := countFin_pos_of_true (fun m => decide (W.w j < W.w m)) k htrue
  omega

end RST
