/-
  Model A (DistributedWeights) vs Model B (SharedMaximum):
  proves that subunit weights hold under Model A, shared maximum excludes
  unique maximum, and Model A does NOT imply Model B via (99/100, 1/100).
-/

import RST.Relational.UniqueMaximum

namespace RST

/-- Model A (Distributed relational weight): at least two distinct partners hold positive weight. -/
def DistributedWeights {n : Nat} (W : Weights n) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ 0 < W.w i ∧ 0 < W.w j

/-- Model B (Non-unique maximal position): at least two distinct partners attain the global maximum. -/
def SharedMaximum {n : Nat} (W : Weights n) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ (∀ k : Fin n, W.w k ≤ W.w i) ∧ (∀ k : Fin n, W.w k ≤ W.w j)

/-- Accurate scope of the v1.0 subunit theorem: under Model A, no individual holds all weight. -/
theorem subunit_weights_of_distributed {n : Nat} (W : Weights n)
    (hdist : DistributedWeights W) :
    ∀ k : Fin n, W.w k < 1 := by
  rcases hdist with ⟨i, j, hij, hi, hj⟩
  intro k
  have hother_pos : 0 < sumFin (fun m => if m = k then 0 else W.w m) := by
    by_cases hki : i = k
    · have hjk : j ≠ k := by
        intro heq
        exact hij (hki.trans heq.symm)
      have hle := elem_le_sumFin (fun m => if m = k then 0 else W.w m)
        (fun m => by by_cases hm : m = k <;> simp [hm, W.nonneg]) j
      simp only [hjk, ↓reduceIte] at hle
      grind
    · have hle := elem_le_sumFin (fun m => if m = k then 0 else W.w m)
        (fun m => by by_cases hm : m = k <;> simp [hm, W.nonneg]) i
      simp only [hki, ↓reduceIte] at hle
      grind
  have hsum := sumFin_zero_single W.w k
  rw [W.sum_one] at hsum
  grind

/-- Model B excludes a unique maximum on any finite portfolio. -/
theorem shared_max_excludes_unique_max {n : Nat} (W : Weights n)
    (hshared : SharedMaximum W) :
    ¬ ∃ k : Fin n, UniqueMaximum W k := by
  intro ⟨k, hk⟩
  rcases hshared with ⟨i, j, hij, hi, hj⟩
  by_cases hik : i = k
  · have hjk : j ≠ k := by
      intro heq
      exact hij (hik.trans heq.symm)
    have hlt := hk j hjk
    have hle := hj k
    grind
  · have hlt := hk i hik
    have hle := hi k
    grind

/-- Under Model B, at least two distinct individuals share competition ordinal rank `1`. -/
theorem shared_max_two_rank_one {n : Nat} (W : Weights n) (hshared : SharedMaximum W) :
    ∃ i j : Fin n, i ≠ j ∧ ordinalRank W.w i = 1 ∧ ordinalRank W.w j = 1 := by
  rcases hshared with ⟨i, j, hij, hi, hj⟩
  have hzero : ∀ {m : Nat} (f : Fin m → Bool), (∀ t, f t = false) → countFin f = 0 := by
    intro m f hf
    induction m with
    | zero => rfl
    | succ d ih =>
        simp only [countFin_succ, hf 0, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact ih (fun t => f t.succ) (fun t => hf t.succ)
  refine ⟨i, j, hij, ?_, ?_⟩
  · unfold ordinalRank
    have hall : ∀ t : Fin n, decide (W.w i < W.w t) = false := by
      intro t
      simp only [decide_eq_false_iff_not]
      have ht := hi t
      grind
    rw [hzero _ hall]
  · unfold ordinalRank
    have hall : ∀ t : Fin n, decide (W.w j < W.w t) = false := by
      intro t
      simp only [decide_eq_false_iff_not]
      have ht := hj t
      grind
    rw [hzero _ hall]

/-- Explicit counterexample: `w = (99/100, 1/100)`. -/
def w99 : Weights 2 where
  w | 0 => 99 / 100 | 1 => 1 / 100
  nonneg := by intro i; match i with | 0 => grind | 1 => grind
  sum_one := by simp [sumFin_succ, sumFin_zero]; grind

theorem counterexample_99_1_properties :
    DistributedWeights w99 ∧ UniqueMaximum w99 0 ∧ ¬ SharedMaximum w99 := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨0, 1, by decide, ?_, ?_⟩ <;> simp [w99] <;> grind
  · intro j hj
    match j with
    | 0 => exact absurd rfl hj
    | 1 => simp [w99]; grind
  · intro hshared
    have hno := shared_max_excludes_unique_max w99 hshared
    apply hno
    refine ⟨0, ?_⟩
    intro j hj
    match j with
    | 0 => exact absurd rfl hj
    | 1 => simp [w99]; grind

/-- Theorem separating Model A and Model B: Model A does not imply Model B. -/
theorem distributed_not_implies_shared_max :
    ¬ (∀ W : Weights 2, DistributedWeights W → SharedMaximum W) := by
  intro hall
  have h := counterexample_99_1_properties
  exact h.2.2 (hall w99 h.1)

/-- Conversely, when `n ≥ 2` and all weights are nonzero under Model B (e.g., uniform weights),
    Model B implies Model A whenever at least two maximal weights are strictly positive. -/
theorem shared_max_pos_implies_distributed {n : Nat} (W : Weights n)
    (hshared : SharedMaximum W)
    (hpos : ∃ i : Fin n, 0 < W.w i ∧ ∀ k, W.w k ≤ W.w i) :
    DistributedWeights W := by
  rcases hshared with ⟨i, j, hij, hi, hj⟩
  rcases hpos with ⟨m, hm_pos, hm_max⟩
  have hmi : W.w m = W.w i := by
    have h1 := hi m
    have h2 := hm_max i
    grind
  have hmj : W.w m = W.w j := by
    have h1 := hj m
    have h2 := hm_max j
    grind
  refine ⟨i, j, hij, ?_, ?_⟩ <;> grind

end RST
