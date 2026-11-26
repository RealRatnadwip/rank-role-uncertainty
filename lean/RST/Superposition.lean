/-
  Formalization of relational superposition and Proposition "Nobody is first":
  whenever at least two partners carry positive weight, no partner holds unit weight.
-/

import RST.Normalization

namespace RST

/-- A weight vector is in relational superposition when at least two distinct
    partners hold strictly positive primary weight. -/
def InSuperposition {n : Nat} (W : Weights n) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ 0 < W.w i ∧ 0 < W.w j

/-- Amplitude-level superposition: at least two distinct amplitudes are nonzero. -/
def AmplitudesInSuperposition {n : Nat} (A : Amplitudes n) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ A.a i ≠ 0 ∧ A.a j ≠ 0

theorem amplitudes_superposition_implies_weights {n : Nat} (A : Amplitudes n)
    (h : AmplitudesInSuperposition A) :
    InSuperposition A.toWeights := by
  rcases h with ⟨i, j, hij, hi, hj⟩
  exact ⟨i, j, hij, rat_sq_pos hi, rat_sq_pos hj⟩

/-- Core theorem ("Nobody is first"): in a superposed state, every partner's
    primary weight is strictly less than 1. -/
theorem nobody_is_first {n : Nat} (W : Weights n) (hsup : InSuperposition W) :
    ∀ k : Fin n, W.w k < 1 := by
  rcases hsup with ⟨i, j, hij, hi, hj⟩
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

theorem nobody_has_unit_weight {n : Nat} (W : Weights n) (hsup : InSuperposition W) :
    ∀ k : Fin n, W.w k ≠ 1 :=
  fun k => by
    have hlt := nobody_is_first W hsup k
    grind

theorem amplitudes_nobody_is_first {n : Nat} (A : Amplitudes n)
    (hsup : AmplitudesInSuperposition A) :
    ∀ k : Fin n, A.a k * A.a k < 1 ∧ A.a k * A.a k ≠ 1 := by
  have hw := amplitudes_superposition_implies_weights A hsup
  intro k
  have hlt := nobody_is_first A.toWeights hw k
  change A.a k * A.a k < 1 at hlt
  exact ⟨hlt, by grind⟩

end RST
