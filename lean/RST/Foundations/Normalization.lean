/-
  Weight normalization, subunit bounds, partner exit renormalization,
  and probability distribution structure.
-/

import RST.Foundations.Vectors

namespace RST

/-- A normalized non-negative weight vector over `n` individuals. -/
structure Weights (n : Nat) where
  w : Fin n → Rat
  nonneg : ∀ i, 0 ≤ w i
  sum_one : sumFin w = 1

/-- Every entry of a normalized weight vector lies in `[0, 1]`. -/
theorem weights_le_one {n : Nat} (W : Weights n) (k : Fin n) : W.w k ≤ 1 := by
  have h := elem_le_sumFin W.w W.nonneg k
  rw [W.sum_one] at h
  exact h

/-- A weight vector obtained by removing individual `k` and renormalizing. -/
def removePartner {n : Nat} (W : Weights n) (k : Fin n) : Fin n → Rat :=
  fun i => if i = k then 0 else W.w i / (1 - W.w k)

theorem removePartner_self {n : Nat} (W : Weights n) (k : Fin n) :
    removePartner W k k = 0 := by
  simp [removePartner]

theorem removePartner_nonneg {n : Nat} (W : Weights n) (k : Fin n)
    (hk : W.w k < 1) (i : Fin n) :
    0 ≤ removePartner W k i := by
  unfold removePartner
  split
  · exact Rat.le_refl
  · exact rat_div_nonneg (W.nonneg i) (by grind)

theorem removePartner_sum_one {n : Nat} (W : Weights n) (k : Fin n)
    (hk : W.w k < 1) :
    sumFin (removePartner W k) = 1 := by
  have hden_ne : 1 - W.w k ≠ 0 := by grind
  have hfun : removePartner W k =
      (fun i => (if i = k then 0 else W.w i) / (1 - W.w k)) := by
    funext i
    unfold removePartner
    split <;> simp [Rat.div_def]
  rw [hfun, sumFin_div_const]
  have hz := sumFin_zero_single W.w k
  rw [W.sum_one] at hz
  have hnum : sumFin (fun i => if i = k then 0 else W.w i) = 1 - W.w k := by grind
  rw [hnum, Rat.div_def, Rat.mul_inv_cancel _ hden_ne]

def renormAfterRemoval {n : Nat} (W : Weights n) (k : Fin n) (hk : W.w k < 1) :
    Weights n where
  w := removePartner W k
  nonneg := removePartner_nonneg W k hk
  sum_one := removePartner_sum_one W k hk

/-- Edge case: if `n = 1`, the unique individual necessarily holds weight `1`. -/
theorem singleton_weight_one (W : Weights 1) : W.w 0 = 1 := by
  have h := W.sum_one
  simp [sumFin_succ, sumFin_zero] at h
  grind

/-- Generalized renormalization over any retained subset `keep` with positive mass. -/
def renormMask {n : Nat} (W : Weights n) (keep : Fin n → Bool) : Fin n → Rat :=
  fun i =>
    let mass := sumFin (fun j => if keep j then W.w j else 0)
    if keep i then W.w i / mass else 0

theorem renormMask_valid {n : Nat} (W : Weights n) (keep : Fin n → Bool)
    (hmass : 0 < sumFin (fun i => if keep i then W.w i else 0)) :
    (∀ i, 0 ≤ renormMask W keep i) ∧
    (∀ i, keep i = false → renormMask W keep i = 0) ∧
    sumFin (renormMask W keep) = 1 := by
  have hne : sumFin (fun j => if keep j then W.w j else 0) ≠ 0 := by grind
  refine ⟨?_, ?_, ?_⟩
  · intro i
    dsimp [renormMask]
    cases h : keep i
    · simp
    · simp [rat_div_nonneg (W.nonneg i) hmass]
  · intro i hi
    dsimp [renormMask]
    simp [hi]
  · have hfun : renormMask W keep =
        (fun i => (if keep i then W.w i else 0) / sumFin (fun j => if keep j then W.w j else 0)) := by
      funext i
      dsimp [renormMask]
      cases keep i <;> simp [Rat.div_def]
    rw [hfun, sumFin_div_const, Rat.div_def, Rat.mul_inv_cancel _ hne]

end RST
