/-
  Per-dimension role dominance, linear scalar aggregation, and rank-reversal sensitivity.
-/

import RST.Relational.RoleMatrix

namespace RST

/-- Individual `i` dominates functional dimension `j` if its entry is maximal in column `j`. -/
def DominatesDim {n m : Nat} (M : RoleMatrix n m) (i : Fin n) (j : Fin m) : Prop :=
  ∀ k : Fin n, M.val k j ≤ M.val i j

/-- Strict dominance in functional dimension `j`. -/
def StrictlyDominatesDim {n m : Nat} (M : RoleMatrix n m) (i : Fin n) (j : Fin m) : Prop :=
  ∀ k : Fin n, k ≠ i → M.val k j < M.val i j

theorem strict_dominates_implies_dominates {n m : Nat} (M : RoleMatrix n m)
    (i : Fin n) (j : Fin m) (h : StrictlyDominatesDim M i j) :
    DominatesDim M i j := by
  intro k
  by_cases hki : k = i
  · rw [hki]; exact Rat.le_refl
  · have hlt := h k hki
    grind

/-- Weighted global aggregation score `G_i(alpha) = sum_j alpha_j * M_{ij}`. -/
def globalScore {n m : Nat} (M : RoleMatrix n m) (alpha : Weights m) (i : Fin n) : Rat :=
  sumFin (fun j => alpha.w j * M.val i j)

theorem globalScore_nonneg {n m : Nat} (M : RoleMatrix n m) (alpha : Weights m) (i : Fin n) :
    0 ≤ globalScore M alpha i := by
  unfold globalScore
  apply sumFin_nonneg
  intro j
  exact Rat.mul_nonneg (alpha.nonneg j) (M.nonneg i j)

theorem globalScore_le_one_of_col_norm {n m : Nat} (M : RoleMatrix n m)
    (hcol : ∀ i j, M.val i j ≤ 1) (alpha : Weights m) (i : Fin n) :
    globalScore M alpha i ≤ 1 := by
  unfold globalScore
  have hle : sumFin (fun j => alpha.w j * M.val i j) ≤ sumFin (fun j => alpha.w j * 1) :=
    sumFin_le_sumFin _ _ (fun j => Rat.mul_le_mul_of_nonneg_left (hcol i j) (alpha.nonneg j))
  have h1 : (fun j : Fin m => alpha.w j * 1) = alpha.w := by
    funext j; grind
  rw [h1, alpha.sum_one] at hle
  exact hle

/-- Disjoint specialization witness: individual 0 dominates role 0, individual 1 dominates role 1,
    and different valid weightings reverse their global ranking. -/
def exRoleM : RoleMatrix 2 2 where
  val
    | 0, 0 => 4 / 5
    | 0, 1 => 1 / 5
    | 1, 0 => 1 / 5
    | 1, 1 => 4 / 5
  nonneg := by
    intro i j
    match i, j with
    | 0, 0 => grind
    | 0, 1 => grind
    | 1, 0 => grind
    | 1, 1 => grind

def exAlphaPrimary : Weights 2 where
  w | 0 => 3 / 4 | 1 => 1 / 4
  nonneg := by intro i; match i with | 0 => grind | 1 => grind
  sum_one := by simp [sumFin_succ, sumFin_zero]; grind

def exAlphaSupport : Weights 2 where
  w | 0 => 1 / 4 | 1 => 3 / 4
  nonneg := by intro i; match i with | 0 => grind | 1 => grind
  sum_one := by simp [sumFin_succ, sumFin_zero]; grind

theorem ex_disjoint_dominance :
    StrictlyDominatesDim exRoleM 0 0 ∧ StrictlyDominatesDim exRoleM 1 1 := by
  constructor
  · intro k hk
    match k with
    | 0 => exact absurd rfl hk
    | 1 => simp [exRoleM]; grind
  · intro k hk
    match k with
    | 0 => simp [exRoleM]; grind
    | 1 => exact absurd rfl hk

theorem ex_aggregation_rank_reversal :
    globalScore exRoleM exAlphaPrimary 1 < globalScore exRoleM exAlphaPrimary 0 ∧
    globalScore exRoleM exAlphaSupport 0 < globalScore exRoleM exAlphaSupport 1 := by
  constructor
  · simp [globalScore, exRoleM, exAlphaPrimary, sumFin_succ, sumFin_zero]; grind
  · simp [globalScore, exRoleM, exAlphaSupport, sumFin_succ, sumFin_zero]; grind

end RST
