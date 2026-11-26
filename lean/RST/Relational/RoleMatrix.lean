/-
  Relational role matrices, zero-safe column normalization, and normalization proofs.
-/

import RST.Foundations.Normalization

namespace RST

/-- Non-negative `n × m` relational role contribution matrix. -/
structure RoleMatrix (n m : Nat) where
  val : Fin n → Fin m → Rat
  nonneg : ∀ i j, 0 ≤ val i j

def colSum {n m : Nat} (M : RoleMatrix n m) (j : Fin m) : Rat :=
  sumFin (fun i => M.val i j)

theorem colSum_nonneg {n m : Nat} (M : RoleMatrix n m) (j : Fin m) :
    0 ≤ colSum M j :=
  sumFin_nonneg _ (fun i => M.nonneg i j)

/-- Zero-safe column normalization: returns `0` when the column sum is zero. -/
def colNormalize {n m : Nat} (M : RoleMatrix n m) (i : Fin n) (j : Fin m) : Rat :=
  let s := colSum M j
  if s = 0 then 0 else M.val i j / s

theorem colNormalize_nonneg {n m : Nat} (M : RoleMatrix n m) (i : Fin n) (j : Fin m) :
    0 ≤ colNormalize M i j := by
  unfold colNormalize
  by_cases hs : colSum M j = 0
  · simp [hs]
  · have hpos : 0 < colSum M j := by
      have hge := colSum_nonneg M j
      grind
    simp only [hs, ↓reduceIte]
    exact rat_div_nonneg (M.nonneg i j) hpos

theorem colNormalize_zero_col {n m : Nat} (M : RoleMatrix n m) (j : Fin m)
    (hz : colSum M j = 0) :
    ∀ i, colNormalize M i j = 0 := by
  intro i
  simp [colNormalize, hz]

theorem colNormalize_sum_one {n m : Nat} (M : RoleMatrix n m) (j : Fin m)
    (hpos : 0 < colSum M j) :
    sumFin (fun i => colNormalize M i j) = 1 := by
  have hne : colSum M j ≠ 0 := by grind
  have hfun : (fun i => colNormalize M i j) = (fun i => M.val i j / colSum M j) := by
    funext i
    simp [colNormalize, hne]
  rw [hfun, sumFin_div_const]
  change colSum M j / colSum M j = 1
  rw [Rat.div_def, Rat.mul_inv_cancel _ hne]

def normalizedRoleMatrix {n m : Nat} (M : RoleMatrix n m) : RoleMatrix n m where
  val := colNormalize M
  nonneg := colNormalize_nonneg M

end RST
