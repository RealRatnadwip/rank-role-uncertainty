/-
  Discrete probability distributions over finite supports, expectation, and variance.
-/

import RST.Foundations.Normalization

namespace RST

abbrev ProbDist (n : Nat) := Weights n

def expectVal {n : Nat} (P : ProbDist n) (X : Fin n → Rat) : Rat :=
  sumFin (fun i => P.w i * X i)

def varianceVal {n : Nat} (P : ProbDist n) (X : Fin n → Rat) : Rat :=
  let mu := expectVal P X
  sumFin (fun i => P.w i * ((X i - mu) * (X i - mu)))

theorem varianceVal_nonneg {n : Nat} (P : ProbDist n) (X : Fin n → Rat) :
    0 ≤ varianceVal P X := by
  unfold varianceVal
  apply sumFin_nonneg
  intro i
  exact Rat.mul_nonneg (P.nonneg i) (rat_sq_nonneg _)

theorem expectVal_const {n : Nat} (P : ProbDist n) (c : Rat) :
    expectVal P (fun _ => c) = c := by
  unfold expectVal
  have h : (fun i : Fin n => P.w i * c) = fun i => c * P.w i := by
    funext i; rw [Rat.mul_comm]
  rw [h, sumFin_smul, P.sum_one]
  grind

theorem expectVal_bounds {n : Nat} (P : ProbDist n) (X : Fin n → Rat) (lo hi : Rat)
    (hlo : ∀ i, lo ≤ X i) (hhi : ∀ i, X i ≤ hi) :
    lo ≤ expectVal P X ∧ expectVal P X ≤ hi := by
  constructor
  · have h1 : sumFin (fun i => P.w i * lo) ≤ sumFin (fun i => P.w i * X i) :=
      sumFin_le_sumFin _ _ (fun i => Rat.mul_le_mul_of_nonneg_left (hlo i) (P.nonneg i))
    have hconst : sumFin (fun i => P.w i * lo) = lo := expectVal_const P lo
    rw [hconst] at h1
    exact h1
  · have h1 : sumFin (fun i => P.w i * X i) ≤ sumFin (fun i => P.w i * hi) :=
      sumFin_le_sumFin _ _ (fun i => Rat.mul_le_mul_of_nonneg_left (hhi i) (P.nonneg i))
    have hconst : sumFin (fun i => P.w i * hi) = hi := expectVal_const P hi
    rw [hconst] at h1
    exact h1

end RST
