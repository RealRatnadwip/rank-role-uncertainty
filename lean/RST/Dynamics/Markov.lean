/-
  Finite-state Markov transition kernels, probability propagation, and regime mixtures.
-/

import RST.Foundations.Probability

namespace RST

/-- Row-stochastic transition matrix over `n` states. -/
structure StochasticMatrix (n : Nat) where
  T : Fin n → Fin n → Rat
  nonneg : ∀ i j, 0 ≤ T i j
  row_sum_one : ∀ i, sumFin (fun j => T i j) = 1

/-- Single-step forward propagation `mu' = mu^T * T`. -/
def stepDist {n : Nat} (M : StochasticMatrix n) (mu : ProbDist n) : ProbDist n where
  w := fun j => sumFin (fun i => mu.w i * M.T i j)
  nonneg := fun j => sumFin_nonneg _ (fun i => Rat.mul_nonneg (mu.nonneg i) (M.nonneg i j))
  sum_one := by
    rw [sumFin_swap]
    have hrow : (fun i : Fin n => sumFin (fun j => mu.w i * M.T i j)) = fun i => mu.w i := by
      funext i
      rw [sumFin_smul, M.row_sum_one]
      grind
    rw [hrow, mu.sum_one]

/-- Convex mixture of two regime transition kernels preserves row-stochasticity. -/
def convexMixKernel {n : Nat} (p : Rat) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : StochasticMatrix n) : StochasticMatrix n where
  T := fun i j => (1 - p) * A.T i j + p * B.T i j
  nonneg := fun i j => by
    have h1 := Rat.mul_nonneg (by grind : 0 ≤ 1 - p) (A.nonneg i j)
    have h2 := Rat.mul_nonneg hp0 (B.nonneg i j)
    grind
  row_sum_one := fun i => by
    rw [sumFin_add, sumFin_smul, sumFin_smul, A.row_sum_one, B.row_sum_one]
    grind

end RST
