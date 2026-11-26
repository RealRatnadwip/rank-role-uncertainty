/-
  Absorbing states, post-collapse invariance, and EMA attention-weight updates.
-/

import RST.Dynamics.Markov

namespace RST

/-- State `k` is absorbing if transition probability `T k k = 1`. -/
def IsAbsorbing {n : Nat} (M : StochasticMatrix n) (k : Fin n) : Prop :=
  M.T k k = 1

theorem absorbing_off_diag_zero {n : Nat} (M : StochasticMatrix n) (k : Fin n)
    (habs : IsAbsorbing M k) :
    ∀ j : Fin n, j ≠ k → M.T k j = 0 := by
  have hz := sumFin_zero_single (fun j => M.T k j) k
  rw [M.row_sum_one, habs] at hz
  have hsum0 : sumFin (fun j => if j = k then 0 else M.T k j) = 0 := by grind
  have hall := sumFin_eq_zero_of_nonneg (fun j => if j = k then 0 else M.T k j)
    (fun j => by by_cases hj : j = k <;> simp [hj, M.nonneg]) hsum0
  intro j hjk
  have hj := hall j
  simp [hjk] at hj
  exact hj

theorem absorbing_point_mass_invariant {n : Nat} (M : StochasticMatrix n) (k : Fin n)
    (habs : IsAbsorbing M k) (mu : ProbDist n) (hmu : mu.w k = 1) :
    (stepDist M mu).w k = 1 := by
  have hother : ∀ i : Fin n, i ≠ k → mu.w i = 0 := by
    have hz := sumFin_zero_single mu.w k
    rw [mu.sum_one, hmu] at hz
    have h0 : sumFin (fun i => if i = k then 0 else mu.w i) = 0 := by grind
    have hall := sumFin_eq_zero_of_nonneg (fun i => if i = k then 0 else mu.w i)
      (fun i => by by_cases hi : i = k <;> simp [hi, mu.nonneg]) h0
    intro i hik
    have hi := hall i
    simp [hik] at hi
    exact hi
  dsimp [stepDist]
  have hterm : (fun i : Fin n => mu.w i * M.T i k) = fun i => if i = k then 1 else 0 := by
    funext i
    by_cases hik : i = k
    · subst hik
      have hkk : M.T i i = 1 := habs
      simp [hmu, hkk]
    · simp [hik, hother i hik]
  rw [hterm]
  have hz := sumFin_zero_single (fun i : Fin n => if i = k then (1 : Rat) else 0) k
  have hzero : (fun i : Fin n => if i = k then (0 : Rat) else if i = k then 1 else 0) =
      fun _ => 0 := by
    funext i; by_cases hik : i = k <;> simp [hik]
  rw [hzero, sumFin_zero_fun] at hz
  simp only [↓reduceIte] at hz
  grind

/-- Exponential moving average (EMA) attention update preserves valid weights. -/
def emaUpdate {n : Nat} (alpha : Rat) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (W : Weights n) (slot : Fin n) : Weights n where
  w := fun i => (1 - alpha) * W.w i + (if i = slot then alpha else 0)
  nonneg := fun i => by
    have h1 := Rat.mul_nonneg (by grind : 0 ≤ 1 - alpha) (W.nonneg i)
    by_cases his : i = slot <;> simp [his] <;> grind
  sum_one := by
    rw [sumFin_add, sumFin_smul, W.sum_one]
    have hz := sumFin_zero_single (fun i : Fin n => if i = slot then alpha else 0) slot
    have hzero : (fun i : Fin n => if i = slot then (0 : Rat) else if i = slot then alpha else 0) =
        fun _ => 0 := by
      funext i; by_cases his : i = slot <;> simp [his]
    rw [hzero, sumFin_zero_fun] at hz
    simp only [↓reduceIte] at hz
    grind

end RST
