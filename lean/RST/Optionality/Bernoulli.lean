/-
  Bernoulli trial moments and heterogeneous Poisson-binomial sum moments.
-/

import RST.Foundations.Vectors

namespace RST

def bernoulliMean (p : Rat) : Rat := p

def bernoulliVar (p : Rat) : Rat := p * (1 - p)

theorem bernoulliVar_nonneg {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ bernoulliVar p := by
  unfold bernoulliVar
  exact Rat.mul_nonneg hp0 (by grind)

theorem bernoulliVar_le_quarter (p : Rat) :
    bernoulliVar p ≤ 1 / 4 := by
  unfold bernoulliVar
  have hsq : 0 ≤ (p - 1 / 2) * (p - 1 / 2) := rat_sq_nonneg (p - 1 / 2)
  grind

/-- Mean of independent heterogeneous Bernoulli trials `X_i ~ Bernoulli(p_i)`. -/
def poissonBinomialMean {n : Nat} (ps : Fin n → Rat) : Rat :=
  sumFin ps

/-- Variance of independent heterogeneous Bernoulli trials `X_i ~ Bernoulli(p_i)`. -/
def poissonBinomialVar {n : Nat} (ps : Fin n → Rat) : Rat :=
  sumFin (fun i => bernoulliVar (ps i))

theorem poissonBinomialMean_mono {n : Nat} (ps qs : Fin n → Rat)
    (hle : ∀ i, ps i ≤ qs i) :
    poissonBinomialMean ps ≤ poissonBinomialMean qs :=
  sumFin_le_sumFin ps qs hle

theorem poissonBinomialVar_nonneg {n : Nat} (ps : Fin n → Rat)
    (hp : ∀ i, 0 ≤ ps i ∧ ps i ≤ 1) :
    0 ≤ poissonBinomialVar ps := by
  unfold poissonBinomialVar
  apply sumFin_nonneg
  intro i
  exact bernoulliVar_nonneg (hp i).1 (hp i).2

theorem poissonBinomialVar_le_n_quarter {n : Nat} (ps : Fin n → Rat) :
    poissonBinomialVar ps ≤ (n : Rat) / 4 := by
  unfold poissonBinomialVar
  have hle : sumFin (fun i : Fin n => bernoulliVar (ps i)) ≤ sumFin (fun _ : Fin n => (1 / 4 : Rat)) :=
    sumFin_le_sumFin _ _ (fun i => bernoulliVar_le_quarter (ps i))
  have hconst : ∀ m : Nat, sumFin (fun _ : Fin m => (1 / 4 : Rat)) = (m : Rat) / 4 := by
    intro m
    induction m with
    | zero => simp; grind
    | succ k ih =>
        simp only [sumFin_succ]
        rw [ih]
        have hsucc : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
          apply Rat.ext
          · rw [Rat.num_natCast, Rat.add_def', Rat.num_mkRat]
            simp [Rat.num_natCast, Rat.den_natCast, Int.natCast_add, Nat.gcd_one_left]
          · rw [Rat.den_natCast, Rat.add_def', Rat.den_mkRat]
            simp [Rat.num_natCast, Rat.den_natCast, Nat.gcd_one_left]
        rw [hsucc]
        grind
  rw [hconst n] at hle
  exact hle

end RST
