/-
  Binomial moments, exact superposition probability P(K >= 2), marginal step identity,
  monotonicity in n and in attractiveness A.
-/

import RST.Optionality.Bernoulli

namespace RST

/-- Rational power by structural recursion on `Nat`. -/
def powRat (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => x * powRat x n

@[simp] theorem powRat_zero (x : Rat) : powRat x 0 = 1 := rfl
@[simp] theorem powRat_succ (x : Rat) (n : Nat) : powRat x (n + 1) = x * powRat x n := rfl

theorem natCast_rat_succ (n : Nat) : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
  apply Rat.ext
  · rw [Rat.num_natCast, Rat.add_def', Rat.num_mkRat]
    simp [Rat.num_natCast, Rat.den_natCast, Int.natCast_add, Nat.gcd_one_left]
  · rw [Rat.den_natCast, Rat.add_def', Rat.den_mkRat]
    simp [Rat.num_natCast, Rat.den_natCast, Nat.gcd_one_left]

theorem powRat_nonneg {x : Rat} (hx : 0 ≤ x) : ∀ n : Nat, 0 ≤ powRat x n
  | 0 => by simp; grind
  | n + 1 => by
      simp only [powRat_succ]
      exact Rat.mul_nonneg hx (powRat_nonneg hx n)

theorem powRat_pos {x : Rat} (hx : 0 < x) : ∀ n : Nat, 0 < powRat x n
  | 0 => by simp; grind
  | n + 1 => by
      simp only [powRat_succ]
      exact Rat.mul_pos hx (powRat_pos hx n)

def binomialMean (n : Nat) (p : Rat) : Rat := (n : Rat) * p

def binomialVar (n : Nat) (p : Rat) : Rat := (n : Rat) * p * (1 - p)

theorem binomialMean_mono_n {n₁ n₂ : Nat} (hn : n₁ ≤ n₂) {p : Rat} (hp : 0 ≤ p) :
    binomialMean n₁ p ≤ binomialMean n₂ p := by
  unfold binomialMean
  exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hn) hp

theorem binomialMean_mono_p (n : Nat) {p₁ p₂ : Rat} (hp : p₁ ≤ p₂) :
    binomialMean n p₁ ≤ binomialMean n p₂ := by
  unfold binomialMean
  exact Rat.mul_le_mul_of_nonneg_left hp Rat.natCast_nonneg

theorem binomialVar_nonneg (n : Nat) {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binomialVar n p := by
  unfold binomialVar
  exact Rat.mul_nonneg (Rat.mul_nonneg Rat.natCast_nonneg hp0) (by grind)

theorem binomialVar_le_n_quarter (n : Nat) (p : Rat) :
    binomialVar n p ≤ (n : Rat) / 4 := by
  unfold binomialVar
  have h1 : p * (1 - p) ≤ 1 / 4 := bernoulliVar_le_quarter p
  have h2 : (n : Rat) * (p * (1 - p)) ≤ (n : Rat) * (1 / 4) :=
    Rat.mul_le_mul_of_nonneg_left h1 Rat.natCast_nonneg
  grind

/-- Probability that at least 2 of `n` independent viable options stabilize
    concurrently, each with retention probability `p`. -/
def superpositionProb (p : Rat) (n : Nat) : Rat :=
  if n < 2 then 0
  else 1 - powRat (1 - p) n - (n : Rat) * p * powRat (1 - p) (n - 1)

@[simp] theorem superpositionProb_zero (p : Rat) : superpositionProb p 0 = 0 := by
  simp [superpositionProb]

@[simp] theorem superpositionProb_one (p : Rat) : superpositionProb p 1 = 0 := by
  simp [superpositionProb]

/-- Exact discrete marginal gain from adding one viable partner (`n >= 1`). -/
theorem superpositionProb_step (p : Rat) : ∀ n : Nat, 1 ≤ n →
    superpositionProb p (n + 1) - superpositionProb p n =
      (n : Rat) * p * p * powRat (1 - p) (n - 1)
  | 0, h => by contradiction
  | 1, _ => by
      simp [superpositionProb, powRat]
      grind
  | k + 2, _ => by
      have h1 : ¬ (k + 2 < 2) := by omega
      have h2 : ¬ (k + 3 < 2) := by omega
      simp only [superpositionProb, h1, h2, ↓reduceIte]
      have hsub1 : k + 3 - 1 = k + 2 := by omega
      have hsub2 : k + 2 - 1 = k + 1 := by omega
      rw [hsub1, hsub2]
      simp only [powRat_succ]
      have hm : ((k + 2 + 1 : Nat) : Rat) = ((k + 2 : Nat) : Rat) + 1 :=
        natCast_rat_succ (k + 2)
      rw [hm]
      grind

theorem superpositionProb_step_nonneg {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {n : Nat} (hn : 1 ≤ n) :
    superpositionProb p n ≤ superpositionProb p (n + 1) := by
  have hdiff := superpositionProb_step p n hn
  have hq : 0 ≤ powRat (1 - p) (n - 1) := powRat_nonneg (by grind) (n - 1)
  have hn0 : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
  have hpp : 0 ≤ p * p := Rat.mul_nonneg hp0 hp0
  have hm1 : 0 ≤ (n : Rat) * (p * p) := Rat.mul_nonneg hn0 hpp
  have hm2 : 0 ≤ (n : Rat) * (p * p) * powRat (1 - p) (n - 1) := Rat.mul_nonneg hm1 hq
  grind

theorem superpositionProb_mono {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ {n m : Nat}, n ≤ m → superpositionProb p n ≤ superpositionProb p m
  | 0, 0, _ => by simp
  | 0, m + 1, _ => by
      have hstep : superpositionProb p 0 ≤ superpositionProb p 1 := by simp
      have hind : superpositionProb p 1 ≤ superpositionProb p (m + 1) := by
        induction m with
        | zero => exact Rat.le_refl
        | succ k ih =>
            have hk : 1 ≤ k + 1 := by omega
            exact Rat.le_trans (ih (by omega)) (superpositionProb_step_nonneg hp0 hp1 hk)
      exact Rat.le_trans hstep hind
  | n + 1, m, hnm => by
      induction m with
      | zero => omega
      | succ k ih =>
          by_cases heq : n + 1 = k + 1
          · rw [heq]; exact Rat.le_refl
          · have hle : n + 1 ≤ k := by omega
            exact Rat.le_trans (ih hle) (superpositionProb_step_nonneg hp0 hp1 (by omega))

theorem superpositionProb_nonneg {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : Nat) :
    0 ≤ superpositionProb p n := by
  have h := superpositionProb_mono hp0 hp1 (Nat.zero_le n)
  simpa using h

theorem superpositionProb_le_one {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : Nat) :
    superpositionProb p n ≤ 1 := by
  unfold superpositionProb
  split
  · decide
  · have h1 : 0 ≤ powRat (1 - p) n := powRat_nonneg (by grind) n
    have h2 : 0 ≤ powRat (1 - p) (n - 1) := powRat_nonneg (by grind) (n - 1)
    have hn : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
    have hterm : 0 ≤ (n : Rat) * p * powRat (1 - p) (n - 1) :=
      Rat.mul_nonneg (Rat.mul_nonneg hn hp0) h2
    grind

theorem superpositionProb_strict_step {p : Rat} (hp0 : 0 < p) (hp1 : p < 1)
    {n : Nat} (hn : 1 ≤ n) :
    superpositionProb p n < superpositionProb p (n + 1) := by
  have hdiff := superpositionProb_step p n hn
  have hq : 0 < powRat (1 - p) (n - 1) := powRat_pos (by grind) (n - 1)
  have hn0 : (0 : Rat) < (n : Rat) := by
    have : 0 < n := by omega
    exact Rat.natCast_pos.mpr this
  have hpp : 0 < p * p := Rat.mul_pos hp0 hp0
  have hm1 : 0 < (n : Rat) * (p * p) := Rat.mul_pos hn0 hpp
  have hm2 : 0 < (n : Rat) * (p * p) * powRat (1 - p) (n - 1) := Rat.mul_pos hm1 hq
  grind

/-- Conditional monotonicity theorem: if option count `nOfA` is nondecreasing
    in attractiveness `A`, then `superpositionProb p (nOfA A)` is nondecreasing in `A`.
    (Mathematical property of the Binomial model, separate from the empirical hypothesis
    that attractiveness increases option count.) -/
theorem conjecture_mono_in_attractiveness {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (nOfA : Rat → Nat) (hA : ∀ A₁ A₂ : Rat, A₁ ≤ A₂ → nOfA A₁ ≤ nOfA A₂)
    {A₁ A₂ : Rat} (hle : A₁ ≤ A₂) :
    superpositionProb p (nOfA A₁) ≤ superpositionProb p (nOfA A₂) :=
  superpositionProb_mono hp0 hp1 (hA A₁ A₂ hle)

end RST
