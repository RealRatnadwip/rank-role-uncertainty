/-
  Formalization of the Attractiveness-Optionality Conjecture retention model:
  monotonicity of superposition probability in the viable option count `n`
  and in perceived attractiveness `A`.
-/

namespace RST

/-- Rational power by structural recursion on `Nat`. -/
def powRat (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => x * powRat x n

@[simp] theorem powRat_zero (x : Rat) : powRat x 0 = 1 := rfl
@[simp] theorem powRat_succ (x : Rat) (n : Nat) : powRat x (n + 1) = x * powRat x n := rfl

theorem natCast_rat_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) :=
  Rat.natCast_nonneg

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

theorem powRat_le_one {x : Rat} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ∀ n : Nat, powRat x n ≤ 1
  | 0 => by simp
  | n + 1 => by
      simp only [powRat_succ]
      have h1 := powRat_le_one hx0 hx1 n
      have h0 := powRat_nonneg hx0 n
      have hmul : x * powRat x n ≤ 1 * powRat x n :=
        Rat.mul_le_mul_of_nonneg_right hx1 h0
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

/-- Exact discrete marginal gain from adding one viable partner (`n ≥ 1`). -/
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
  have hn0 : (0 : Rat) ≤ (n : Rat) := natCast_rat_nonneg n
  have hpp : 0 ≤ p * p := Rat.mul_nonneg hp0 hp0
  have hm1 : 0 ≤ (n : Rat) * (p * p) := Rat.mul_nonneg hn0 hpp
  have hm2 : 0 ≤ (n : Rat) * (p * p) * powRat (1 - p) (n - 1) := Rat.mul_nonneg hm1 hq
  grind

/-- Monotonicity: superposition probability is nondecreasing in partner count `n`. -/
theorem superpositionProb_mono {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ {n m : Nat}, n ≤ m → superpositionProb p n ≤ superpositionProb p m
  | 0, 0, _ => by simp
  | 0, m + 1, _ => by
      have hstep : superpositionProb p 0 ≤ superpositionProb p 1 := by
        simp
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
    have hn : (0 : Rat) ≤ (n : Rat) := natCast_rat_nonneg n
    have hterm : 0 ≤ (n : Rat) * p * powRat (1 - p) (n - 1) :=
      Rat.mul_nonneg (Rat.mul_nonneg hn hp0) h2
    grind

/-- Strict monotonicity when `0 < p < 1` and `n ≥ 1`. -/
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

/-- Attractiveness-Optionality composition theorem: if viable partner count `nOfA`
    is nondecreasing in attractiveness `A`, superposition probability is nondecreasing
    in `A`. -/
theorem conjecture_mono_in_attractiveness {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (nOfA : Rat → Nat) (hA : ∀ A₁ A₂ : Rat, A₁ ≤ A₂ → nOfA A₁ ≤ nOfA A₂)
    {A₁ A₂ : Rat} (hle : A₁ ≤ A₂) :
    superpositionProb p (nOfA A₁) ≤ superpositionProb p (nOfA A₂) :=
  superpositionProb_mono hp0 hp1 (hA A₁ A₂ hle)

end RST
