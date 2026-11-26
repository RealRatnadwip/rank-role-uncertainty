/-
  Finite-index summation, double-sum swapping, and counting helpers over `Fin n`.
-/

namespace RST

/-- Sum of a finite rational-valued function `Fin n → Rat`. -/
def sumFin : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | _ + 1, f => f 0 + sumFin (fun i => f i.succ)

@[simp] theorem sumFin_zero (f : Fin 0 → Rat) : sumFin f = 0 := rfl

@[simp] theorem sumFin_succ {n : Nat} (f : Fin (n + 1) → Rat) :
    sumFin f = f 0 + sumFin (fun i => f i.succ) := rfl

theorem sumFin_zero_fun : ∀ {d : Nat}, sumFin (fun _ : Fin d => (0 : Rat)) = 0
  | 0 => rfl
  | k + 1 => by
      simp only [sumFin_succ]
      rw [sumFin_zero_fun (d := k)]
      grind

theorem sumFin_add : ∀ {n : Nat} (f g : Fin n → Rat),
    sumFin (fun i => f i + g i) = sumFin f + sumFin g
  | 0, _, _ => by simp; grind
  | n + 1, f, g => by
      have ih := sumFin_add (n := n) (fun i => f i.succ) (fun i => g i.succ)
      simp only [sumFin_succ]
      grind

theorem sumFin_sub : ∀ {n : Nat} (f g : Fin n → Rat),
    sumFin (fun i => f i - g i) = sumFin f - sumFin g
  | 0, _, _ => by simp; grind
  | n + 1, f, g => by
      have ih := sumFin_sub (n := n) (fun i => f i.succ) (fun i => g i.succ)
      simp only [sumFin_succ]
      grind

theorem sumFin_smul : ∀ {n : Nat} (c : Rat) (f : Fin n → Rat),
    sumFin (fun i => c * f i) = c * sumFin f
  | 0, c, _ => by simp
  | n + 1, c, f => by
      have ih := sumFin_smul (n := n) c (fun i => f i.succ)
      simp only [sumFin_succ]
      grind

theorem sumFin_div_const {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumFin (fun i => f i / c) = sumFin f / c := by
  have h1 : (fun i => f i / c) = (fun i => c⁻¹ * f i) := by
    funext i
    rw [Rat.div_def, Rat.mul_comm]
  rw [h1, sumFin_smul, Rat.mul_comm, ← Rat.div_def]

theorem sumFin_nonneg : ∀ {n : Nat} (f : Fin n → Rat),
    (∀ i, 0 ≤ f i) → 0 ≤ sumFin f
  | 0, _, _ => by simp
  | n + 1, f, h => by
      have h0 : 0 ≤ f 0 := h 0
      have hrest : 0 ≤ sumFin (fun i => f i.succ) :=
        sumFin_nonneg (n := n) (fun i => f i.succ) (fun i => h i.succ)
      simp only [sumFin_succ]
      grind

theorem sumFin_le_sumFin : ∀ {n : Nat} (f g : Fin n → Rat),
    (∀ i, f i ≤ g i) → sumFin f ≤ sumFin g
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
      have h0 : f 0 ≤ g 0 := h 0
      have hrest : sumFin (fun i => f i.succ) ≤ sumFin (fun i => g i.succ) :=
        sumFin_le_sumFin (n := n) (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)
      simp only [sumFin_succ]
      grind

theorem elem_le_sumFin : ∀ {n : Nat} (f : Fin n → Rat),
    (∀ i, 0 ≤ f i) → ∀ k : Fin n, f k ≤ sumFin f
  | 0, _, _, k => Fin.elim0 k
  | n + 1, f, h, k => by
      refine Fin.cases ?_ ?_ k
      · simp only [sumFin_succ]
        have hrest := sumFin_nonneg (n := n) (fun i => f i.succ) (fun i => h i.succ)
        grind
      · intro j
        simp only [sumFin_succ]
        have ih := elem_le_sumFin (n := n) (fun i => f i.succ) (fun i => h i.succ) j
        have h0 : 0 ≤ f 0 := h 0
        grind

theorem sumFin_eq_zero_of_nonneg : ∀ {n : Nat} (f : Fin n → Rat),
    (∀ i, 0 ≤ f i) → sumFin f = 0 → ∀ i, f i = 0
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, f, h, hsum, i => by
      simp only [sumFin_succ] at hsum
      have h0 : 0 ≤ f 0 := h 0
      have hrest : 0 ≤ sumFin (fun j => f j.succ) :=
        sumFin_nonneg (n := n) (fun j => f j.succ) (fun j => h j.succ)
      have hf0 : f 0 = 0 := by grind
      have hrest0 : sumFin (fun j => f j.succ) = 0 := by grind
      refine Fin.cases hf0 ?_ i
      intro j
      exact sumFin_eq_zero_of_nonneg (n := n) (fun k => f k.succ) (fun k => h k.succ) hrest0 j

theorem sumFin_zero_single : ∀ {n : Nat} (f : Fin n → Rat) (k : Fin n),
    sumFin (fun i => if i = k then 0 else f i) + f k = sumFin f
  | 0, _, k => Fin.elim0 k
  | n + 1, f, k => by
      refine Fin.cases ?_ ?_ k
      · simp only [sumFin_succ, ↓reduceIte]
        have hfun : (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then 0 else f i.succ) =
            (fun i => f i.succ) := by
          funext i
          simp [Fin.succ_ne_zero]
        rw [hfun]
        grind
      · intro j
        simp only [sumFin_succ]
        have h0 : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
        simp only [h0, ↓reduceIte]
        have hsub : (fun i : Fin n => if i.succ = j.succ then 0 else f i.succ) =
            (fun i => if i = j then 0 else f i.succ) := by
          funext i
          simp [Fin.succ_inj]
        rw [hsub]
        have ih := sumFin_zero_single (n := n) (fun i => f i.succ) j
        grind

theorem sumFin_swap : ∀ {m n : Nat} (F : Fin m → Fin n → Rat),
    sumFin (fun i => sumFin (fun j => F i j)) =
      sumFin (fun j => sumFin (fun i => F i j))
  | 0, n, F => by
      simp only [sumFin_zero]
      induction n with
      | zero => simp
      | succ k ih =>
          simp only [sumFin_succ]
          have h := ih (fun i j => F i j.succ)
          grind
  | m + 1, n, F => by
      simp only [sumFin_succ]
      have ih := sumFin_swap (m := m) (n := n) (fun i j => F i.succ j)
      rw [ih, ← sumFin_add]

/-- Count how many indices in `Fin n` satisfy a boolean predicate `p`. -/
def countFin : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | _ + 1, p => (if p 0 then 1 else 0) + countFin (fun i => p i.succ)

@[simp] theorem countFin_zero (p : Fin 0 → Bool) : countFin p = 0 := rfl

@[simp] theorem countFin_succ {n : Nat} (p : Fin (n + 1) → Bool) :
    countFin p = (if p 0 then 1 else 0) + countFin (fun i => p i.succ) := rfl

theorem countFin_le_len : ∀ {n : Nat} (p : Fin n → Bool), countFin p ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, p => by
      simp only [countFin_succ]
      have ih := countFin_le_len (n := n) (fun i => p i.succ)
      cases hp : p 0
      · simp_all; omega
      · simp_all; omega

theorem countFin_pos_of_true : ∀ {n : Nat} (p : Fin n → Bool) (k : Fin n),
    p k = true → 0 < countFin p
  | 0, _, k, _ => Fin.elim0 k
  | n + 1, p, k, hk => by
      revert hk
      refine Fin.cases ?_ ?_ k
      · intro h0
        simp [countFin_succ, h0]
        omega
      · intro j hj
        have ih := countFin_pos_of_true (n := n) (fun i => p i.succ) j hj
        simp only [countFin_succ]
        omega

theorem countFin_ge_two_of_two_true : ∀ {n : Nat} (p : Fin n → Bool) (i j : Fin n),
    i ≠ j → p i = true → p j = true → 2 ≤ countFin p
  | 0, _, i, _, _, _, _ => Fin.elim0 i
  | n + 1, p, i, j, hij, hi, hj => by
      revert hij hi hj
      refine Fin.cases ?_ ?_ i
      · intro hij hi0 hj
        revert hij hj
        refine Fin.cases ?_ ?_ j
        · intro hne _; exact absurd rfl hne
        · intro j' _ hj'
          have h1 := countFin_pos_of_true (fun k => p k.succ) j' hj'
          simp [countFin_succ, hi0]
          omega
      · intro i' hij hi' hj
        revert hij hi' hj
        refine Fin.cases ?_ ?_ j
        · intro _ hi' hj0
          have h1 := countFin_pos_of_true (fun k => p k.succ) i' hi'
          simp [countFin_succ, hj0]
          omega
        · intro j' hij hi' hj'
          have hne : i' ≠ j' := fun h => hij (congrArg Fin.succ h)
          have ih := countFin_ge_two_of_two_true (n := n) (fun k => p k.succ) i' j' hne hi' hj'
          simp only [countFin_succ]
          omega

end RST
