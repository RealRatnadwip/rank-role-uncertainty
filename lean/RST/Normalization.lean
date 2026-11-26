/-
  Finite-dimensional weight vectors, amplitude normalization,
  and post-removal renormalization for Relational Superposition Theory.
-/

namespace RST

/-- Sum of a finite rational-valued function `Fin n → Rat`. -/
def sumFin : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | _ + 1, f => f 0 + sumFin (fun i => f i.succ)

@[simp] theorem sumFin_zero (f : Fin 0 → Rat) : sumFin f = 0 := rfl

@[simp] theorem sumFin_succ {n : Nat} (f : Fin (n + 1) → Rat) :
    sumFin f = f 0 + sumFin (fun i => f i.succ) := rfl

theorem rat_sq_nonneg (x : Rat) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hneg : 0 ≤ -x := by grind
    have hprod : (-x) * (-x) = x * x := by grind
    rw [← hprod]
    exact Rat.mul_nonneg hneg hneg

theorem rat_sq_pos {x : Rat} (hx : x ≠ 0) : 0 < x * x := by
  have hge := rat_sq_nonneg x
  have hne : x * x ≠ 0 := by grind
  grind

theorem rat_div_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  have hinv : 0 < b⁻¹ := by
    by_cases h : b⁻¹ ≤ 0
    · have : b * b⁻¹ ≤ 0 := by
        have h1 : b * b⁻¹ ≤ b * 0 := Rat.mul_le_mul_of_nonneg_left h (by grind)
        grind
      have hmul : b * b⁻¹ = 1 := Rat.mul_inv_cancel b (by grind)
      grind
    · grind
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (by grind)

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

/-- A normalized probability weight distribution over `n` partners. -/
structure Weights (n : Nat) where
  w : Fin n → Rat
  nonneg : ∀ i, 0 ≤ w i
  sum_one : sumFin w = 1

/-- A unit-norm real amplitude vector over `n` partners. -/
structure Amplitudes (n : Nat) where
  a : Fin n → Rat
  unit_norm : sumFin (fun i => a i * a i) = 1

/-- Squared amplitudes form a valid collapse probability distribution. -/
def Amplitudes.toWeights {n : Nat} (A : Amplitudes n) : Weights n where
  w := fun i => A.a i * A.a i
  nonneg := fun i => rat_sq_nonneg (A.a i)
  sum_one := A.unit_norm

theorem collapse_probs_sum_one {n : Nat} (A : Amplitudes n) :
    sumFin A.toWeights.w = 1 :=
  A.unit_norm

/-- Weight vector obtained after removing partner `k` and renormalizing. -/
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

/-- Packaged valid `Weights n` distribution after removing partner `k`. -/
def renormAfterRemoval {n : Nat} (W : Weights n) (k : Fin n) (hk : W.w k < 1) :
    Weights n where
  w := removePartner W k
  nonneg := removePartner_nonneg W k hk
  sum_one := removePartner_sum_one W k hk

/-- Generalized renormalization over an arbitrary retained subset `keep`. -/
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
