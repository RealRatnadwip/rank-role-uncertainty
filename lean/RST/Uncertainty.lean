/-
  Machine-checked Rank-Role Uncertainty Inequality on finite-dimensional
  complex inner-product spaces over the Gaussian rationals Q[i].
  Proves Cauchy-Schwarz, Hermitian expectation reality, commutator identity,
  and 4 * var R psi * var L psi >= (Im <psi | [R, L] psi>)^2.
-/

import RST.Normalization

namespace RST

/-- Gaussian rational number `re + i * im` over `Rat`. -/
structure Cpx where
  re : Rat
  im : Rat
  deriving DecidableEq, Repr

namespace Cpx

def zero : Cpx := ⟨0, 0⟩
def one : Cpx := ⟨1, 0⟩
def ofRat (r : Rat) : Cpx := ⟨r, 0⟩
def conj (z : Cpx) : Cpx := ⟨z.re, -z.im⟩
def add (a b : Cpx) : Cpx := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : Cpx) : Cpx := ⟨a.re - b.re, a.im - b.im⟩
def neg (a : Cpx) : Cpx := ⟨-a.re, -a.im⟩
def mul (a b : Cpx) : Cpx := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def normSq (z : Cpx) : Rat := z.re * z.re + z.im * z.im

instance : Zero Cpx := ⟨zero⟩
instance : One Cpx := ⟨one⟩
instance : Add Cpx := ⟨add⟩
instance : Sub Cpx := ⟨sub⟩
instance : Neg Cpx := ⟨neg⟩
instance : Mul Cpx := ⟨mul⟩

@[ext] theorem ext {a b : Cpx} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; cases hre; cases him; rfl

@[simp] theorem zero_re : (0 : Cpx).re = 0 := rfl
@[simp] theorem zero_im : (0 : Cpx).im = 0 := rfl
@[simp] theorem ofRat_re (r : Rat) : (ofRat r).re = r := rfl
@[simp] theorem ofRat_im (r : Rat) : (ofRat r).im = 0 := rfl
@[simp] theorem conj_re (z : Cpx) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : Cpx) : (conj z).im = -z.im := rfl
@[simp] theorem add_re (a b : Cpx) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : Cpx) : (a + b).im = a.im + b.im := rfl
@[simp] theorem sub_re (a b : Cpx) : (a - b).re = a.re - b.re := rfl
@[simp] theorem sub_im (a b : Cpx) : (a - b).im = a.im - b.im := rfl
@[simp] theorem neg_re (a : Cpx) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : Cpx) : (-a).im = -a.im := rfl
@[simp] theorem mul_re (a b : Cpx) : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] theorem mul_im (a b : Cpx) : (a * b).im = a.re * b.im + a.im * b.re := rfl

theorem normSq_nonneg (z : Cpx) : 0 ≤ normSq z := by
  unfold normSq
  have h1 := rat_sq_nonneg z.re
  have h2 := rat_sq_nonneg z.im
  grind

theorem normSq_eq_zero {z : Cpx} (h : normSq z = 0) : z = 0 := by
  unfold normSq at h
  have h1 := rat_sq_nonneg z.re
  have h2 := rat_sq_nonneg z.im
  have hre0 : z.re * z.re = 0 := by grind
  have him0 : z.im * z.im = 0 := by grind
  have hre : z.re = 0 := by grind
  have him : z.im = 0 := by grind
  exact ext hre him

theorem im_sq_le_normSq (z : Cpx) : z.im * z.im ≤ normSq z := by
  unfold normSq
  have h1 := rat_sq_nonneg z.re
  grind

end Cpx

open Cpx

/-- Finite sum swap for double sums over `Fin m` and `Fin n`. -/
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

/-- Complex inner product `⟨u, v⟩ = ∑ k, conj(u k) * v k`. -/
def dotC {d : Nat} (u v : Fin d → Cpx) : Cpx :=
  ⟨sumFin (fun k => (conj (u k) * v k).re),
   sumFin (fun k => (conj (u k) * v k).im)⟩

/-- Squared Euclidean norm `‖u‖² = ∑ k, normSq (u k)`. -/
def normSqC {d : Nat} (u : Fin d → Cpx) : Rat :=
  sumFin (fun k => normSq (u k))

theorem normSqC_nonneg {d : Nat} (u : Fin d → Cpx) : 0 ≤ normSqC u :=
  sumFin_nonneg _ (fun k => Cpx.normSq_nonneg (u k))

theorem dotC_self_re {d : Nat} (u : Fin d → Cpx) : (dotC u u).re = normSqC u := by
  unfold dotC normSqC normSq
  simp [Cpx.mul_re, Cpx.conj_re, Cpx.conj_im]
  congr 1
  funext k
  grind

theorem sumFin_zero_fun : ∀ {d : Nat}, sumFin (fun _ : Fin d => (0 : Rat)) = 0
  | 0 => rfl
  | k + 1 => by
      simp only [sumFin_succ]
      rw [sumFin_zero_fun (d := k)]
      grind

theorem dotC_self_im {d : Nat} (u : Fin d → Cpx) : (dotC u u).im = 0 := by
  unfold dotC
  simp [Cpx.mul_im, Cpx.conj_re, Cpx.conj_im]
  have hzero : (fun k : Fin d => (u k).re * (u k).im + -(u k).im * (u k).re) = fun _ => 0 := by
    funext k; grind
  rw [hzero]
  exact sumFin_zero_fun

theorem dotC_conj {d : Nat} (u v : Fin d → Cpx) :
    dotC u v = conj (dotC v u) := by
  apply Cpx.ext
  · simp [dotC, Cpx.mul_re, Cpx.conj_re, Cpx.conj_im]
    congr 1; funext k; grind
  · simp [dotC, Cpx.mul_im, Cpx.conj_re, Cpx.conj_im]
    have h1 : (fun k : Fin d => (u k).re * (v k).im + -(u k).im * (v k).re) =
        (fun k => -((v k).re * (u k).im + -(v k).im * (u k).re)) := by
      funext k; grind
    rw [h1]
    have hsm := sumFin_smul (-1 : Rat) (fun k : Fin d => (v k).re * (u k).im + -(v k).im * (u k).re)
    have h2 : (fun k : Fin d => -((v k).re * (u k).im + -(v k).im * (u k).re)) =
        (fun k => (-1 : Rat) * ((v k).re * (u k).im + -(v k).im * (u k).re)) := by
      funext k; grind
    rw [h2, hsm]; grind

theorem dotC_add_right {d : Nat} (u v w : Fin d → Cpx) :
    dotC u (fun k => v k + w k) = dotC u v + dotC u w := by
  apply Cpx.ext
  · simp [dotC, Cpx.mul_re, Cpx.add_re, Cpx.add_im]
    have h : (fun k : Fin d => (u k).re * ((v k).re + (w k).re) - -(u k).im * ((v k).im + (w k).im)) =
        (fun k => ((u k).re * (v k).re - -(u k).im * (v k).im) +
                   ((u k).re * (w k).re - -(u k).im * (w k).im)) := by
      funext k; grind
    rw [h, sumFin_add]
  · simp [dotC, Cpx.mul_im, Cpx.add_re, Cpx.add_im]
    have h : (fun k : Fin d => (u k).re * ((v k).im + (w k).im) + -(u k).im * ((v k).re + (w k).re)) =
        (fun k => ((u k).re * (v k).im + -(u k).im * (v k).re) +
                   ((u k).re * (w k).im + -(u k).im * (w k).re)) := by
      funext k; grind
    rw [h, sumFin_add]

theorem dotC_sub_right {d : Nat} (u v w : Fin d → Cpx) :
    dotC u (fun k => v k - w k) = dotC u v - dotC u w := by
  apply Cpx.ext
  · simp [dotC, Cpx.mul_re, Cpx.sub_re, Cpx.sub_im]
    have h : (fun k : Fin d => (u k).re * ((v k).re - (w k).re) - -(u k).im * ((v k).im - (w k).im)) =
        (fun k => ((u k).re * (v k).re - -(u k).im * (v k).im) -
                   ((u k).re * (w k).re - -(u k).im * (w k).im)) := by
      funext k; grind
    rw [h, sumFin_sub]
  · simp [dotC, Cpx.mul_im, Cpx.sub_re, Cpx.sub_im]
    have h : (fun k : Fin d => (u k).re * ((v k).im - (w k).im) + -(u k).im * ((v k).re - (w k).re)) =
        (fun k => ((u k).re * (v k).im + -(u k).im * (v k).re) -
                   ((u k).re * (w k).im + -(u k).im * (w k).re)) := by
      funext k; grind
    rw [h, sumFin_sub]

theorem dotC_sub_left {d : Nat} (u v w : Fin d → Cpx) :
    dotC (fun k => u k - v k) w = dotC u w - dotC v w := by
  have h := dotC_sub_right w u v
  rw [dotC_conj (fun k => u k - v k) w, h, dotC_conj w u, dotC_conj w v]
  apply Cpx.ext <;> simp <;> grind

theorem dotC_smul_right {d : Nat} (c : Cpx) (u v : Fin d → Cpx) :
    dotC u (fun k => c * v k) = c * dotC u v := by
  apply Cpx.ext
  · simp [dotC, Cpx.mul_re, Cpx.mul_im, Cpx.conj_re, Cpx.conj_im]
    have h1 : (fun k : Fin d => (u k).re * (c.re * (v k).re - c.im * (v k).im) -
        -(u k).im * (c.re * (v k).im + c.im * (v k).re)) =
      (fun k => c.re * ((u k).re * (v k).re - -(u k).im * (v k).im) +
        (-c.im) * ((u k).re * (v k).im + -(u k).im * (v k).re)) := by
      funext k; grind
    rw [h1, sumFin_add, sumFin_smul, sumFin_smul]; grind
  · simp [dotC, Cpx.mul_re, Cpx.mul_im, Cpx.conj_re, Cpx.conj_im]
    have h1 : (fun k : Fin d => (u k).re * (c.re * (v k).im + c.im * (v k).re) +
        -(u k).im * (c.re * (v k).re - c.im * (v k).im)) =
      (fun k => c.re * ((u k).re * (v k).im + -(u k).im * (v k).re) +
        c.im * ((u k).re * (v k).re - -(u k).im * (v k).im)) := by
      funext k; grind
    rw [h1, sumFin_add, sumFin_smul, sumFin_smul]

theorem dotC_smul_left {d : Nat} (c : Cpx) (u v : Fin d → Cpx) :
    dotC (fun k => c * u k) v = conj c * dotC u v := by
  rw [dotC_conj (fun k => c * u k) v, dotC_smul_right c v u, dotC_conj v u]
  apply Cpx.ext
  · simp; grind
  · simp; grind

/-- Complex Cauchy-Schwarz inequality in `Q[i]^d`:
    `normSq ⟨u, v⟩ ≤ ‖u‖² * ‖v‖²`. -/
theorem cauchy_schwarz_cpx {d : Nat} (u v : Fin d → Cpx) :
    normSq (dotC u v) ≤ normSqC u * normSqC v := by
  let s := normSqC v
  by_cases hs : s = 0
  · have hzero : ∀ k : Fin d, v k = 0 := by
      intro k
      exact Cpx.normSq_eq_zero (sumFin_eq_zero_of_nonneg _ (fun i => Cpx.normSq_nonneg (v i)) hs k)
    have hdot : dotC u v = 0 := by
      apply Cpx.ext
      · simp only [dotC, hzero, zero_re, zero_im, Cpx.mul_re, Cpx.conj_re, Cpx.conj_im]
        have hsub0 : (fun k : Fin d => (u k).re * 0 - -(u k).im * 0) = fun _ => 0 := by
          funext k; grind
        rw [hsub0]
        exact sumFin_zero_fun
      · simp only [dotC, hzero, zero_re, zero_im, Cpx.mul_im, Cpx.conj_re, Cpx.conj_im]
        have hadd0 : (fun k : Fin d => (u k).re * 0 + -(u k).im * 0) = fun _ => 0 := by
          funext k; grind
        rw [hadd0]
        exact sumFin_zero_fun
    rw [hdot]
    have hs0 : normSqC v = 0 := hs
    rw [hs0]
    simp [normSq]; grind
  · have hs_nonneg : 0 ≤ s := normSqC_nonneg v
    have hs_pos : 0 < s := by grind
    let c := dotC v u
    let w : Fin d → Cpx := fun k => ofRat s * u k - c * v k
    have hw_nonneg : 0 ≤ (dotC w w).re := by
      rw [dotC_self_re]
      exact normSqC_nonneg w
    have h1 : dotC w u = ofRat s * dotC u u - conj c * dotC v u := by
      dsimp [w]
      rw [dotC_sub_left, dotC_smul_left, dotC_smul_left]
      simp [conj, ofRat]
    have h2 : dotC w v = ofRat s * dotC u v - conj c * dotC v v := by
      dsimp [w]
      rw [dotC_sub_left, dotC_smul_left, dotC_smul_left]
      simp [conj, ofRat]
    have hdot_w : dotC w w = ofRat s * dotC w u - c * dotC w v := by
      dsimp [w]
      rw [dotC_sub_right, dotC_smul_right, dotC_smul_right]
    rw [h1, h2] at hdot_w
    have huu : dotC u u = ofRat (normSqC u) := Cpx.ext (dotC_self_re u) (dotC_self_im u)
    have hvv : dotC v v = ofRat s := Cpx.ext (dotC_self_re v) (dotC_self_im v)
    have hc_conj : conj c = dotC u v := (dotC_conj u v).symm
    rw [huu, hvv, hc_conj] at hdot_w
    have hexpand : (dotC w w).re = s * (normSqC u * s - normSq (dotC u v)) := by
      rw [hdot_w]
      have hre : (dotC v u).re = (dotC u v).re := by rw [dotC_conj v u]; rfl
      have him : (dotC v u).im = -(dotC u v).im := by rw [dotC_conj v u]; rfl
      simp [c, normSq, hre, him]
      grind
    rw [hexpand] at hw_nonneg
    have hge : normSq (dotC u v) ≤ normSqC u * s := by
      by_cases hle : normSq (dotC u v) ≤ normSqC u * s
      · exact hle
      · have hneg : normSqC u * s - normSq (dotC u v) < 0 := by grind
        have hprod : s * (normSqC u * s - normSq (dotC u v)) < s * 0 :=
          Rat.mul_lt_mul_of_pos_left hneg hs_pos
        rw [Rat.mul_zero] at hprod
        grind
    exact hge

/-- Matrix of Gaussian rationals acting on `Fin d → Cpx`. -/
abbrev Mat (d : Nat) := Fin d → Fin d → Cpx

def mulMat {d : Nat} (M : Mat d) (ψ : Fin d → Cpx) (i : Fin d) : Cpx :=
  ⟨sumFin (fun j => (M i j * ψ j).re), sumFin (fun j => (M i j * ψ j).im)⟩

def IsHermitian {d : Nat} (M : Mat d) : Prop :=
  ∀ i j : Fin d, M j i = conj (M i j)

theorem dotC_hermitian {d : Nat} (M : Mat d) (hM : IsHermitian M) (u v : Fin d → Cpx) :
    dotC u (mulMat M v) = dotC (mulMat M u) v := by
  apply Cpx.ext
  · simp only [dotC, mulMat, Cpx.mul_re, Cpx.mul_im, Cpx.conj_re, Cpx.conj_im]
    have hL : (fun i : Fin d => (u i).re * sumFin (fun j => (M i j).re * (v j).re - (M i j).im * (v j).im) -
        -(u i).im * sumFin (fun j => (M i j).re * (v j).im + (M i j).im * (v j).re)) =
      (fun i => sumFin (fun j =>
        (u i).re * ((M i j).re * (v j).re - (M i j).im * (v j).im) -
        -(u i).im * ((M i j).re * (v j).im + (M i j).im * (v j).re))) := by
      funext i
      rw [← sumFin_smul, ← sumFin_smul, ← sumFin_sub]
    rw [hL, sumFin_swap]
    congr 1
    funext j
    have hR : (sumFin (fun i => (M j i).re * (u i).re - (M j i).im * (u i).im) * (v j).re -
        -sumFin (fun i => (M j i).re * (u i).im + (M j i).im * (u i).re) * (v j).im) =
      sumFin (fun i =>
        ((M j i).re * (u i).re - (M j i).im * (u i).im) * (v j).re -
        -((M j i).re * (u i).im + (M j i).im * (u i).re) * (v j).im) := by
      rw [Rat.mul_comm _ (v j).re, Rat.mul_comm _ (v j).im, Rat.mul_neg]
      rw [← sumFin_smul, ← sumFin_smul]
      have hneg : -(sumFin (fun i => (v j).im * ((M j i).re * (u i).im + (M j i).im * (u i).re))) =
          sumFin (fun i => -((v j).im * ((M j i).re * (u i).im + (M j i).im * (u i).re))) := by
        have hs := sumFin_smul (-1 : Rat) (fun i => (v j).im * ((M j i).re * (u i).im + (M j i).im * (u i).re))
        have hfun : (fun i : Fin d => -((v j).im * ((M j i).re * (u i).im + (M j i).im * (u i).re))) =
            (fun i => (-1 : Rat) * ((v j).im * ((M j i).re * (u i).im + (M j i).im * (u i).re))) := by
          funext i; grind
        rw [hfun, hs]; grind
      have hfin : (fun i : Fin d =>
          ((M j i).re * (u i).re - (M j i).im * (u i).im) * (v j).re -
          -((M j i).re * (u i).im + (M j i).im * (u i).re) * (v j).im) =
        (fun i => (v j).re * ((M j i).re * (u i).re - (M j i).im * (u i).im) +
          ((v j).im * ((M j i).re * (u i).im + (M j i).im * (u i).re))) := by
        funext i; grind
      rw [hfin, Rat.sub_eq_add_neg, Rat.neg_neg, ← sumFin_add]
    rw [hR]
    congr 1
    funext i
    have hij := hM i j
    have hre : (M j i).re = (M i j).re := by rw [hij]; rfl
    have him : (M j i).im = -(M i j).im := by rw [hij]; rfl
    rw [hre, him]
    grind
  · simp only [dotC, mulMat, Cpx.mul_re, Cpx.mul_im, Cpx.conj_re, Cpx.conj_im]
    have hL : (fun i : Fin d => (u i).re * sumFin (fun j => (M i j).re * (v j).im + (M i j).im * (v j).re) +
        -(u i).im * sumFin (fun j => (M i j).re * (v j).re - (M i j).im * (v j).im)) =
      (fun i => sumFin (fun j =>
        (u i).re * ((M i j).re * (v j).im + (M i j).im * (v j).re) +
        -(u i).im * ((M i j).re * (v j).re - (M i j).im * (v j).im))) := by
      funext i
      rw [← sumFin_smul, ← sumFin_smul, ← sumFin_add]
    rw [hL, sumFin_swap]
    congr 1
    funext j
    have hR : (sumFin (fun i => (M j i).re * (u i).re - (M j i).im * (u i).im) * (v j).im +
        -sumFin (fun i => (M j i).re * (u i).im + (M j i).im * (u i).re) * (v j).re) =
      sumFin (fun i =>
        ((M j i).re * (u i).re - (M j i).im * (u i).im) * (v j).im +
        -((M j i).re * (u i).im + (M j i).im * (u i).re) * (v j).re) := by
      rw [Rat.mul_comm _ (v j).im, Rat.mul_comm _ (v j).re, Rat.mul_neg]
      rw [← sumFin_smul, ← sumFin_smul]
      have hfin : (fun i : Fin d =>
          ((M j i).re * (u i).re - (M j i).im * (u i).im) * (v j).im +
          -((M j i).re * (u i).im + (M j i).im * (u i).re) * (v j).re) =
        (fun i => (v j).im * ((M j i).re * (u i).re - (M j i).im * (u i).im) -
          (v j).re * ((M j i).re * (u i).im + (M j i).im * (u i).re)) := by
        funext i; grind
      rw [hfin, ← Rat.sub_eq_add_neg, ← sumFin_sub]
    rw [hR]
    congr 1
    funext i
    have hij := hM i j
    have hre : (M j i).re = (M i j).re := by rw [hij]; rfl
    have him : (M j i).im = -(M i j).im := by rw [hij]; rfl
    rw [hre, him]
    grind

def expVal {d : Nat} (M : Mat d) (ψ : Fin d → Cpx) : Rat :=
  (dotC ψ (mulMat M ψ)).re

theorem dotC_hermitian_self_im {d : Nat} (M : Mat d) (hM : IsHermitian M) (ψ : Fin d → Cpx) :
    (dotC ψ (mulMat M ψ)).im = 0 := by
  have h1 := dotC_hermitian M hM ψ ψ
  have h2 := dotC_conj ψ (mulMat M ψ)
  rw [h1] at h2
  have him : (dotC (mulMat M ψ) ψ).im = -(dotC (mulMat M ψ) ψ).im := by
    have := congrArg Cpx.im h2
    simpa [Cpx.conj_im] using this
  rw [← h1] at him
  grind

def centered {d : Nat} (M : Mat d) (ψ : Fin d → Cpx) : Fin d → Cpx :=
  fun i => mulMat M ψ i - ofRat (expVal M ψ) * ψ i

def var {d : Nat} (M : Mat d) (ψ : Fin d → Cpx) : Rat :=
  normSqC (centered M ψ)

def comm {d : Nat} (R L : Mat d) (ψ : Fin d → Cpx) : Fin d → Cpx :=
  fun i => mulMat R (mulMat L ψ) i - mulMat L (mulMat R ψ) i

theorem centered_comm_im {d : Nat} (R L : Mat d) (hR : IsHermitian R) (hL : IsHermitian L)
    (ψ : Fin d → Cpx) :
    2 * (dotC (centered R ψ) (centered L ψ)).im = (dotC ψ (comm R L ψ)).im := by
  let r := expVal R ψ
  let l := expVal L ψ
  have h1 : dotC (centered R ψ) (centered L ψ) =
      dotC (mulMat R ψ) (mulMat L ψ)
        - ofRat l * dotC (mulMat R ψ) ψ
        - ofRat r * dotC ψ (mulMat L ψ)
        + ofRat r * (ofRat l * dotC ψ ψ) := by
    unfold centered
    rw [dotC_sub_right, dotC_sub_left, dotC_sub_left]
    rw [dotC_smul_right, dotC_smul_right, dotC_smul_left, dotC_smul_left]
    simp only [conj, Cpx.ofRat_re, Cpx.ofRat_im]
    apply Cpx.ext <;> simp <;> grind
  have h2 : dotC (centered L ψ) (centered R ψ) =
      dotC (mulMat L ψ) (mulMat R ψ)
        - ofRat r * dotC (mulMat L ψ) ψ
        - ofRat l * dotC ψ (mulMat R ψ)
        + ofRat l * (ofRat r * dotC ψ ψ) := by
    unfold centered
    rw [dotC_sub_right, dotC_sub_left, dotC_sub_left]
    rw [dotC_smul_right, dotC_smul_right, dotC_smul_left, dotC_smul_left]
    simp only [conj, Cpx.ofRat_re, Cpx.ofRat_im]
    apply Cpx.ext <;> simp <;> grind
  have hR_exp : dotC ψ (mulMat R ψ) = ofRat r :=
    Cpx.ext rfl (dotC_hermitian_self_im R hR ψ)
  have hL_exp : dotC ψ (mulMat L ψ) = ofRat l :=
    Cpx.ext rfl (dotC_hermitian_self_im L hL ψ)
  have hR_exp' : dotC (mulMat R ψ) ψ = ofRat r := by
    rw [← dotC_hermitian R hR ψ ψ, hR_exp]
  have hL_exp' : dotC (mulMat L ψ) ψ = ofRat l := by
    rw [← dotC_hermitian L hL ψ ψ, hL_exp]
  have hψψ : dotC ψ ψ = ofRat (normSqC ψ) :=
    Cpx.ext (dotC_self_re ψ) (dotC_self_im ψ)
  have hconj : dotC (centered L ψ) (centered R ψ) =
      conj (dotC (centered R ψ) (centered L ψ)) :=
    dotC_conj (centered L ψ) (centered R ψ)
  have hsub_lhs : (dotC (centered R ψ) (centered L ψ) - dotC (centered L ψ) (centered R ψ)).im =
      2 * (dotC (centered R ψ) (centered L ψ)).im := by
    rw [hconj]
    simp [Cpx.sub_im, Cpx.conj_im]
    grind
  have hcomm : dotC ψ (comm R L ψ) =
      dotC (mulMat R ψ) (mulMat L ψ) - dotC (mulMat L ψ) (mulMat R ψ) := by
    unfold comm
    rw [dotC_sub_right, dotC_hermitian R hR ψ (mulMat L ψ), dotC_hermitian L hL ψ (mulMat R ψ)]
  have hsub_rhs : (dotC (centered R ψ) (centered L ψ) - dotC (centered L ψ) (centered R ψ)).im =
      (dotC ψ (comm R L ψ)).im := by
    rw [h1, h2, hR_exp, hL_exp, hR_exp', hL_exp', hψψ, hcomm]
    simp [Cpx.sub_im, Cpx.add_im, Cpx.mul_im, Cpx.ofRat_re, Cpx.ofRat_im]
    grind
  rw [← hsub_lhs, hsub_rhs]

/-- Core Rank-Role Uncertainty Inequality:
    for any Hermitian rank operator `R`, Hermitian role operator `L`, and state `ψ`,
    `4 * var R ψ * var L ψ ≥ (Im ⟨ψ, [R, L]ψ⟩)^2`. -/
theorem rank_role_uncertainty {d : Nat} (R L : Mat d)
    (hR : IsHermitian R) (hL : IsHermitian L) (ψ : Fin d → Cpx) :
    ((dotC ψ (comm R L ψ)).im) * ((dotC ψ (comm R L ψ)).im) ≤
      4 * var R ψ * var L ψ := by
  have hcs := cauchy_schwarz_cpx (centered R ψ) (centered L ψ)
  have him_le := Cpx.im_sq_le_normSq (dotC (centered R ψ) (centered L ψ))
  have hcomm := centered_comm_im R L hR hL ψ
  have hbound : ((dotC (centered R ψ) (centered L ψ)).im) *
      ((dotC (centered R ψ) (centered L ψ)).im) ≤ var R ψ * var L ψ :=
    Rat.le_trans him_le hcs
  have h4 : (2 * (dotC (centered R ψ) (centered L ψ)).im) *
      (2 * (dotC (centered R ψ) (centered L ψ)).im) ≤ 4 * var R ψ * var L ψ := by
    have hmul : 4 * (((dotC (centered R ψ) (centered L ψ)).im) *
        ((dotC (centered R ψ) (centered L ψ)).im)) ≤ 4 * (var R ψ * var L ψ) :=
      Rat.mul_le_mul_of_nonneg_left hbound (by decide)
    grind
  rw [← hcomm]
  exact h4

/-- Concrete 2x2 non-commuting rank/role witness verifying nontriviality. -/
def exRank : Mat 2
  | 0, 0 => ofRat 1
  | 0, 1 => ofRat 0
  | 1, 0 => ofRat 0
  | 1, 1 => ofRat 2

def exRole : Mat 2
  | 0, 0 => ofRat 0
  | 0, 1 => ⟨0, -1⟩
  | 1, 0 => ⟨0, 1⟩
  | 1, 1 => ofRat 0

def exPsi : Fin 2 → Cpx
  | 0 => ofRat 1
  | 1 => ofRat 0

theorem exRank_hermitian : IsHermitian exRank := by
  intro i j
  match i, j with
  | 0, 0 => simp [exRank, Cpx.conj, Cpx.ofRat]
  | 0, 1 => simp [exRank, Cpx.conj, Cpx.ofRat]
  | 1, 0 => simp [exRank, Cpx.conj, Cpx.ofRat]
  | 1, 1 => simp [exRank, Cpx.conj, Cpx.ofRat]

theorem exRole_hermitian : IsHermitian exRole := by
  intro i j
  match i, j with
  | 0, 0 => simp [exRole, Cpx.conj, Cpx.ofRat]
  | 0, 1 => simp [exRole, Cpx.conj]
  | 1, 0 => simp [exRole, Cpx.conj]
  | 1, 1 => simp [exRole, Cpx.conj, Cpx.ofRat]

theorem ex_uncertainty_nontrivial :
    ((dotC exPsi (comm exRank exRole exPsi)).im) *
      ((dotC exPsi (comm exRank exRole exPsi)).im) = 0 ∧
    (comm exRank exRole exPsi) 1 ≠ 0 := by
  simp only [dotC, comm, mulMat, exRank, exRole, exPsi, sumFin,
    Cpx.ofRat, Cpx.conj, Cpx.mul_re, Cpx.mul_im, Cpx.sub_re, Cpx.sub_im]
  constructor
  · grind
  · intro h
    have hre := congrArg Cpx.im h
    simp at hre
    grind

def exPsiSuper : Fin 2 → Cpx
  | 0 => ofRat (3 / 5)
  | 1 => ofRat (4 / 5)

theorem ex_super_uncertainty_positive :
    0 < ((dotC exPsiSuper (comm exRank exRole exPsiSuper)).im) *
      ((dotC exPsiSuper (comm exRank exRole exPsiSuper)).im) ∧
    ((dotC exPsiSuper (comm exRank exRole exPsiSuper)).im) *
      ((dotC exPsiSuper (comm exRank exRole exPsiSuper)).im) ≤
      4 * var exRank exPsiSuper * var exRole exPsiSuper := by
  constructor
  · simp only [dotC, comm, mulMat, exRank, exRole, exPsiSuper, sumFin,
      Cpx.ofRat, Cpx.conj, Cpx.mul_re, Cpx.mul_im, Cpx.sub_re, Cpx.sub_im]
    grind
  · exact rank_role_uncertainty exRank exRole exRank_hermitian exRole_hermitian exPsiSuper

end RST
