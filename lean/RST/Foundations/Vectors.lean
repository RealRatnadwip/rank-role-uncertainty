/-
  Gaussian rationals Q[i], complex inner products, norms, and Cauchy-Schwarz.
-/

import RST.Foundations.FiniteSets

namespace RST

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

theorem re_sq_add_im_sq (z : Cpx) : z.re * z.re + z.im * z.im = normSq z := rfl

end Cpx

open Cpx

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

theorem dotC_add_left {d : Nat} (u v w : Fin d → Cpx) :
    dotC (fun k => u k + v k) w = dotC u w + dotC v w := by
  have h := dotC_add_right w u v
  rw [dotC_conj (fun k => u k + v k) w, h, dotC_conj w u, dotC_conj w v]
  apply Cpx.ext <;> simp <;> grind

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

end RST
