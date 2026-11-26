/-
  Commutator, centered anticommutator, diagonal commutativity,
  and unitary-basis-change Hermiticity preservation.
-/

import RST.Uncertainty.Operators

namespace RST

/-- Action of the commutator `[R, L] = R L - L R` on state `ψ`. -/
def comm {d : Nat} (R L : Mat d) (ψ : Fin d → Cpx) : Fin d → Cpx :=
  fun i => mulMat R (mulMat L ψ) i - mulMat L (mulMat R ψ) i

/-- Matrix-level commutator `[A, B] = A B - B A`. -/
def commMat {d : Nat} (A B : Mat d) (i j : Fin d) : Cpx :=
  matMul A B i j - matMul B A i j

/-- Action of the centered anticommutator `{R', L'} = R' L' + L' R'` on `ψ`. -/
def anticommCentered {d : Nat} (R L : Mat d) (ψ : Fin d → Cpx) : Fin d → Cpx :=
  let r := expVal R ψ
  let l := expVal L ψ
  let rPsi := fun i => mulMat R ψ i - Cpx.ofRat r * ψ i
  let lPsi := fun i => mulMat L ψ i - Cpx.ofRat l * ψ i
  fun i => (mulMat R lPsi i - Cpx.ofRat r * lPsi i) +
           (mulMat L rPsi i - Cpx.ofRat l * rPsi i)

/-- Diagonal operators in the same basis commute identically (`[diag a, diag b] = 0`). -/
theorem diag_mulMat {d : Nat} (v : Fin d → Rat) (ψ : Fin d → Cpx) (i : Fin d) :
    mulMat (diagMat v) ψ i = Cpx.ofRat (v i) * ψ i := by
  have hsingle : ∀ {m : Nat} (f : Fin m → Rat) (k : Fin m),
      sumFin (fun j => if k = j then f j else 0) = f k := by
    intro m f k
    induction m with
    | zero => exact Fin.elim0 k
    | succ n ih =>
        refine Fin.cases ?_ ?_ k
        · simp only [sumFin_succ, ↓reduceIte]
          have hz : (fun j : Fin n => if (0 : Fin (n + 1)) = j.succ then f j.succ else 0) = fun _ => 0 := by
            funext j; have hne : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm; simp [hne]
          rw [hz, sumFin_zero_fun]; grind
        · intro k'
          simp only [sumFin_succ]
          have h0 : (k'.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero k'
          simp only [h0, ↓reduceIte]
          have hsub : (fun j : Fin n => if k'.succ = j.succ then f j.succ else 0) =
              fun j => if k' = j then f j.succ else 0 := by
            funext j; simp [Fin.succ_inj]
          rw [hsub, ih (fun j => f j.succ) k']; grind
  apply Cpx.ext
  · simp only [mulMat]
    have hre : (fun j : Fin d => (diagMat v i j * ψ j).re) =
        fun j => if i = j then (Cpx.ofRat (v j) * ψ j).re else 0 := by
      funext j
      by_cases hij : i = j
      · subst hij; simp [diagMat]
      · simp [diagMat, hij, Cpx.mul_re]; grind
    rw [hre, hsingle _ i]
  · simp only [mulMat]
    have him : (fun j : Fin d => (diagMat v i j * ψ j).im) =
        fun j => if i = j then (Cpx.ofRat (v j) * ψ j).im else 0 := by
      funext j
      by_cases hij : i = j
      · subst hij; simp [diagMat]
      · simp [diagMat, hij, Cpx.mul_im]; grind
    rw [him, hsingle _ i]

theorem diagMat_commute {d : Nat} (a b : Fin d → Rat) (ψ : Fin d → Cpx) :
    comm (diagMat a) (diagMat b) ψ = fun _ => 0 := by
  funext i
  unfold comm
  rw [diag_mulMat a (mulMat (diagMat b) ψ) i, diag_mulMat b ψ i]
  rw [diag_mulMat b (mulMat (diagMat a) ψ) i, diag_mulMat a ψ i]
  apply Cpx.ext <;> simp <;> grind

/-- Conjugating a Hermitian matrix `D` by any matrix `U` via `U† D U` preserves Hermiticity. -/
def conjugateBy {d : Nat} (U D : Mat d) : Mat d :=
  matMul (conjTranspose U) (matMul D U)

theorem conjugateBy_hermitian {d : Nat} (U D : Mat d) (hD : IsHermitian D) :
    IsHermitian (conjugateBy U D) := by
  intro i j
  unfold conjugateBy matMul conjTranspose
  apply Cpx.ext
  · simp only [Cpx.conj_re, Cpx.mul_re, Cpx.mul_im, Cpx.conj_im]
    have hL : (fun k : Fin d =>
        (U k j).re * sumFin (fun l => (D k l).re * (U l i).re - (D k l).im * (U l i).im) -
        -(U k j).im * sumFin (fun l => (D k l).re * (U l i).im + (D k l).im * (U l i).re)) =
      fun k => sumFin (fun l =>
        (U k j).re * ((D k l).re * (U l i).re - (D k l).im * (U l i).im) -
        -(U k j).im * ((D k l).re * (U l i).im + (D k l).im * (U l i).re)) := by
      funext k; rw [← sumFin_smul, ← sumFin_smul, ← sumFin_sub]
    rw [hL, sumFin_swap]
    congr 1
    funext l
    have hR' : ((U l i).re * sumFin (fun k => (D l k).re * (U k j).re - (D l k).im * (U k j).im) -
        -(U l i).im * sumFin (fun k => (D l k).re * (U k j).im + (D l k).im * (U k j).re)) =
      sumFin (fun k =>
        (U l i).re * ((D l k).re * (U k j).re - (D l k).im * (U k j).im) -
        -(U l i).im * ((D l k).re * (U k j).im + (D l k).im * (U k j).re)) := by
      rw [← sumFin_smul, ← sumFin_smul, ← sumFin_sub]
    rw [hR']
    congr 1
    funext k
    have hkl := hD l k
    have hre : (D k l).re = (D l k).re := by rw [hkl]; rfl
    have him : (D k l).im = -(D l k).im := by rw [hkl]; rfl
    rw [hre, him]
    grind
  · simp only [Cpx.conj_re, Cpx.conj_im, Cpx.mul_re, Cpx.mul_im]
    have hL : (fun k : Fin d =>
        (U k j).re * sumFin (fun l => (D k l).re * (U l i).im + (D k l).im * (U l i).re) +
        -(U k j).im * sumFin (fun l => (D k l).re * (U l i).re - (D k l).im * (U l i).im)) =
      fun k => sumFin (fun l =>
        (U k j).re * ((D k l).re * (U l i).im + (D k l).im * (U l i).re) +
        -(U k j).im * ((D k l).re * (U l i).re - (D k l).im * (U l i).im)) := by
      funext k; rw [← sumFin_smul, ← sumFin_smul, ← sumFin_add]
    rw [hL, sumFin_swap]
    have hR : (fun l : Fin d =>
        (U l i).re * sumFin (fun k => (D l k).re * (U k j).im + (D l k).im * (U k j).re) +
        -(U l i).im * sumFin (fun k => (D l k).re * (U k j).re - (D l k).im * (U k j).im)) =
      fun l => sumFin (fun k =>
        (U l i).re * ((D l k).re * (U k j).im + (D l k).im * (U k j).re) +
        -(U l i).im * ((D l k).re * (U k j).re - (D l k).im * (U k j).im)) := by
      funext l; rw [← sumFin_smul, ← sumFin_smul, ← sumFin_add]
    rw [hR]
    have hnegR : -(sumFin (fun l : Fin d => sumFin (fun k =>
        (U l i).re * ((D l k).re * (U k j).im + (D l k).im * (U k j).re) +
        -(U l i).im * ((D l k).re * (U k j).re - (D l k).im * (U k j).im)))) =
      sumFin (fun l => sumFin (fun k =>
        -((U l i).re * ((D l k).re * (U k j).im + (D l k).im * (U k j).re) +
          -(U l i).im * ((D l k).re * (U k j).re - (D l k).im * (U k j).im)))) := by
      have h1 := sumFin_smul (-1 : Rat) (fun l : Fin d => sumFin (fun k =>
        (U l i).re * ((D l k).re * (U k j).im + (D l k).im * (U k j).re) +
        -(U l i).im * ((D l k).re * (U k j).re - (D l k).im * (U k j).im)))
      have h2 : -(sumFin (fun l : Fin d => sumFin (fun k =>
          (U l i).re * ((D l k).re * (U k j).im + (D l k).im * (U k j).re) +
          -(U l i).im * ((D l k).re * (U k j).re - (D l k).im * (U k j).im)))) =
        (-1 : Rat) * sumFin (fun l : Fin d => sumFin (fun k =>
          (U l i).re * ((D l k).re * (U k j).im + (D l k).im * (U k j).re) +
          -(U l i).im * ((D l k).re * (U k j).re - (D l k).im * (U k j).im))) := by grind
      rw [h2, ← h1]
      congr 1; funext l
      have hs := sumFin_smul (-1 : Rat) (fun k : Fin d =>
        (U l i).re * ((D l k).re * (U k j).im + (D l k).im * (U k j).re) +
        -(U l i).im * ((D l k).re * (U k j).re - (D l k).im * (U k j).im))
      rw [← hs]
      congr 1; funext k; grind
    rw [hnegR]
    congr 1; funext l; congr 1; funext k
    have hkl := hD l k
    have hre : (D k l).re = (D l k).re := by rw [hkl]; rfl
    have him : (D k l).im = -(D l k).im := by rw [hkl]; rfl
    rw [hre, him]; grind

end RST
