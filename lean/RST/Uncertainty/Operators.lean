/-
  Finite-dimensional matrices over Q[i], Hermitian and unitary properties,
  expectation values, centered operators, and variances.
-/

import RST.Foundations.Vectors

namespace RST

abbrev Mat (d : Nat) := Fin d → Fin d → Cpx

def mulMat {d : Nat} (M : Mat d) (ψ : Fin d → Cpx) (i : Fin d) : Cpx :=
  ⟨sumFin (fun j => (M i j * ψ j).re), sumFin (fun j => (M i j * ψ j).im)⟩

def matMul {d : Nat} (A B : Mat d) (i j : Fin d) : Cpx :=
  ⟨sumFin (fun k => (A i k * B k j).re), sumFin (fun k => (A i k * B k j).im)⟩

def conjTranspose {d : Nat} (M : Mat d) (i j : Fin d) : Cpx :=
  Cpx.conj (M j i)

def idMat (d : Nat) (i j : Fin d) : Cpx :=
  if i = j then Cpx.ofRat 1 else 0

def diagMat {d : Nat} (v : Fin d → Rat) (i j : Fin d) : Cpx :=
  if i = j then Cpx.ofRat (v i) else 0

def IsHermitian {d : Nat} (M : Mat d) : Prop :=
  ∀ i j : Fin d, M j i = Cpx.conj (M i j)

def IsUnitary {d : Nat} (U : Mat d) : Prop :=
  matMul (conjTranspose U) U = idMat d

theorem diagMat_hermitian {d : Nat} (v : Fin d → Rat) : IsHermitian (diagMat v) := by
  intro i j
  by_cases hij : i = j
  · subst hij; simp [diagMat, Cpx.conj, Cpx.ofRat]
  · have hji : j ≠ i := Ne.symm hij
    simp [diagMat, hij, hji, Cpx.conj]
    rfl

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
  fun i => mulMat M ψ i - Cpx.ofRat (expVal M ψ) * ψ i

def var {d : Nat} (M : Mat d) (ψ : Fin d → Cpx) : Rat :=
  normSqC (centered M ψ)

end RST
