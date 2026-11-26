/-
  Robertson and Schrodinger uncertainty inequalities over Q[i]^d,
  plus exact 2D and 3D unitary-rotated operator witnesses.
-/

import RST.Uncertainty.Commutator

namespace RST

theorem centered_comm_im {d : Nat} (R L : Mat d) (hR : IsHermitian R) (hL : IsHermitian L)
    (ψ : Fin d → Cpx) :
    2 * (dotC (centered R ψ) (centered L ψ)).im = (dotC ψ (comm R L ψ)).im := by
  let r := expVal R ψ
  let l := expVal L ψ
  have h1 : dotC (centered R ψ) (centered L ψ) =
      dotC (mulMat R ψ) (mulMat L ψ)
        - Cpx.ofRat l * dotC (mulMat R ψ) ψ
        - Cpx.ofRat r * dotC ψ (mulMat L ψ)
        + Cpx.ofRat r * (Cpx.ofRat l * dotC ψ ψ) := by
    unfold centered
    rw [dotC_sub_right, dotC_sub_left, dotC_sub_left]
    rw [dotC_smul_right, dotC_smul_right, dotC_smul_left, dotC_smul_left]
    simp only [Cpx.conj, Cpx.ofRat_re, Cpx.ofRat_im]
    apply Cpx.ext <;> simp <;> grind
  have h2 : dotC (centered L ψ) (centered R ψ) =
      dotC (mulMat L ψ) (mulMat R ψ)
        - Cpx.ofRat r * dotC (mulMat L ψ) ψ
        - Cpx.ofRat l * dotC ψ (mulMat R ψ)
        + Cpx.ofRat l * (Cpx.ofRat r * dotC ψ ψ) := by
    unfold centered
    rw [dotC_sub_right, dotC_sub_left, dotC_sub_left]
    rw [dotC_smul_right, dotC_smul_right, dotC_smul_left, dotC_smul_left]
    simp only [Cpx.conj, Cpx.ofRat_re, Cpx.ofRat_im]
    apply Cpx.ext <;> simp <;> grind
  have hR_exp : dotC ψ (mulMat R ψ) = Cpx.ofRat r :=
    Cpx.ext rfl (dotC_hermitian_self_im R hR ψ)
  have hL_exp : dotC ψ (mulMat L ψ) = Cpx.ofRat l :=
    Cpx.ext rfl (dotC_hermitian_self_im L hL ψ)
  have hR_exp' : dotC (mulMat R ψ) ψ = Cpx.ofRat r := by
    rw [← dotC_hermitian R hR ψ ψ, hR_exp]
  have hL_exp' : dotC (mulMat L ψ) ψ = Cpx.ofRat l := by
    rw [← dotC_hermitian L hL ψ ψ, hL_exp]
  have hψψ : dotC ψ ψ = Cpx.ofRat (normSqC ψ) :=
    Cpx.ext (dotC_self_re ψ) (dotC_self_im ψ)
  have hconj : dotC (centered L ψ) (centered R ψ) =
      Cpx.conj (dotC (centered R ψ) (centered L ψ)) :=
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

theorem centered_anticomm_re {d : Nat} (R L : Mat d) (hR : IsHermitian R) (hL : IsHermitian L)
    (ψ : Fin d → Cpx) :
    2 * (dotC (centered R ψ) (centered L ψ)).re = (dotC ψ (anticommCentered R L ψ)).re := by
  have hanti : dotC ψ (anticommCentered R L ψ) =
      dotC (centered R ψ) (centered L ψ) + dotC (centered L ψ) (centered R ψ) := by
    unfold anticommCentered centered
    rw [dotC_add_right, dotC_sub_right, dotC_sub_right, dotC_smul_right, dotC_smul_right]
    have hR1 : dotC ψ (mulMat R (fun i => mulMat L ψ i - Cpx.ofRat (expVal L ψ) * ψ i)) =
        dotC (mulMat R ψ) (fun i => mulMat L ψ i - Cpx.ofRat (expVal L ψ) * ψ i) :=
      dotC_hermitian R hR ψ _
    have hL1 : dotC ψ (mulMat L (fun i => mulMat R ψ i - Cpx.ofRat (expVal R ψ) * ψ i)) =
        dotC (mulMat L ψ) (fun i => mulMat R ψ i - Cpx.ofRat (expVal R ψ) * ψ i) :=
      dotC_hermitian L hL ψ _
    rw [hR1, hL1]
    have hR2 : dotC (fun i => mulMat R ψ i - Cpx.ofRat (expVal R ψ) * ψ i)
          (fun i => mulMat L ψ i - Cpx.ofRat (expVal L ψ) * ψ i) =
        dotC (mulMat R ψ) (fun i => mulMat L ψ i - Cpx.ofRat (expVal L ψ) * ψ i) -
          Cpx.ofRat (expVal R ψ) * dotC ψ (fun i => mulMat L ψ i - Cpx.ofRat (expVal L ψ) * ψ i) := by
      rw [dotC_sub_left, dotC_smul_left]
      simp [Cpx.conj, Cpx.ofRat]
    have hL2 : dotC (fun i => mulMat L ψ i - Cpx.ofRat (expVal L ψ) * ψ i)
          (fun i => mulMat R ψ i - Cpx.ofRat (expVal R ψ) * ψ i) =
        dotC (mulMat L ψ) (fun i => mulMat R ψ i - Cpx.ofRat (expVal R ψ) * ψ i) -
          Cpx.ofRat (expVal L ψ) * dotC ψ (fun i => mulMat R ψ i - Cpx.ofRat (expVal R ψ) * ψ i) := by
      rw [dotC_sub_left, dotC_smul_left]
      simp [Cpx.conj, Cpx.ofRat]
    rw [hR2, hL2]
  rw [hanti, dotC_conj (centered L ψ) (centered R ψ)]
  simp [Cpx.add_re, Cpx.conj_re]
  grind

/-- Schrodinger uncertainty inequality (1930) in finite dimension over Q[i]^d:
    `4 * var R psi * var L psi >= (Im <psi, [R, L]psi>)^2 + (Re <psi, {R', L'}psi>)^2`. -/
theorem schrodinger_uncertainty {d : Nat} (R L : Mat d)
    (hR : IsHermitian R) (hL : IsHermitian L) (ψ : Fin d → Cpx) :
    ((dotC ψ (comm R L ψ)).im) * ((dotC ψ (comm R L ψ)).im) +
      ((dotC ψ (anticommCentered R L ψ)).re) * ((dotC ψ (anticommCentered R L ψ)).re) ≤
      4 * var R ψ * var L ψ := by
  have hcs := cauchy_schwarz_cpx (centered R ψ) (centered L ψ)
  have hcomm := centered_comm_im R L hR hL ψ
  have hanti := centered_anticomm_re R L hR hL ψ
  rw [← hcomm, ← hanti]
  have hnorm : Cpx.normSq (dotC (centered R ψ) (centered L ψ)) =
      (dotC (centered R ψ) (centered L ψ)).re * (dotC (centered R ψ) (centered L ψ)).re +
      (dotC (centered R ψ) (centered L ψ)).im * (dotC (centered R ψ) (centered L ψ)).im := rfl
  rw [hnorm] at hcs
  have h4 : 4 * ((dotC (centered R ψ) (centered L ψ)).re * (dotC (centered R ψ) (centered L ψ)).re +
      (dotC (centered R ψ) (centered L ψ)).im * (dotC (centered R ψ) (centered L ψ)).im) ≤
      4 * (var R ψ * var L ψ) :=
    Rat.mul_le_mul_of_nonneg_left hcs (by grind : (0 : Rat) ≤ 4)
  grind

/-- Robertson uncertainty inequality (1929) as an immediate corollary of Schrodinger's bound. -/
theorem robertson_uncertainty {d : Nat} (R L : Mat d)
    (hR : IsHermitian R) (hL : IsHermitian L) (ψ : Fin d → Cpx) :
    ((dotC ψ (comm R L ψ)).im) * ((dotC ψ (comm R L ψ)).im) ≤
      4 * var R ψ * var L ψ := by
  have hsch := schrodinger_uncertainty R L hR hL ψ
  have hsq := rat_sq_nonneg ((dotC ψ (anticommCentered R L ψ)).re)
  grind

/-- Exact 2x2 unitary transformation `U2 = (1/5)[[3, 4i], [4i, 3]]`. -/
def U2 : Mat 2
  | 0, 0 => Cpx.ofRat (3 / 5)
  | 0, 1 => ⟨0, 4 / 5⟩
  | 1, 0 => ⟨0, 4 / 5⟩
  | 1, 1 => Cpx.ofRat (3 / 5)

theorem U2_unitary : IsUnitary U2 := by
  funext i j
  match i, j with
  | 0, 0 =>
      apply Cpx.ext <;> simp [matMul, conjTranspose, idMat, U2, sumFin_succ, sumFin_zero, Cpx.conj, Cpx.ofRat] <;> grind
  | 0, 1 =>
      apply Cpx.ext <;> simp [matMul, conjTranspose, idMat, U2, sumFin_succ, sumFin_zero, Cpx.conj, Cpx.ofRat] <;> grind
  | 1, 0 =>
      apply Cpx.ext <;> simp [matMul, conjTranspose, idMat, U2, sumFin_succ, sumFin_zero, Cpx.conj, Cpx.ofRat] <;> grind
  | 1, 1 =>
      apply Cpx.ext <;> simp [matMul, conjTranspose, idMat, U2, sumFin_succ, sumFin_zero, Cpx.conj, Cpx.ofRat] <;> grind

def D_R2 : Mat 2 := diagMat (fun | 0 => 1 | 1 => 2)
def D_L2 : Mat 2 := diagMat (fun | 0 => -1 | 1 => 1)
def L2_rot : Mat 2 := conjugateBy U2 D_L2

theorem D_R2_hermitian : IsHermitian D_R2 := diagMat_hermitian _
theorem L2_rot_hermitian : IsHermitian L2_rot := conjugateBy_hermitian U2 D_L2 (diagMat_hermitian _)

def psi2_ex : Fin 2 → Cpx
  | 0 => Cpx.ofRat (3 / 5)
  | 1 => Cpx.ofRat (4 / 5)

theorem ex_2d_schrodinger_verified :
    0 < ((dotC psi2_ex (comm D_R2 L2_rot psi2_ex)).im) * ((dotC psi2_ex (comm D_R2 L2_rot psi2_ex)).im) ∧
    ((dotC psi2_ex (comm D_R2 L2_rot psi2_ex)).im) * ((dotC psi2_ex (comm D_R2 L2_rot psi2_ex)).im) +
      ((dotC psi2_ex (anticommCentered D_R2 L2_rot psi2_ex)).re) *
      ((dotC psi2_ex (anticommCentered D_R2 L2_rot psi2_ex)).re) ≤
      4 * var D_R2 psi2_ex * var L2_rot psi2_ex := by
  constructor
  · simp [dotC, comm, mulMat, D_R2, L2_rot, conjugateBy, matMul, conjTranspose, D_L2,
      diagMat, U2, psi2_ex, sumFin_succ, sumFin_zero, Cpx.conj, Cpx.ofRat,
      Cpx.mul_re, Cpx.mul_im, Cpx.sub_re, Cpx.sub_im]
    grind
  · exact schrodinger_uncertainty D_R2 L2_rot D_R2_hermitian L2_rot_hermitian psi2_ex

/-- Exact 3x3 unitary transformation extending U2 on coordinates (0, 1) and identity on 2. -/
def U3 : Mat 3
  | 0, 0 => Cpx.ofRat (3 / 5)
  | 0, 1 => ⟨0, 4 / 5⟩
  | 0, 2 => 0
  | 1, 0 => ⟨0, 4 / 5⟩
  | 1, 1 => Cpx.ofRat (3 / 5)
  | 1, 2 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => Cpx.ofRat 1

def D_R3 : Mat 3 := diagMat (fun | 0 => 1 | 1 => 2 | 2 => 3)
def D_L3 : Mat 3 := diagMat (fun | 0 => -1 | 1 => 0 | 2 => 1)
def L3_rot : Mat 3 := conjugateBy U3 D_L3

theorem D_R3_hermitian : IsHermitian D_R3 := diagMat_hermitian _
theorem L3_rot_hermitian : IsHermitian L3_rot := conjugateBy_hermitian U3 D_L3 (diagMat_hermitian _)

def psi3_ex : Fin 3 → Cpx
  | 0 => Cpx.ofRat (9 / 25)
  | 1 => Cpx.ofRat (12 / 25)
  | 2 => Cpx.ofRat (4 / 5)

theorem ex_3d_schrodinger_verified :
    normSqC psi3_ex = 1 ∧
    0 < ((dotC psi3_ex (comm D_R3 L3_rot psi3_ex)).im) * ((dotC psi3_ex (comm D_R3 L3_rot psi3_ex)).im) ∧
    ((dotC psi3_ex (comm D_R3 L3_rot psi3_ex)).im) * ((dotC psi3_ex (comm D_R3 L3_rot psi3_ex)).im) +
      ((dotC psi3_ex (anticommCentered D_R3 L3_rot psi3_ex)).re) *
      ((dotC psi3_ex (anticommCentered D_R3 L3_rot psi3_ex)).re) ≤
      4 * var D_R3 psi3_ex * var L3_rot psi3_ex := by
  refine ⟨?_, ?_, ?_⟩
  · simp [normSqC, psi3_ex, Cpx.normSq, Cpx.ofRat, sumFin_succ, sumFin_zero]; grind
  · simp [dotC, comm, mulMat, D_R3, L3_rot, conjugateBy, matMul, conjTranspose, D_L3,
      diagMat, U3, psi3_ex, sumFin_succ, sumFin_zero, Cpx.conj, Cpx.ofRat,
      Cpx.mul_re, Cpx.mul_im, Cpx.sub_re, Cpx.sub_im]
    grind
  · exact schrodinger_uncertainty D_R3 L3_rot D_R3_hermitian L3_rot_hermitian psi3_ex

end RST
