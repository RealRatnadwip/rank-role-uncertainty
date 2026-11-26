/-
  Orthogonal subspace projection, Pythagorean norm decomposition, and post-projection
  weight normalization under nonzero projection.
-/

import RST.Superposition.States

namespace RST

/-- Orthogonal coordinate projector onto the subset `keep : Fin d → Bool`. -/
def projSubspace {d : Nat} (keep : Fin d → Bool) (ψ : Fin d → Cpx) : Fin d → Cpx :=
  fun i => if keep i then ψ i else 0

theorem projSubspace_idempotent {d : Nat} (keep : Fin d → Bool) (ψ : Fin d → Cpx) :
    projSubspace keep (projSubspace keep ψ) = projSubspace keep ψ := by
  funext i
  dsimp [projSubspace]
  cases keep i <;> simp

theorem projSubspace_pythagorean {d : Nat} (keep : Fin d → Bool) (ψ : Fin d → Cpx) :
    normSqC (projSubspace keep ψ) + normSqC (projSubspace (fun i => !keep i) ψ) = normSqC ψ := by
  unfold normSqC projSubspace
  rw [← sumFin_add]
  congr 1
  funext i
  cases hk : keep i <;> simp [hk, Cpx.normSq] <;> grind

theorem projSubspace_norm_le {d : Nat} (keep : Fin d → Bool) (ψ : Fin d → Cpx) :
    normSqC (projSubspace keep ψ) ≤ normSqC ψ := by
  have hpy := projSubspace_pythagorean keep ψ
  have hcomp : 0 ≤ normSqC (projSubspace (fun i => !keep i) ψ) := normSqC_nonneg _
  grind

/-- Normalized weight distribution induced by a nonzero projection `P_k |Ψ⟩ / ‖P_k |Ψ⟩‖`. -/
def projectedWeights {d : Nat} (keep : Fin d → Bool) (ψ : Fin d → Cpx)
    (hpos : 0 < normSqC (projSubspace keep ψ)) : Weights d where
  w := fun i => Cpx.normSq (projSubspace keep ψ i) / normSqC (projSubspace keep ψ)
  nonneg := fun i => rat_div_nonneg (Cpx.normSq_nonneg _) hpos
  sum_one := by
    rw [sumFin_div_const]
    have hne : normSqC (projSubspace keep ψ) ≠ 0 := by grind
    change normSqC (projSubspace keep ψ) / normSqC (projSubspace keep ψ) = 1
    rw [Rat.div_def, Rat.mul_inv_cancel _ hne]

/-- When a projected vector admits an exact rational norm `s > 0` (`normSqC = s * s`),
    the normalized vector `(1/s) • P_k |Ψ⟩` has exact unit norm `1`. -/
theorem projected_vector_unit_norm {d : Nat} (keep : Fin d → Bool) (ψ : Fin d → Cpx)
    (s : Rat) (hs : 0 < s) (hnorm : normSqC (projSubspace keep ψ) = s * s) :
    normSqC (fun i => Cpx.ofRat (1 / s) * projSubspace keep ψ i) = 1 := by
  unfold normSqC
  have hmul : (fun i : Fin d => Cpx.normSq (Cpx.ofRat (1 / s) * projSubspace keep ψ i)) =
      fun i => ((1 / s) * (1 / s)) * Cpx.normSq (projSubspace keep ψ i) := by
    funext i
    simp [Cpx.normSq, Cpx.mul_re, Cpx.mul_im, Cpx.ofRat]
    grind
  rw [hmul, sumFin_smul]
  have h1 : sumFin (fun i => Cpx.normSq (projSubspace keep ψ i)) = s * s := hnorm
  rw [h1]
  have hne : s ≠ 0 := by grind
  rw [Rat.div_def, Rat.one_mul]
  have hid : (s⁻¹ * s⁻¹) * (s * s) = (s⁻¹ * s) * (s⁻¹ * s) := by grind
  rw [hid, Rat.inv_mul_cancel _ hne]
  grind

end RST
