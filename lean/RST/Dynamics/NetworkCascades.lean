/-
  Finite social-network graphs, bounded cascade cluster sizes,
  and branching-process reproduction number helpers.
-/

import RST.Foundations.Vectors

namespace RST

/-- Undirected simple graph on `n` vertices. -/
structure SocialGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  irrefl : ∀ i, adj i i = false
  symm : ∀ i j, adj i j = adj j i

/-- Number of informed vertices in a cascade state `informed : Fin n → Bool`. -/
def cascadeSize {n : Nat} (informed : Fin n → Bool) : Nat :=
  countFin informed

theorem cascadeSize_le_n {n : Nat} (informed : Fin n → Bool) :
    cascadeSize informed ≤ n :=
  countFin_le_len informed

def cascadeFraction {n : Nat} (informed : Fin n → Bool) : Rat :=
  if n = 0 then 0 else ((cascadeSize informed : Rat) / (n : Rat))

theorem cascadeFraction_bounds {n : Nat} (hn : 0 < n) (informed : Fin n → Bool) :
    0 ≤ cascadeFraction informed ∧ cascadeFraction informed ≤ 1 := by
  have hn_ne : n ≠ 0 := by omega
  have hnpos : (0 : Rat) < (n : Rat) := Rat.natCast_pos.mpr hn
  have hsz_nonneg : (0 : Rat) ≤ (cascadeSize informed : Rat) := Rat.natCast_nonneg
  have hsz_le : cascadeSize informed ≤ n := cascadeSize_le_n informed
  have hsz_rat_le : (cascadeSize informed : Rat) ≤ (n : Rat) :=
    Rat.natCast_le_natCast.mpr hsz_le
  unfold cascadeFraction
  simp only [hn_ne, ↓reduceIte]
  constructor
  · exact rat_div_nonneg hsz_nonneg hnpos
  · rw [Rat.div_def]
    have hinv_pos : 0 < (n : Rat)⁻¹ := by
      have h1 : (0 : Rat) ≤ (n : Rat)⁻¹ := by
        by_cases h : (n : Rat)⁻¹ ≤ 0
        · have : (n : Rat) * (n : Rat)⁻¹ ≤ (n : Rat) * 0 :=
            Rat.mul_le_mul_of_nonneg_left h (by grind)
          have hmul : (n : Rat) * (n : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
          grind
        · grind
      grind
    have hmul : (cascadeSize informed : Rat) * (n : Rat)⁻¹ ≤ (n : Rat) * (n : Rat)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hsz_rat_le (by grind)
    have hid : (n : Rat) * (n : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
    grind

/-- Homogeneous branching-process reproduction number `R_0 = (n - 1) * q * p_tx`. -/
def reproductionNumber (n : Nat) (q ptx : Rat) : Rat :=
  ((n - 1 : Nat) : Rat) * q * ptx

theorem reproductionNumber_nonneg (n : Nat) {q ptx : Rat} (hq : 0 ≤ q) (hptx : 0 ≤ ptx) :
    0 ≤ reproductionNumber n q ptx := by
  unfold reproductionNumber
  have hn : (0 : Rat) ≤ ((n - 1 : Nat) : Rat) := Rat.natCast_nonneg
  exact Rat.mul_nonneg (Rat.mul_nonneg hn hq) hptx

theorem reproductionNumber_mono_q (n : Nat) {q₁ q₂ ptx : Rat}
    (hq : q₁ ≤ q₂) (hptx : 0 ≤ ptx) :
    reproductionNumber n q₁ ptx ≤ reproductionNumber n q₂ ptx := by
  unfold reproductionNumber
  have hn : (0 : Rat) ≤ ((n - 1 : Nat) : Rat) := Rat.natCast_nonneg
  have h1 : ((n - 1 : Nat) : Rat) * q₁ ≤ ((n - 1 : Nat) : Rat) * q₂ :=
    Rat.mul_le_mul_of_nonneg_left hq hn
  exact Rat.mul_le_mul_of_nonneg_right h1 hptx

end RST
