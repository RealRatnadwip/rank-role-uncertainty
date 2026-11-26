/-
  Real and complex amplitude vectors and induced normalized weight distributions.
-/

import RST.Foundations.Normalization

namespace RST

/-- Real unit-norm amplitude vector over `n` individuals. -/
structure Amplitudes (n : Nat) where
  a : Fin n → Rat
  unit_norm : sumFin (fun i => a i * a i) = 1

/-- Complex (Gaussian-rational) unit-norm amplitude vector over `n` individuals. -/
structure CpxAmplitudes (n : Nat) where
  a : Fin n → Cpx
  unit_norm : normSqC a = 1

/-- Induced classical probability weights `w_i = a_i^2`. -/
def Amplitudes.toWeights {n : Nat} (A : Amplitudes n) : Weights n where
  w := fun i => A.a i * A.a i
  nonneg := fun i => rat_sq_nonneg (A.a i)
  sum_one := A.unit_norm

/-- Induced classical probability weights `w_i = |a_i|^2` from complex amplitudes. -/
def CpxAmplitudes.toWeights {n : Nat} (A : CpxAmplitudes n) : Weights n where
  w := fun i => Cpx.normSq (A.a i)
  nonneg := fun i => Cpx.normSq_nonneg (A.a i)
  sum_one := A.unit_norm

theorem collapse_probs_sum_one {n : Nat} (A : Amplitudes n) :
    sumFin A.toWeights.w = 1 :=
  A.unit_norm

theorem cpx_collapse_probs_sum_one {n : Nat} (A : CpxAmplitudes n) :
    sumFin A.toWeights.w = 1 :=
  A.unit_norm

end RST
