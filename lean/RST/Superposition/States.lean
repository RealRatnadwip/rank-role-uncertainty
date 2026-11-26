/-
  Composite partner-role relational states, tensor normalization, and superposition predicates.
-/

import RST.Superposition.Amplitudes
import RST.Relational.SharedMaximum

namespace RST

/-- A composite state pairs system-level complex amplitudes `a_i` with unit-norm
    partner role vectors `c_{ij}` in `Q[i]^m`. -/
structure CompositeState (n m : Nat) where
  sys : CpxAmplitudes n
  roleVec : Fin n → Fin m → Cpx
  role_norm : ∀ i, normSqC (roleVec i) = 1

/-- Composite squared norm equals 1 whenever system weights and partner role
    vectors are normalized. -/
theorem composite_state_norm_one {n m : Nat} (S : CompositeState n m) :
    sumFin (fun i => sumFin (fun j => Cpx.normSq (S.sys.a i * S.roleVec i j))) = 1 := by
  have hterm : ∀ i : Fin n,
      sumFin (fun j => Cpx.normSq (S.sys.a i * S.roleVec i j)) = Cpx.normSq (S.sys.a i) := by
    intro i
    have hmul : (fun j : Fin m => Cpx.normSq (S.sys.a i * S.roleVec i j)) =
        fun j => Cpx.normSq (S.sys.a i) * Cpx.normSq (S.roleVec i j) := by
      funext j
      simp [Cpx.normSq, Cpx.mul_re, Cpx.mul_im]
      grind
    rw [hmul, sumFin_smul]
    have hr := S.role_norm i
    unfold normSqC at hr
    rw [hr]
    grind
  have hfun : (fun i : Fin n => sumFin (fun j => Cpx.normSq (S.sys.a i * S.roleVec i j))) =
      fun i => Cpx.normSq (S.sys.a i) := by
    funext i; exact hterm i
  rw [hfun]
  exact S.sys.unit_norm

theorem amplitudes_distributed_weights {n : Nat} (A : Amplitudes n)
    (h : ∃ i j : Fin n, i ≠ j ∧ A.a i ≠ 0 ∧ A.a j ≠ 0) :
    DistributedWeights A.toWeights := by
  rcases h with ⟨i, j, hij, hi, hj⟩
  exact ⟨i, j, hij, rat_sq_pos hi, rat_sq_pos hj⟩

theorem amplitudes_subunit_weights {n : Nat} (A : Amplitudes n)
    (h : ∃ i j : Fin n, i ≠ j ∧ A.a i ≠ 0 ∧ A.a j ≠ 0) :
    ∀ k : Fin n, A.a k * A.a k < 1 ∧ A.a k * A.a k ≠ 1 := by
  have hw := amplitudes_distributed_weights A h
  intro k
  have hlt := subunit_weights_of_distributed A.toWeights hw k
  change A.a k * A.a k < 1 at hlt
  exact ⟨hlt, by grind⟩

end RST
