# RST v1.1 Revision Report and Verification Ledger

This document records the concrete mathematical corrections, structural additions,
and theorem-to-artifact status mapping introduced in the v1.1 revision of
**The Rank-Role Uncertainty Principle: Relational Superposition Theory (RST)**.

## 1. Summary of Changes from v1.0 to v1.1

1. **Resolution of the Rank-Role Flaw (`Model A` vs `Model B`)**:
   - Explicitly showed that positive distributed weights ($\sum_i w_i = 1, w_i > 0$
     for at least two $i$) guarantee only $w_k < 1$ and do **not** eliminate a unique
     rank-1 winner, demonstrated formally via $\mathbf{w}_{99} = (0.99, 0.01)$.
   - Defined competition ordinal rank $r_i(\mathbf{w}) = 1 + \#\{j : w_j > w_i\}$,
     `UniqueMaximum`, `DistributedWeights` (Model A), and `SharedMaximum` (Model B).
2. **Role Matrix Normalization & Aggregation Sensitivity**:
   - Grounded raw non-negative role matrices $M \in \Rnum_{\ge 0}^{n\times m}$ with
     zero-safe column normalization, strict dimension dominance, linear aggregation
     $G_i(\boldsymbol{\alpha})$, and rank-reversal sensitivity (`4 x 5` example +
     1,000 Dirichlet weights).
3. **Explicit Epistemic Separation (5 Layers)**:
   - Tagged definitions, theorems, assumptions, hypotheses, and commentary throughout
     the monograph with `Established Math`, `RST Formalization`, `Behavioral Assumption`,
     `Empirical Hypothesis`, and `Satirical Interpretation`.
   - Honestly scoped complex phases in $\ket{\Psi} \in \Cnum^n \otimes \Cnum^m$ as an
     algebraic mechanism enabling non-commuting context rotations rather than measured
     psychometric data, explicitly contrasting classical simplex states $\Delta^{n-1}$.
4. **Robertson (1929) and Schrodinger (1930) Attribution & Covariance Tightness**:
   - Replaced unattributed uncertainty framing with Robertson (1929) and Schrodinger
     (1930) citations, added full centered anticommutator covariance proofs, proved
     exact diagonal commutation at $\gamma = 0$, derived context rotation
     $L = U^\dagger D_L U$, and added machine-checked 2D and 3D unitary witnesses.
5. **Markov Joint Representation & Absorbing Boundary**:
   - Formulated both the periodic stroboscopic kernel $P_{\mathrm{week}}$ and a
     homogeneous 12-state `(partner, regime)` Markov chain, proved absorbing point-mass
     invariance, and demonstrated divergence between stroboscopic attention occupancy
     ($G_4$ at `0.3779`) and static support dominance ($G_4$ at `0.1458`).
6. **Separated Poke Mechanics & Finite-Network Cascade Thresholds**:
   - Separated subspace projection (`P_k |Psi> / ||P_k |Psi>||`), exit renormalization
     with explicit $n=1$ singleton handling, and finite-$n=8$ percolation crossovers
     (distinguishing asymptotic $R_0 = 1$ at $q = 0.1984$ from finite-$n$ broadening
     and $p_{\mathrm{tx}}$ sensitivity).
7. **Extended Optionality, Falsifiable Hypotheses, and Scope Table**:
   - Added heterogeneous Poisson-binomial bounds, capacity-constrained ($B_{\max}=3$)
     negative-correlation sweeps, an 8-part falsifiable hypothesis chapter (`H1` to `H4`),
     and a comprehensive Assumptions, Scope Conditions, and Failure Modes ledger.
8. **Modular 20-File Lean 4 Suite & Python Invariant Tests**:
   - Replaced 4 flat Lean files with 20 modular Lean files (`RST.Foundations`,
     `RST.Relational`, `RST.Superposition`, `RST.Uncertainty`, `RST.Dynamics`,
     `RST.Optionality`) plus `tests/test_rst_invariants.py` integrated into `Makefile`.

## 2. Complete Theorem-to-Implementation Status Table

| Claim / Result | Paper Ref | Epistemic Status | Verification Method & Location |
| :-- | :-- | :-- | :-- |
| Pareto failure & weighting sensitivity | Prop `prop:order-failure` | Established Math | Analytic + `RST.Relational.RoleDominance.ex_aggregation_rank_reversal` |
| Zero-safe column normalization | Def `def:role-matrix` | Formally verified | `RST.Relational.RoleMatrix.colNormalize_sum_one`, `colNormalize_zero_col` |
| Composite tensor state norm | Lem `lem:composite-norm` | Formally verified | `RST.Superposition.States.composite_state_norm_one` |
| Ordinal rank bounds `[1, n]` | Def `def:rank` | Formally verified | `RST.Relational.Ranking.ordinalRank_ge_one`, `ordinalRank_le_n` |
| Distributed weights => `w_k < 1` | Prop `prop:nobody-first`(1) | Formally verified | `RST.Relational.SharedMaximum.subunit_weights_of_distributed` |
| SharedMax excludes UniqueMax | Prop `prop:nobody-first`(2) | Formally verified | `RST.Relational.SharedMaximum.shared_max_excludes_unique_max` |
| `DistributedWeights` != `SharedMaximum` (`w99`) | Prop `prop:nobody-first`(3) | Formally verified | `RST.Relational.SharedMaximum.distributed_not_implies_shared_max` |
| Complex Cauchy-Schwarz over `Q[i]^d` | Lem `lem:app-cs` | Formally verified | `RST.Foundations.Vectors.cauchy_schwarz_cpx` |
| Diagonal operators commute | Prop `prop:diag-commute` | Formally verified | `RST.Uncertainty.Commutator.diagMat_commute` |
| `U^dagger D U` preserves Hermiticity | Eq `eq:rotated-role` | Formally verified | `RST.Uncertainty.Commutator.conjugateBy_hermitian` |
| Schrodinger & Robertson inequalities | Thm `thm:rank-role-inequality` | Formally verified | `RST.Uncertainty.Robertson.{schrodinger_uncertainty,robertson_uncertainty}` |
| 2D & 3D rational unitary witnesses | Ex `ex:uncertainty-2x2`, `3x3` | Formally verified + Python | `ex_2d_schrodinger_verified`, `ex_3d_schrodinger_verified` + `test_rst_invariants.py` |
| Popoviciu spectral upper bound | Prop `prop:popoviciu` | Analytically derived | Analytic proof in Sec `sec:uncertainty` |
| Minimum-uncertainty saturation (`d=2`) | Prop `prop:minimum-uncertainty` | Analytically derived + Numerically validated | Proof in Sec `sec:uncertainty` + `uncertainty_sweep.csv` (`d=2`) |
| 3,200-sample unitary uncertainty sweep | Exp 5 (`202604`) | Numerically validated | `run_simulations.py` + `test_rst_invariants.py` (0 violations) |
| Doeblin mixing & stationary `P_week` / `P_aug` | Prop `prop:stationary` | Analytically derived + Numerically validated | `lem:app-doeblin` + `stepDist`, `test_markov_kernels` |
| Absorbing point-mass invariance & EMA | Sec `subsec:dyn-stationary` | Formally verified | `RST.Dynamics.StateTransitions.{absorbing_point_mass_invariant,emaUpdate}` |
| Subspace projection & Pythagorean norm | Sec `subsec:poke-rule` | Formally verified | `RST.Superposition.Projection.{projSubspace_idempotent,projSubspace_pythagorean}` |
| Poke Rule collapse probabilities | Prin `prin:poke-rule` | Behavioral Assumption / Illustrative | Behavioral postulate modeled via `projSubspace` weights |
| Exit renormalization & `n=1` boundary | Prop `prop:renormalization` | Formally verified | `RST.Foundations.Normalization.{removePartner_sum_one,singleton_weight_one}` |
| Entropy decrease on collapse | Prop `prop:irreversibility` | Analytically derived | Direct Shannon inequality in Sec `subsec:poke-irreversibility` |
| Branching `R_0` monotonicity & bounds | Thm `thm:percolation-threshold` | Formally verified + Analytically derived | `RST.Dynamics.NetworkCascades.{cascadeFraction_bounds,reproductionNumber_mono_q}` |
| Finite `n=8` cascade crossovers & `p_tx` | Exp 4 (`202603`) | Simulated only | `run_simulations.py` (`cascade_percolation.csv`, `cascade_ptx_sensitivity.csv`) |
| Bernoulli / Poisson-binomial variance bounds | Sec `subsec:conj-model` | Formally verified | `RST.Optionality.Bernoulli.{bernoulliVar_le_quarter,poissonBinomialVar_le_n_quarter}` |
| Binomial `P(K>=2)` monotonicity & conditional `n(A)` | Thm `thm:optionality-monotonicity` | Formally verified | `RST.Optionality.Binomial.{superpositionProb_step,superpositionProb_mono,conjecture_mono_in_attractiveness}` |
| Capacity-capped sublinear crowding | Exp 3 (`202602`) | Simulated only | `optionality_heterogeneity.csv` (`B_max = 3`) |
| Attractiveness increases pool `n(A)` | Conj `conj:optionality` | Conjectural / Empirical Hypothesis | Untested empirical hypothesis; protocol in Sec `sec:hypotheses` & App `app:instrument` |
| Permutation & relabeling symmetry | Prop `prop:unitary-invariance`, `prop:symmetry` | Analytically derived | Unitary conjugation & graph isomorphism invariance in Sec `sec:symmetry` |
| Query-order & cascade empirical claims (`H1`..`H4`) | Sec `sec:hypotheses` | Conjectural / Empirical Hypothesis | Pre-specified falsifiable study plans; zero empirical data collected |

## 3. Reproducibility Verification Summary

All verification commands pass cleanly from repository root:
- `make lean`: `Build completed successfully (44 jobs)` across 20 `RST` modules + `Main.lean`, zero `sorry`, zero custom axioms.
- `make test`: `Ran 6 tests ... OK` (`tests/test_rst_invariants.py`).
- `make figures`: deterministic datasets (`role_aggregation.csv`, `markov_drift.csv`, `optionality_vs_n.csv`, `optionality_vs_A.csv`, `optionality_heterogeneity.csv`, `cascade_percolation.csv`, `cascade_ptx_sensitivity.csv`, `uncertainty_sweep.csv`, `summary.json`) plus all PDF/SVG plots.
- `make pdf`: compiles [paper/output/rank-role-uncertainty.pdf](paper/output/rank-role-uncertainty.pdf) cleanly with zero errors and zero undefined references or citations.
