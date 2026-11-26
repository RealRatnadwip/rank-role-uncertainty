# Mathematical Audit of RST v1.0

This document records a source-level mathematical and formal-methods audit of
**The Rank-Role Uncertainty Principle: Relational Superposition Theory (RST)**
prior to the v1.1 revision. Every finding below was verified directly against
the LaTeX source (`paper/sections/*.tex`), Lean 4 proofs (`lean/RST/*.lean`),
Python simulation runner (`scripts/run_simulations.py`), build configuration
(`Makefile`), and project documentation (`README.md`, `TECHNICAL.md`).


## Summary of Structural Findings

The v1.0 repository compiled cleanly (`48 pages`, `12 Lean build jobs`,
deterministic simulation CSVs), but source inspection revealed eight major
mathematical and scoping gaps:

1. `nobody_is_first` proved only `w_k < 1` while the prose claimed no unique
   ordinal first position exists.
2. Functional role matrices were introduced descriptively and disconnected from
   both global rank aggregation and the uncertainty operators `R` and `L`.
3. Complex amplitudes and phases were assigned ungrounded behavioral claims
   without contrasting classical lottery mixtures and Hilbert-space states.
4. The Robertson uncertainty relation was presented without acknowledging its
   established identity, without the full Schrodinger covariance term in the
   formal theorem, and with ad hoc matrices rather than operator constructions
   tied to the role matrix.
5. The Markov attention model conflated time-inhomogeneous periodic switching,
   homogeneous stationary variance formulas, instantaneous attention slots,
   and functional role dominance.
6. The Poke Rule conflated projective measurement, partner exit and
   renormalization, and finite-network cascade percolation, while treating an
   infinite-system branching threshold `q_c` as a sharp phase transition at `n = 8`.
7. The Attractiveness-Optionality Conjecture conflated mathematical monotonicity
   of `P(Binomial(n, p) >= 2)` with the empirical claim that attractiveness
   increases `n` or `p`, and omitted heterogeneous and correlated pools.
8. Python simulations had no automated invariant test suite, and the Lean
   formalization covered only four flat files without role matrices, projection
   renormalization, Markov kernels, Bernoulli/Binomial statistics, or finite
   network bounds.


## Detailed Issue Ledger

### Issue 1: Conflation of Subunit Weights (`w_k < 1`) with Absence of a Unique First Rank

- **Original statement or definition:**
  - `paper/sections/03_framework.tex` lines 118-142 (`def:superposition`,
    `prop:nobody-first`): defines superposition as at least two positive weights
    and claims `"who is first?" has no deterministic answer prior to a poke`
    because `w_k < 1` for all `k`.
  - `lean/RST/Superposition.lean` lines 12-47 (`InSuperposition`,
    `nobody_is_first`): proves `∀ k, W.w k < 1`.
- **Mathematical problem:** A weight distribution such as `w = (0.99, 0.01)`
  satisfies `InSuperposition` and `w_k < 1` for all `k`, yet `w_1 > w_2`
  strictly gives individual `1` a unique maximum and ordinal rank `1`.
- **Why it is a problem:** The theorem proves only that no partner holds *all*
  weight (`w_k < 1`), not that no partner holds the *strictly highest* weight.
- **Proposed correction:**
  - Define exact distinctions between ordinal rank `r_i = 1 + #{j : w_j > w_i}`
    (plus tie-breaking), `UniqueMaximum`, `SharedMaximum` (`|argmax(w)| >= 2`),
    functional role dominance, perceived rank, and rank uncertainty.
  - Separate **Model A** (distributed positive weights, permitting a unique
    maximum) from **Model B** (non-unique maximal relational position, an
    explicit stronger structural assumption).
  - Retain `nobody_is_first` in Lean under accurate naming (`subunit_weights_of_distributed`),
    add `UniqueMaximum` and `SharedMaximum`, prove `SharedMaximum -> ¬UniqueMaximum`,
    prove `DistributedWeights` does not imply `SharedMaximum` via exact formal
    counterexample `(99/100, 1/100)`, and verify ordinal rank properties.
- **Impact:** Changes definitions, theorems, prose interpretation, and Lean
  modules (`Relational/Ranking.lean`, `Relational/UniqueMaximum.lean`,
  `Relational/SharedMaximum.lean`).


### Issue 2: Disconnected Role Basis and Missing Role-Matrix Normalization / Aggregation Analysis

- **Original statement or definition:**
  - `paper/sections/03_framework.tex` lines 20-36 (`tab:roles`) and lines
    144-166 (`P_{ij} = |c_{ij}|^2`, `fig_weight_matrix.tex`).
- **Mathematical problem:** Roles are introduced as five illustrative examples
  and row-stochastic squared amplitudes `P_{ij}`, without defining a raw
  contribution matrix `M ∈ R_{>=0}^{n x m}`, specifying entry provenance
  (measured frequencies vs latent parameters vs subjective estimates), defining
  column-wise normalization with zero-column handling, defining per-dimension
  dominance `D_j = argmax_i M_tilde_{ij}`, or analyzing global scalar
  aggregation `G_i(alpha) = sum_j alpha_j M_tilde_{ij}`.
- **Why it is a problem:** Without a formal role matrix and explicit sensitivity
  analysis of `alpha`, claims that "no global ranking exists" are imprecise;
  different `alpha` schemes induce different global rankings, and collapsing
  `M` to `G` destroys multi-dimensional dominance structure.
- **Proposed correction:**
  - Formalize `M ∈ R_{>=0}^{n x m}`, explicit entry-interpretation taxonomy,
    zero-safe column normalization `M_tilde`, per-dimension dominance `D_j`,
    and linear aggregation `G_i(alpha)`.
  - Demonstrate explicitly (both analytically and numerically) how two valid
    weightings `alpha^(1)` and `alpha^(2)` reverse the global ranking of
    partners who dominate disjoint dimensions.
  - Formalize row/column normalization and dominance conditions in Lean
    (`Relational/RoleMatrix.lean`, `Relational/RoleDominance.lean`).
- **Impact:** Changes definitions, adds new section on functional role matrices,
  adds Lean formalization and simulation sensitivity sweeps.


### Issue 3: Unscoped Complex Amplitudes and Quantum Metaphor

- **Original statement or definition:**
  - `paper/sections/03_framework.tex` lines 60-93 (`def:partner-state`,
    `def:system-state`) and lines 72-76: asserts `"The complex phase of c_{ij}
    encodes relational timing and framing coherence"` and equates `|a_i|^2`
    with both primary-partner attention weight and literal collapse probability.
- **Mathematical problem:** No map from behavioral timing to complex phase is
  ever defined; complex phases are therefore ungrounded mathematically while
  being given a behavioral interpretation. Moreover, normalized scores in the
  simplex `Delta^{n-1}` are conflated with empirical event probabilities.
- **Why it is a problem:** Overstates what the complex representation adds
  beyond a classical probability vector `w ∈ Delta^{n-1}`.
- **Proposed correction:**
  - Explicitly compare Classical Weight Vector (`w ∈ Delta^{n-1}`) vs Complex
    Hilbert-Space State (`|Psi> ∈ C^n`).
  - Clarify that complex representation is an algebraic generalization that
    supports unitary basis rotations `U` and non-commuting Hermitian measurement
    contexts, and explicitly state where complex phase is a modelling freedom
    without direct psychometric measurement.
  - Distinguish normalized relational scores from operational selection probabilities.
- **Impact:** Refines definitions, prose, and epistemic tagging across Sections 5-7.


### Issue 4: Ungrounded Rank-Role Operators and Missing Robertson-Schrodinger Attribution

- **Original statement or definition:**
  - `paper/sections/04_uncertainty.tex` lines 36-48, 110-173 (`thm:rank-role-inequality`),
    188-200 (`rem:covariance-bound`), and 292-362 (`ex:uncertainty-2x2`,
    `ex:uncertainty-4x4`).
- **Mathematical problem:**
  1. Presents the Robertson (1929) uncertainty inequality under the internal
     name "Rank-Role Inequality" without citing Robertson (1929) or
     Schrodinger (1930) as the established mathematical theorem.
  2. Drops the anticommutator covariance term `1/2 <{Delta R, Delta L}>` into a
     remark without stating the full Schrodinger uncertainty theorem.
  3. Selects ad hoc Pauli/tridiagonal matrices (`exRank`, `exRole`) that have
     no mathematical relationship to the role matrix `M` or rank vector `r`.
  4. Notes in prose that `"R = diag(1,...,n) plus weak cross-partner coupling"`
     without explaining that diagonal `R` and diagonal `L` in the same basis
     commute (`[R, L] = 0`).
- **Why it is a problem:** Conflates standard Hilbert-space inequalities with
  original RST claims and uses arbitrary matrices to illustrate "inevitable"
  relational uncertainty.
- **Proposed correction:**
  - Explicitly attribute the Robertson (1929) and Schrodinger (1930) uncertainty
    relations to established mathematics, defining centred operators,
    commutator `[R, L]`, and anticommutator `{Delta R, Delta L}`.
  - Construct `R = diag(r_1, ..., r_n)` from the defined ranking observable and
    show explicitly that a diagonal role observable in the same basis commutes
    (`[R, D_L] = 0`).
  - Derive non-commuting role observables explicitly via context-induced
    unitary basis change `L = U^dagger D_L U` constructed from role mixing,
    clearly stating which part is modelling construction vs behavioral claim.
  - Add fully worked 2D and 3D examples verified in Python and Lean (`Uncertainty/`).
- **Impact:** Major revision of uncertainty sections, new Lean `Uncertainty/`
  modules, updated numerical sweeps.


### Issue 5: Conflation of Time-Inhomogeneous Regimes, Homogeneous EMA Variance, and Role Importance in Markov Model

- **Original statement or definition:**
  - `paper/sections/05_dynamics.tex` lines 13-131 (`prop:stationary`,
    `eq:ema-variance`, `ex:markov-2x2`, `fig_markov_drift`).
- **Mathematical problem:**
  1. Defines `S_t ∈ {1,...,n}` as primary attention slot, then uses periodic
     matrices `P^(wd)`, `P^(we)`, `P^(st)` while applying a *homogeneous*
     stationary covariance formula (`eq:ema-variance`) without stating that
     it is an approximation to a homogeneous chain rather than the periodic
     stroboscopic chain `P_week`.
  2. Equates stationary attention occupancy `pi_i` with relational priority
     (`E[w_i(t)] = pi_i`) without distinguishing attention time from role-matrix
     dominance `D_j`.
  3. Omits absorbing-state analysis and explicit state-space specification for
     regime-coupled dynamics (`(S_t, R_t)`).
- **Why it is a problem:** Conflates two distinct stochastic processes and blurs
  time allocation (attention) with structural importance (role matrix).
- **Proposed correction:**
  - Explicitly define the augmented homogeneous Markov chain on `(partner, regime)`
    alongside the periodic stroboscopic operator `P_week`, clearly separating
    exact periodic results from homogeneous approximations.
  - Analyze irreducibility, aperiodicity, transient vs stationary behavior,
    and absorbing states (post-collapse / post-cascade).
  - Show explicitly via worked example and simulation how one partner dominates
    long-run attention occupancy `pi` while another dominates core roles in `M_tilde`.
- **Impact:** Updates dynamics chapter, simulation scripts, invariant tests,
  and adds `Dynamics/Markov.lean` and `Dynamics/StateTransitions.lean`.


### Issue 6: Conflation of Projection, Exit Renormalization, and Finite-Network Cascades

- **Original statement or definition:**
  - `paper/sections/06_poke_collapse.tex` lines 28-117 (`prin:poke-rule`,
    `prop:renormalization`) and `paper/sections/07_decoherence_cascade.tex`
    lines 39-98 (`def:cascade`, `thm:percolation-threshold`, `eq:q-crit`).
- **Mathematical problem:**
  1. Presents projective selection (`|Psi> -> |G_k>`), partner departure
     (`w'_i = w_i / sum_{j != k} w_j`), and network cascade as sequential phases
     of a single operation without separating projection operators `P_k`
     (`P_k |Psi> / ||P_k |Psi>||` for `||P_k |Psi>|| > 0`) from subspace
     restriction / exit.
  2. Does not handle the `n = 1` or zero-remaining-mass edge case cleanly in
     prose (though Lean checks `w_k < 1`).
  3. Applies the Galton-Watson branching threshold `q_c = 1 / ((n - 1) p_tx)`
     to `n = 8` nodes and refers to `q_c` as a sharp percolation transition,
     confusing expected reproduction number `R_0 = 1` in an infinite tree limit
     with smooth finite-graph crossover probabilities.
- **Why it is a problem:** Finite `n = 8` graphs do not undergo sharp phase
  transitions; `R_0 = 1` is only an asymptotic branching reference point.
- **Proposed correction:**
  - Separate (a) projective selection `P_k`, (b) partner exit and
    renormalization (including `n = 1` and zero-mass cases), and (c) social-graph
    cascade `G = (V, E)` with complete graph/transmission/threshold/irreversibility
    specification.
  - Explicitly distinguish branching reproduction number `R_0 = (n - 1) q p_tx`,
    exact finite-network cascade probability, threshold-exceedance probability
    `P(|C|/n >= theta)`, and expected cascade size `E[|C|]`.
  - Add sensitivity sweeps over topology and `p_tx`.
- **Impact:** Separates Poke Rule, removal/renormalization, and cascades into
  distinct chapters; adds `Superposition/Projection.lean` and
  `Dynamics/NetworkCascades.lean`.


### Issue 7: Conflation of Model Properties with Behavioral Hypothesis in Optionality Conjecture

- **Original statement or definition:**
  - `paper/sections/08_conjecture.tex` lines 10-95 (`def:binomial-superposition`,
    `thm:optionality-monotonicity`, `conj:optionality`).
- **Mathematical problem:** Mixes the purely mathematical theorem (that
  `P(Binomial(n, p) >= 2)` increases in `n` and `p`) with the behavioral
  hypothesis (`n(A)` or `p` rises with attractiveness `A`), assumes i.i.d.
  equal-`p` trials without analyzing heterogeneous `p_i` (Poisson-binomial) or
  correlated trials (shared time budget / negative correlation), and omits
  Poisson limit validity conditions (`n` large, `p` small, `np -> lambda`).
- **Why it is a problem:** Readers could mistake a proved property of binomial
  CDFs for proof of a psychological claim about attractiveness.
- **Proposed correction:**
  - Separate (i) Binomial and Poisson-binomial mathematical results (including
    exact expectation/variance, Poisson limit regime, heterogeneous `p_i`, and
    negatively correlated time-budget models) from (ii) the empirical
    Attractiveness-Optionality Conjecture, confounders, and selection effects.
  - Expand Lean `Optionality/` with `Bernoulli.lean` and `Binomial.lean`.
- **Impact:** Expands optionality chapter, simulations, invariant tests, and Lean.


### Issue 8: Missing Automated Invariant Tests, Parameter Sweeps, and Verification Boundaries

- **Original statement or definition:**
  - `Makefile` lacks a `test` target; `scripts/run_simulations.py` writes CSVs
    with no automated assertion suite checking stochastic row sums, unitary/norm
    invariants, finite-network bounds, or Monte Carlo convergence tolerances.
  - `paper/sections/12_limitations.tex` lacks a comprehensive assumptions table
    and falsifiable hypothesis specification matrix.
- **Why it is a problem:** Plausible-looking plots are not mathematical
  validation, and empirical testability requires operationalized hypotheses
  (IV, DV, confounders, `H_0`, `H_1`, falsification criteria).
- **Proposed correction:**
  - Create `tests/test_rst_invariants.py` and wire `make test` into `Makefile`.
  - Expand `scripts/run_simulations.py` with explicit model docstrings and
    parameter sweeps (role aggregation `alpha`, commutator coupling, cascade
    `p_tx`, heterogeneous optionality).
  - Add dedicated **Assumptions, Scope Conditions, and Failure Modes** and
    **Falsifiable Predictions and Empirical Research Pathway** sections plus
    `paper/appendices/revision-report.md`.
- **Impact:** Adds test suite, new simulations, new figures, and comprehensive
  epistemic accountability across monograph and docs.
