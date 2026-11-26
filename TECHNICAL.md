# Technical Architecture and Verification (v1.1)

This repository holds the LaTeX monograph, deterministic Monte Carlo and
linear-algebra simulation scripts, invariant tests, generated datasets and
vector figures, and a modular Lean 4 formalization for Relational Superposition
Theory (RST).

## Repository Layout and Build Pipeline

- Monograph sources live in [paper/main.tex](paper/main.tex),
  [paper/preamble.tex](paper/preamble.tex), `paper/sections/`, and
  [paper/bib/references.bib](paper/bib/references.bib). Intermediate artifacts
  go to `paper/build/`, and the compiled PDF lands at
  [paper/output/rank-role-uncertainty.pdf](paper/output/rank-role-uncertainty.pdf).
- Source-level mathematical audit and v1.1 revision summary live at
  [paper/appendices/mathematical-audit.md](paper/appendices/mathematical-audit.md)
  and [paper/appendices/revision-report.md](paper/appendices/revision-report.md).
- Simulation and plotting pipeline:
  - [scripts/run_simulations.py](scripts/run_simulations.py) runs five
    deterministic experiments (NumPy PCG64) writing CSV tables and
    [paper/data/summary.json](paper/data/summary.json).
  - [scripts/generate_figures.py](scripts/generate_figures.py) generates six
    publication PDF/SVG plots from the CSV outputs, while standalone TikZ
    diagrams (`fig_weight_matrix.tex`, `fig_collapse.tex`, `fig_social_graph.tex`)
    render via `pdflatex` and `pdf2svg`.
- Automated invariant tests live in [tests/test_rst_invariants.py](tests/test_rst_invariants.py)
  covering both direct algebraic properties of simulation helpers and invariants
  over generated CSV outputs.

## Modular Formal Verification in Lean 4

The Lean suite in `lean/` targets Lean `4.36.0` (pinned in
[lean/lean-toolchain](lean/lean-toolchain)) with Lake `5.0.0` and pure standard
`Init` (no external dependencies, zero `sorry`, zero `admit`, zero custom axioms).

Library root [lean/RST.lean](lean/RST.lean) and executable entrypoint
[lean/Main.lean](lean/Main.lean) organize 20 modules across six namespaces:

- `RST.Foundations`:
  - `FiniteSets`: recursive `sumFin` linearity lemmas and boolean counting `countFin`.
  - `Vectors`: Gaussian rational vectors over `Q[i]^d`, conjugate transpose dot products,
    and division-free complex Cauchy-Schwarz (`cauchy_schwarz_cpx`).
  - `Normalization`: simplex weights (`Weights`), guarded exit renormalization
    (`removePartner_sum_one`), masked subset renormalization (`renormMask_valid`),
    and the `n = 1` singleton boundary (`singleton_weight_one`).
  - `Probability`: discrete distributions (`ProbDist`), expectations, and non-negative
    variance (`varianceVal_nonneg`).
- `RST.Relational`:
  - `RoleMatrix`: non-negative raw matrix normalization with zero-column safety
    (`colNormalize_sum_one`, `colNormalize_zero_col`).
  - `RoleDominance`: dimension dominance and explicit rank-reversal witness
    (`ex_aggregation_rank_reversal`).
  - `Ranking`: competition ordinal rank `1 + #{j : w_j > w_i}` (`ordinalRank_ge_one`,
    `ordinalRank_le_n`, tie invariance).
  - `UniqueMaximum`: uniqueness of global maximizer and strict rank-1 characterization.
  - `SharedMaximum`: separates Model A (`DistributedWeights`) from Model B (`SharedMaximum`),
    proving `subunit_weights_of_distributed`, `shared_max_excludes_unique_max`, and the
    formal refutation `distributed_not_implies_shared_max` via `w99 = (99/100, 1/100)`.
- `RST.Superposition`:
  - `Amplitudes`: real and Gaussian-rational collapse weights summing to 1.
  - `States`: tensor product composite state unit norm (`composite_state_norm_one`).
  - `Projection`: orthogonal subspace projector idempotence, Pythagorean split, and
    unit norm of normalized post-projection vectors (`projected_vector_unit_norm`).
- `RST.Uncertainty`:
  - `Operators`: `IsHermitian`, `IsUnitary`, real expectation property, centered variance.
  - `Commutator`: diagonal operator commutativity (`diagMat_commute`), centered
    anticommutator, and Hermiticity preservation under `U^dagger D U` (`conjugateBy_hermitian`).
  - `Robertson`: full finite-dimensional Schrodinger uncertainty inequality
    (`schrodinger_uncertainty`), Robertson corollary (`robertson_uncertainty`), plus
    verified 2D (`U2_unitary`, `ex_2d_schrodinger_verified`) and 3D
    (`ex_3d_schrodinger_verified`) unitary witnesses.
- `RST.Dynamics`:
  - `Markov`: row-stochastic matrices, `stepDist` propagation, convex regime mixtures.
  - `StateTransitions`: absorbing state invariance (`absorbing_point_mass_invariant`)
    and valid EMA weight updates (`emaUpdate`).
  - `NetworkCascades`: simple graph bounds (`cascadeFraction_bounds`) and monotonic
    branching reproduction number (`reproductionNumber_mono_q`).
- `RST.Optionality`:
  - `Bernoulli`: Bernoulli variance bound `p*(1 - p) <= 1/4` and Poisson-binomial
    mean and variance bounds (`poissonBinomialVar_le_n_quarter`).
  - `Binomial`: exact incremental formula `superpositionProb_step`, monotonicity in `n`
    (`superpositionProb_mono`), strict step positivity, and conditional monotonicity
    `conjecture_mono_in_attractiveness`.

## Simulation Ledger and Seeds

1. **Role aggregation (`SEED_ROLE_AGG = 202605`)**: `4 x 5` matrix normalization,
   comparison of `alpha_vis` vs `alpha_sup` rank reversal (`G_1` at `0.4167` vs
   `G_2` at `0.3508`), and 1,000 `Dirichlet(1,...,1)` samples yielding Top-1 shares
   `[227, 190, 253, 330]`. Outputs `paper/data/role_aggregation.csv`.
2. **Markov drift (`SEED_MARKOV = 202601`)**: 180 half-day steps (`p_st = 0.15`,
   EMA `alpha = 0.16`), periodic weekly stroboscopic stationary vector
   `[0.2511, 0.2248, 0.1462, 0.3779]`, and `12 x 12` homogeneous joint marginal
   `[0.3334, 0.3087, 0.1741, 0.1838]`. Outputs `paper/data/markov_drift.csv`.
3. **Optionality (`SEED_OPTIONALITY = 202602`)**: 4,000 trials per grid point on
   `n in {1..10}` (`p in {0.25, 0.45, 0.65}`), `A in [0, 10]`, heterogeneous
   Poisson-binomial retention, and time-budget crowding (`B_max = 3`, mean kept `3.4947`
   vs unconstrained `4.5000` at `n = 10`). Outputs `optionality_vs_n.csv`,
   `optionality_vs_A.csv`, and `optionality_heterogeneity.csv`.
4. **Cascade percolation (`SEED_CASCADE = 202603`)**: `n = 8`, 1,500 trials per edge
   density across ER, clustered two-clique, and hub topologies at `p_tx = 0.72`
   (`R_0 = 1` at `q = 0.1984`) plus `p_tx in {0.40, 0.72, 0.90}` sensitivity. Outputs
   `cascade_percolation.csv` and `cascade_ptx_sensitivity.csv`.
5. **Operator uncertainty (`SEED_UNCERTAINTY = 202604`)**: 3,200 Haar-random states
   across `d in {2, 3, 4, 5}` and `gamma in {0.0, 0.25, 0.75, 1.50}` with
   `L(gamma) = U(gamma)^dagger D_L U(gamma)`. Outputs `uncertainty_sweep.csv`
   with `0` Robertson violations and `0` Schrodinger violations.

## Full Reproduction Pipeline

```bash
make figures   # runs simulations, matplotlib figures, and TikZ diagrams
make lean      # runs lake build (44 jobs across 20 RST modules + Main)
make test      # runs python3 -m unittest discover -s tests -v (6 test suites)
make pdf       # compiles paper/main.tex to paper/output/rank-role-uncertainty.pdf
```

`make all` executes all four targets sequentially (`figures -> lean -> test -> pdf`).
