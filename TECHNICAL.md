# Technical Notes and Verification

This repository contains the LaTeX monograph, deterministic Monte Carlo
simulation scripts, generated datasets and vector figures, and a standalone
Lean 4 formalization for Relational Superposition Theory.

## Repository Layout and Build Pipeline

The monograph compiles from [paper/main.tex](paper/main.tex) with package and
macro configuration in [paper/preamble.tex](paper/preamble.tex), chapter files
in `paper/sections/`, and bibliographic entries in
[paper/bib/references.bib](paper/bib/references.bib). Intermediate build files go
into `paper/build/` (ignored by git), and only the compiled PDF lands at
[paper/output/rank-role-uncertainty.pdf](paper/output/rank-role-uncertainty.pdf).

All figures are produced in both PDF (for LaTeX inclusion) and SVG (for web
rendering) inside `paper/figures/`:
- [scripts/run_simulations.py](scripts/run_simulations.py) writes deterministic
  CSV outputs and `paper/data/summary.json` using NumPy PCG64 generators.
- [scripts/generate_figures.py](scripts/generate_figures.py) renders the four
  data-driven plots from those CSV files.
- Standalone TikZ diagrams (`fig_weight_matrix.tex`, `fig_collapse.tex`,
  `fig_social_graph.tex`) compile via `pdflatex` and convert to SVG via `pdf2svg`.

## Formal Verification in Lean 4

The Lean project in `lean/` targets Lean `4.36.0` (pinned in
[lean/lean-toolchain](lean/lean-toolchain)) with Lake `5.0.0` and zero external
library dependencies (`Init` only). No `sorry` or custom axioms appear anywhere.

Verified modules and key declarations:
- [lean/RST/Normalization.lean](lean/RST/Normalization.lean): `collapse_probs_sum_one`
  (squared unit amplitudes sum to 1), `removePartner_nonneg`,
  `removePartner_sum_one` (post-removal renormalization preserves validity when
  `w k < 1`), and `renormMask_valid` (arbitrary retained-subset renormalization).
- [lean/RST/Superposition.lean](lean/RST/Superposition.lean): `nobody_is_first`
  and `amplitudes_nobody_is_first` (under at least two positive weights, every
  partner satisfies `w k < 1` and `w k ≠ 1`).
- [lean/RST/Optionality.lean](lean/RST/Optionality.lean): `superpositionProb_step`
  (exact marginal identity `f(p, n+1) - f(p, n) = n * p^2 * (1 - p)^(n - 1)`),
  `superpositionProb_mono`, `superpositionProb_strict_step`, and
  `conjecture_mono_in_attractiveness`.
- [lean/RST/Uncertainty.lean](lean/RST/Uncertainty.lean): `cauchy_schwarz_cpx`
  over the Gaussian rationals `Q[i]^d`, `dotC_hermitian_self_im`,
  `rank_role_uncertainty` (`4 * var R psi * var L psi >= (Im <psi, [R, L]psi>)^2`),
  and concrete non-commuting witness `ex_super_uncertainty_positive`.

What is not machine-checked in Lean: continuous real-analytic properties of
Shannon entropy and Markov mixing rates (Sections 3 and 5), asymptotic
Galton-Watson percolation survival probabilities (Section 7), the empirical
premise `n'(A) > 0` in the Attractiveness-Optionality Conjecture (Section 8),
and floating-point Monte Carlo runs in `scripts/run_simulations.py`.

## Key Simulation Parameters and Seeds

- Attention drift (`SEED_MARKOV = 202601`, 180 half-day steps, 20,000-week
  check): stress probability `p_st = 0.15`, EMA smoothing `alpha = 0.16`.
- Optionality scaling (`SEED_OPTIONALITY = 202602`, 4,000 trials per grid
  point): retention probability `p in {0.25, 0.45, 0.65}`, attractiveness grid
  `A in [0, 10]` with Poisson pool mean `0.35 * exp(0.32 * A)`.
- Social-graph percolation (`SEED_CASCADE = 202603`, 1,500 trials per density):
  `n = 8` partners, note-sharing probability `p_tx = 0.72`, cascade threshold
  `theta = 0.60`, comparing homogeneous, clustered, and hub-mediated graphs.
- Uncertainty operator sweep (`SEED_UNCERTAINTY = 202604`, 2,400 samples):
  dimensions `d in {2, 3, 4, 5}`, coupling `gamma in {0.25, 0.75, 1.50}`.

Known limits of the models (observer reactivity under direct probing, selection
bias, non-universality of `kappa`, role-basis orthogonality, and independence
assumptions in retention and percolation) are documented in Section 12 of the
monograph.

## Check It Yourself

Run the full deterministic pipeline from the repository root:

```bash
make figures
make lean
make pdf
```

Expected output and reproducible reference values:
1. `make figures` populates 5 CSVs plus `summary.json` in `paper/data/` and
   14 vector files (7 PDF, 7 SVG) in `paper/figures/`. In `summary.json`:
   - `stationary_theory`: `[0.2511, 0.2248, 0.1462, 0.3779]`
   - `p_superposition_n5_p45_exact`: `0.743782` (`mc`: `0.73175`)
   - `q_crit_analytic`: `0.1984` (`cascade_er_q02`: `0.293333`)
   - `uncertainty.violations`: `0`, `min_ratio_prod_over_bound`: `1.0`
2. `make lean` prints `Build completed successfully (12 jobs)` with exit code `0`.
3. `make pdf` writes [paper/output/rank-role-uncertainty.pdf](paper/output/rank-role-uncertainty.pdf)
   (48 pages, author `Ratnadwip Sarkar`, zero TeX errors or undefined references).
