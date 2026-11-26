"""Deterministic Monte Carlo simulations for Relational Superposition Theory.

Generates reproducible CSV datasets and summary statistics in paper/data/
using fixed PCG64 seeds for all numerical figures and tables in the paper.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "paper" / "data"

SEED_MARKOV = 202601
SEED_OPTIONALITY = 202602
SEED_CASCADE = 202603
SEED_UNCERTAINTY = 202604


def simulate_markov_drift() -> dict:
    """Simulate 90-day attention-weight trajectory and long-run stationary weights."""
    rng = np.random.default_rng(SEED_MARKOV)

    # Four partners: G1 (weekday/photo primary), G2 (late-night emotional),
    # G3 (practical/dinner), G4 (weekend entertainment)
    # Transition matrices over active attention state S_t in {0, 1, 2, 3}
    p_weekday = np.array([
        [0.62, 0.18, 0.14, 0.06],
        [0.24, 0.54, 0.14, 0.08],
        [0.28, 0.18, 0.44, 0.10],
        [0.30, 0.20, 0.15, 0.35],
    ])
    p_weekend = np.array([
        [0.44, 0.12, 0.14, 0.30],
        [0.20, 0.32, 0.12, 0.36],
        [0.22, 0.14, 0.28, 0.36],
        [0.16, 0.10, 0.12, 0.62],
    ])
    p_stress = np.array([
        [0.30, 0.52, 0.12, 0.06],
        [0.14, 0.72, 0.08, 0.06],
        [0.20, 0.50, 0.22, 0.08],
        [0.22, 0.48, 0.12, 0.18],
    ])

    # Weekly kernel: 5 weekdays + 2 weekend days, with stress probability 0.15/day
    # Compute exact time-averaged transition matrix for stationary reference
    p_week = (
        np.linalg.matrix_power(0.85 * p_weekday + 0.15 * p_stress, 5)
        @ np.linalg.matrix_power(0.85 * p_weekend + 0.15 * p_stress, 2)
    )
    eigvals, eigvecs = np.linalg.eig(p_week.T)
    idx = np.argmin(np.abs(eigvals - 1.0))
    pi_theory = np.real(eigvecs[:, idx])
    pi_theory = pi_theory / np.sum(pi_theory)

    # Simulate EMA-smoothed attention weights w_i(t) over 90 days (half-day steps = 180)
    n_days = 90
    alpha_ema = 0.16
    w = np.array([0.34, 0.26, 0.20, 0.20], dtype=float)
    state = 0

    rows = []
    for step in range(n_days * 2):
        day = step // 2
        dow = day % 7
        is_weekend = dow >= 5
        is_stress = rng.random() < 0.15
        if is_stress:
            mat = p_stress
            regime = "stress"
        elif is_weekend:
            mat = p_weekend
            regime = "weekend"
        else:
            mat = p_weekday
            regime = "weekday"

        state = int(rng.choice(4, p=mat[state]))
        one_hot = np.zeros(4)
        one_hot[state] = 1.0
        w = (1.0 - alpha_ema) * w + alpha_ema * one_hot
        w = w / np.sum(w)

        entropy = float(-np.sum(w * np.log2(np.clip(w, 1e-12, 1.0))))
        rows.append({
            "step": step,
            "day": round(step * 0.5, 1),
            "regime": regime,
            "w1": round(float(w[0]), 6),
            "w2": round(float(w[1]), 6),
            "w3": round(float(w[2]), 6),
            "w4": round(float(w[3]), 6),
            "entropy_bits": round(entropy, 6),
        })

    # Long-run empirical check (20,000 weeks)
    counts = np.zeros(4, dtype=int)
    s = 0
    for _ in range(20000):
        for d in range(7):
            is_stress = rng.random() < 0.15
            mat = p_stress if is_stress else (p_weekend if d >= 5 else p_weekday)
            s = int(rng.choice(4, p=mat[s]))
        counts[s] += 1
    pi_emp = counts / np.sum(counts)

    out_path = DATA_DIR / "markov_drift.csv"
    with out_path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    return {
        "seed": SEED_MARKOV,
        "n_steps": len(rows),
        "stationary_theory": [round(float(x), 4) for x in pi_theory],
        "stationary_empirical_weekly": [round(float(x), 4) for x in pi_emp],
        "final_entropy_bits": rows[-1]["entropy_bits"],
    }


def simulate_optionality_and_collapse() -> dict:
    """Simulate Attractiveness-Optionality scaling and partner-count collapse hazard."""
    rng = np.random.default_rng(SEED_OPTIONALITY)
    n_trials = 4000

    # Part A: Superposition probability vs viable partner pool n = 1..10
    p_values = [0.25, 0.45, 0.65]
    rows_n = []
    for n in range(1, 11):
        row: dict[str, float | int] = {"n_partners": n}
        for p in p_values:
            exact = 0.0 if n < 2 else float(1.0 - (1.0 - p) ** n - n * p * (1.0 - p) ** (n - 1))
            active_counts = rng.binomial(n, p, size=n_trials)
            mc = float(np.mean(active_counts >= 2))
            tag = str(int(round(p * 100)))
            row[f"exact_p{tag}"] = round(exact, 6)
            row[f"mc_p{tag}"] = round(mc, 6)
        # Expected collapse hazard per unit time under independent poke rate h0=0.08 per active partner
        # plus pairwise visibility exposure
        row["collapse_hazard_30d"] = round(float(1.0 - np.exp(-0.08 * n * (1.0 + 0.12 * (n - 1)))), 6)
        rows_n.append(row)

    with (DATA_DIR / "optionality_vs_n.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows_n[0].keys()))
        writer.writeheader()
        writer.writerows(rows_n)

    # Part B: Attractiveness A in [0, 10] -> Poisson viable option pool lambda(A) = 0.35 * exp(0.32 * A)
    rows_a = []
    a_grid = np.linspace(0.0, 10.0, 21)
    for a_val in a_grid:
        lam = 0.35 * float(np.exp(0.32 * a_val))
        pool = rng.poisson(lam, size=n_trials)
        row_a: dict[str, float] = {"attractiveness_A": round(float(a_val), 2), "mean_pool": round(float(np.mean(pool)), 4)}
        for p in p_values:
            kept = np.array([rng.binomial(k, p) if k > 0 else 0 for k in pool])
            tag = str(int(round(p * 100)))
            row_a[f"p_superposition_p{tag}"] = round(float(np.mean(kept >= 2)), 6)
        rows_a.append(row_a)

    with (DATA_DIR / "optionality_vs_A.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows_a[0].keys()))
        writer.writeheader()
        writer.writerows(rows_a)

    return {
        "seed": SEED_OPTIONALITY,
        "n_trials": n_trials,
        "p_superposition_n5_p45_exact": rows_n[4]["exact_p45"],
        "p_superposition_n5_p45_mc": rows_n[4]["mc_p45"],
        "p_superposition_A2_p45": rows_a[4]["p_superposition_p45"],
        "p_superposition_A8_p45": rows_a[16]["p_superposition_p45"],
    }


def _run_cascade_trial(
    rng: np.random.Generator,
    n: int,
    q: float,
    topology: str,
    tx_prob: float = 0.72,
    collapse_frac_threshold: float = 0.60,
) -> tuple[bool, float]:
    """Run one social-graph decoherence cascade trial from a single poked partner."""
    adj = np.zeros((n, n), dtype=bool)
    if topology == "erdos_renyi":
        upper = rng.random((n, n)) < q
        upper = np.triu(upper, 1)
        adj = upper | upper.T
    elif topology == "clustered":
        # Two overlapping social circles with intra-circle boost and bridge probability q
        half = n // 2
        for i in range(n):
            for j in range(i + 1, n):
                same_group = (i < half and j < half) or (i >= half and j >= half)
                p_edge = min(1.0, 1.8 * q) if same_group else 0.45 * q
                if rng.random() < p_edge:
                    adj[i, j] = adj[j, i] = True
    elif topology == "hub_mediated":
        # Hub partner 0 connects to others with prob min(1, 1.6*q); others connect with 0.35*q
        for i in range(1, n):
            if rng.random() < min(1.0, 1.6 * q):
                adj[0, i] = adj[i, 0] = True
        for i in range(1, n):
            for j in range(i + 1, n):
                if rng.random() < 0.35 * q:
                    adj[i, j] = adj[j, i] = True

    # Seed poke at random partner; partner compares notes along open transmission edges
    seed_node = int(rng.integers(0, n))
    exposed = np.zeros(n, dtype=bool)
    exposed[seed_node] = True
    queue = [seed_node]
    while queue:
        u = queue.pop(0)
        neighbors = np.where(adj[u])[0]
        for v in neighbors:
            if not exposed[v] and rng.random() < tx_prob:
                exposed[v] = True
                queue.append(int(v))

    frac = float(np.sum(exposed)) / float(n)
    total_decoherence = frac >= collapse_frac_threshold
    return total_decoherence, frac


def simulate_cascade_percolation() -> dict:
    """Simulate decoherence cascade probability across graph density and topology."""
    rng = np.random.default_rng(SEED_CASCADE)
    n_trials = 1500
    n_partners = 8
    q_grid = np.linspace(0.0, 1.0, 21)
    topologies = ["erdos_renyi", "clustered", "hub_mediated"]

    rows = []
    for q in q_grid:
        row: dict[str, float] = {"edge_density_q": round(float(q), 3)}
        for topo in topologies:
            cascades = 0
            frac_sum = 0.0
            for _ in range(n_trials):
                tot, frac = _run_cascade_trial(rng, n_partners, float(q), topo)
                cascades += int(tot)
                frac_sum += frac
            row[f"cascade_{topo}"] = round(cascades / n_trials, 6)
            row[f"mean_exposed_{topo}"] = round(frac_sum / n_trials, 6)
        # Analytic giant-component reference threshold q_c = 1 / ((n - 1) * tx_prob)
        rows.append(row)

    with (DATA_DIR / "cascade_percolation.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    q_crit_analytic = 1.0 / ((n_partners - 1) * 0.72)
    return {
        "seed": SEED_CASCADE,
        "n_partners": n_partners,
        "n_trials": n_trials,
        "tx_prob": 0.72,
        "q_crit_analytic": round(q_crit_analytic, 4),
        "cascade_er_q02": rows[4]["cascade_erdos_renyi"],
        "cascade_er_q06": rows[12]["cascade_erdos_renyi"],
    }


def simulate_uncertainty_sweep() -> dict:
    """Sample Hermitian rank/role operators and superposed states to inspect uncertainty bound."""
    rng = np.random.default_rng(SEED_UNCERTAINTY)
    n_samples = 600
    rows = []
    min_ratio = 1e9
    violations = 0

    for d in [2, 3, 4, 5]:
        # Rank operator diagonal 1..d plus small coupling perturbation
        r_diag = np.diag(np.arange(1, d + 1, dtype=complex))
        for gamma in [0.25, 0.75, 1.50]:
            for _ in range(n_samples // 3):
                # Random Hermitian perturbation for off-diagonal role mixing
                a = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
                h_mix = 0.5 * (a + a.conj().T)
                h_mix = h_mix / max(1e-8, float(np.linalg.norm(h_mix, ord=2)))
                op_r = r_diag + 0.15 * gamma * h_mix

                # Role operator with distinct diagonal plus non-commuting complex off-diagonals
                l_diag = np.diag(np.linspace(-1.0, 1.0, d))
                b = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
                l_mix = 0.5 * (b + b.conj().T)
                l_mix = l_mix / max(1e-8, float(np.linalg.norm(l_mix, ord=2)))
                op_l = l_diag + gamma * l_mix

                # Random normalized superposed state
                psi = rng.normal(size=d) + 1j * rng.normal(size=d)
                psi = psi / np.linalg.norm(psi)

                exp_r = float(np.real(np.vdot(psi, op_r @ psi)))
                exp_l = float(np.real(np.vdot(psi, op_l @ psi)))
                u = (op_r - exp_r * np.eye(d)) @ psi
                v = (op_l - exp_l * np.eye(d)) @ psi
                delta_r = float(np.linalg.norm(u))
                delta_l = float(np.linalg.norm(v))
                prod = delta_r * delta_l

                comm_psi = (op_r @ op_l - op_l @ op_r) @ psi
                kappa_comm = 0.5 * abs(float(np.imag(np.vdot(psi, comm_psi))))

                if prod + 1e-12 < kappa_comm:
                    violations += 1
                if kappa_comm > 1e-9:
                    min_ratio = min(min_ratio, prod / kappa_comm)

                rows.append({
                    "dim": d,
                    "gamma": gamma,
                    "delta_R": round(delta_r, 6),
                    "delta_L": round(delta_l, 6),
                    "product": round(prod, 6),
                    "kappa_bound": round(kappa_comm, 6),
                    "slack": round(prod - kappa_comm, 6),
                })

    with (DATA_DIR / "uncertainty_sweep.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    prods = np.array([r["product"] for r in rows])
    bounds = np.array([r["kappa_bound"] for r in rows])
    return {
        "seed": SEED_UNCERTAINTY,
        "total_samples": len(rows),
        "violations": violations,
        "min_ratio_prod_over_bound": round(min_ratio, 4),
        "median_product": round(float(np.median(prods)), 4),
        "median_kappa_bound": round(float(np.median(bounds)), 4),
    }


def main() -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    summary = {
        "markov": simulate_markov_drift(),
        "optionality": simulate_optionality_and_collapse(),
        "cascade": simulate_cascade_percolation(),
        "uncertainty": simulate_uncertainty_sweep(),
    }
    out_json = DATA_DIR / "summary.json"
    out_json.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
