"""Deterministic mathematical simulations and parameter sweeps for RST v1.2.

Every simulation corresponds explicitly to a formal model in the monograph:
1. Role Matrix Normalization & Aggregation Sensitivity (SEED_ROLE_AGG = 202605)
2. Joint Regime-Partner Markov Chain & Periodic EMA Drift (SEED_MARKOV = 202601)
3. Unitary Context-Rotated Robertson & Schrodinger Sweep (SEED_UNCERTAINTY = 202604)
4. Finite-Network Cascade Percolation & p_tx Sensitivity (SEED_CASCADE = 202603)
5. Homogeneous, Heterogeneous, and Time-Budget Optionality (SEED_OPTIONALITY = 202602)
"""

from __future__ import annotations

import csv
import json
from pathlib import Path

import numpy as np
from scipy.linalg import expm

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "paper" / "data"

SEED_MARKOV = 202601
SEED_OPTIONALITY = 202602
SEED_CASCADE = 202603
SEED_UNCERTAINTY = 202604
SEED_ROLE_AGG = 202605


# ===========================================================================
# Core mathematical helpers (imported directly by tests/test_rst_invariants.py)
# ===========================================================================

def normalize_role_matrix_cols(mat: np.ndarray) -> np.ndarray:
    """Column-normalize a nonnegative n x m role matrix, mapping zero columns to 0."""
    mat = np.asarray(mat, dtype=float)
    col_sums = mat.sum(axis=0, keepdims=True)
    out = np.zeros_like(mat)
    nz = col_sums[0] > 0.0
    out[:, nz] = mat[:, nz] / col_sums[:, nz]
    return out


def ordinal_ranks_desc(scores: np.ndarray) -> np.ndarray:
    """Competition ordinal rank r_i = 1 + #{j : scores[j] > scores[i]}."""
    scores = np.asarray(scores, dtype=float)
    return np.array([1 + int(np.sum(scores > scores[i] + 1e-12)) for i in range(len(scores))], dtype=int)


def project_and_normalize(psi: np.ndarray, mask: np.ndarray) -> np.ndarray:
    """Apply orthogonal subspace projection mask and renormalize when norm > 0."""
    proj = np.where(mask, psi, 0.0 + 0.0j)
    norm = float(np.linalg.norm(proj))
    if norm <= 0.0:
        raise ValueError("Cannot normalize a zero projection.")
    return proj / norm


def remove_partner_weights(weights: np.ndarray, k: int) -> np.ndarray:
    """Remove partner k and renormalize remaining nonnegative weights."""
    rem = float(np.sum(weights) - weights[k])
    if rem <= 0.0:
        raise ValueError("Remaining weight mass must be positive.")
    out = np.array(weights, dtype=float, copy=True)
    out[k] = 0.0
    return out / rem


def build_unitary_context(dim: int, gamma: float, generator_h: np.ndarray) -> np.ndarray:
    """Construct unitary context change U(gamma) = exp(i * gamma * H) from Hermitian H."""
    return expm(1j * gamma * generator_h)


def uncertainty_metrics(op_r: np.ndarray, op_l: np.ndarray, psi: np.ndarray) -> dict[str, float]:
    """Compute dispersions, Robertson bound, covariance term, and Schrodinger bound."""
    psi = psi / np.linalg.norm(psi)
    exp_r = float(np.real(np.vdot(psi, op_r @ psi)))
    exp_l = float(np.real(np.vdot(psi, op_l @ psi)))
    r_c = op_r - exp_r * np.eye(len(psi))
    l_c = op_l - exp_l * np.eye(len(psi))
    u = r_c @ psi
    v = l_c @ psi
    delta_r = float(np.linalg.norm(u))
    delta_l = float(np.linalg.norm(v))
    prod = delta_r * delta_l

    comm_val = np.vdot(psi, (op_r @ op_l - op_l @ op_r) @ psi)
    robertson = 0.5 * abs(float(np.imag(comm_val)))
    anticomm_val = np.vdot(psi, (r_c @ l_c + l_c @ r_c) @ psi)
    cov_term = 0.5 * abs(float(np.real(anticomm_val)))
    schrodinger = float(np.sqrt(robertson ** 2 + cov_term ** 2))
    return {
        "delta_R": delta_r,
        "delta_L": delta_l,
        "product": prod,
        "robertson_bound": robertson,
        "cov_term": cov_term,
        "schrodinger_bound": schrodinger,
    }


def markov_regime_kernels() -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return canonical weekday, weekend, and stress 4x4 transition matrices."""
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
    return p_weekday, p_weekend, p_stress


def build_joint_regime_chain(p_st: float = 0.15) -> np.ndarray:
    """Build 12x12 homogeneous Markov kernel over (partner in 0..3, regime in {wd, we, st})."""
    p_wd, p_we, p_st_m = markov_regime_kernels()
    # Regime chain: wd(0) -> wd(5/7*(1-p_st)), we(2/7*(1-p_st)), st(p_st)
    # Using exact stationary regime weights (5/7*(1-p_st), 2/7*(1-p_st), p_st) for i.i.d. day type
    reg_probs = np.array([(5.0 / 7.0) * (1.0 - p_st), (2.0 / 7.0) * (1.0 - p_st), p_st])
    mats = [p_wd, p_we, p_st_m]
    joint = np.zeros((12, 12), dtype=float)
    for r_curr in range(3):
        for r_next in range(3):
            block = reg_probs[r_next] * mats[r_next]
            joint[r_curr * 4:(r_curr + 1) * 4, r_next * 4:(r_next + 1) * 4] = block
    return joint


# ===========================================================================
# Experiment runners
# ===========================================================================

def simulate_role_aggregation() -> dict:
    """Experiment 1: Column normalization and Dirichlet alpha sensitivity on 4x5 role matrix."""
    rng = np.random.default_rng(SEED_ROLE_AGG)

    # Canonical 4-partner, 5-role latent score matrix M (rows G1..G4, cols r1..r5)
    raw_m = np.array([
        [8.5, 3.0, 2.0, 3.5, 1.0],  # G1 dominates r1 (Primary)
        [2.5, 9.0, 1.5, 2.0, 1.5],  # G2 dominates r2 (Emotional)
        [1.5, 2.0, 8.8, 1.8, 2.0],  # G3 dominates r3 (Financial)
        [1.5, 1.8, 1.2, 8.2, 4.5],  # G4 dominates r4 (Weekend) and r5 (Contingency)
    ])
    m_norm = normalize_role_matrix_cols(raw_m)
    dim_winners = [int(np.argmax(m_norm[:, j])) + 1 for j in range(5)]

    # Structured weighting comparison: visibility-heavy vs support-heavy
    alpha_vis = np.array([0.55, 0.15, 0.10, 0.15, 0.05])
    alpha_sup = np.array([0.10, 0.50, 0.30, 0.05, 0.05])
    g_vis = m_norm @ alpha_vis
    g_sup = m_norm @ alpha_sup

    # Sweep 1,000 Dirichlet(1,1,1,1,1) weightings to count how often each partner ranks #1
    alphas = rng.dirichlet(np.ones(5), size=1000)
    top_counts = np.zeros(4, dtype=int)
    rows = []
    for idx, a in enumerate(alphas):
        g = m_norm @ a
        winner = int(np.argmax(g))
        top_counts[winner] += 1
        rows.append({
            "sample": idx,
            "alpha_1": round(float(a[0]), 5),
            "alpha_2": round(float(a[1]), 5),
            "alpha_3": round(float(a[2]), 5),
            "alpha_4": round(float(a[3]), 5),
            "alpha_5": round(float(a[4]), 5),
            "G1_score": round(float(g[0]), 6),
            "G2_score": round(float(g[1]), 6),
            "G3_score": round(float(g[2]), 6),
            "G4_score": round(float(g[3]), 6),
            "top_partner": winner + 1,
        })

    with (DATA_DIR / "role_aggregation.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    return {
        "seed": SEED_ROLE_AGG,
        "dim_winners_1indexed": dim_winners,
        "rank1_visibility_scheme": int(np.argmax(g_vis)) + 1,
        "rank1_support_scheme": int(np.argmax(g_sup)) + 1,
        "g_vis": [round(float(x), 4) for x in g_vis],
        "g_sup": [round(float(x), 4) for x in g_sup],
        "dirichlet_top1_counts": [int(c) for c in top_counts],
    }


def simulate_markov_drift() -> dict:
    """Experiment 2: Periodic weekly Markov chain, joint 12-state chain, and EMA drift."""
    rng = np.random.default_rng(SEED_MARKOV)
    p_weekday, p_weekend, p_stress = markov_regime_kernels()

    # Exact weekly stroboscopic operator (periodic phase-locked)
    p_week = (
        np.linalg.matrix_power(0.85 * p_weekday + 0.15 * p_stress, 5)
        @ np.linalg.matrix_power(0.85 * p_weekend + 0.15 * p_stress, 2)
    )
    eigvals, eigvecs = np.linalg.eig(p_week.T)
    idx = int(np.argmin(np.abs(eigvals - 1.0)))
    pi_theory = np.real(eigvecs[:, idx])
    pi_theory = pi_theory / np.sum(pi_theory)

    # Exact 12-state joint stationary marginal over partners
    joint = build_joint_regime_chain(p_st=0.15)
    jeigs, jvecs = np.linalg.eig(joint.T)
    jidx = int(np.argmin(np.abs(jeigs - 1.0)))
    pi_joint = np.real(jvecs[:, jidx])
    pi_joint = pi_joint / np.sum(pi_joint)
    pi_joint_partner = np.sum(pi_joint.reshape(3, 4), axis=0)

    # 90-day half-day EMA trajectory
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
            mat, regime = p_stress, "stress"
        elif is_weekend:
            mat, regime = p_weekend, "weekend"
        else:
            mat, regime = p_weekday, "weekday"

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

    # 20,000-week Monte Carlo occupancy check
    counts = np.zeros(4, dtype=int)
    s = 0
    for _ in range(20000):
        for d in range(7):
            is_stress = rng.random() < 0.15
            mat = p_stress if is_stress else (p_weekend if d >= 5 else p_weekday)
            s = int(rng.choice(4, p=mat[s]))
        counts[s] += 1
    pi_emp = counts / np.sum(counts)

    with (DATA_DIR / "markov_drift.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    return {
        "seed": SEED_MARKOV,
        "n_steps": len(rows),
        "stationary_theory": [round(float(x), 4) for x in pi_theory],
        "stationary_joint_marginal": [round(float(x), 4) for x in pi_joint_partner],
        "stationary_empirical_weekly": [round(float(x), 4) for x in pi_emp],
        "final_entropy_bits": rows[-1]["entropy_bits"],
    }


def simulate_optionality_and_collapse() -> dict:
    """Experiment 5: Homogeneous Binomial, Poisson pool, heterogeneous, and time-budget models."""
    rng = np.random.default_rng(SEED_OPTIONALITY)
    n_trials = 4000
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
        row["collapse_hazard_30d"] = round(float(1.0 - np.exp(-0.08 * n * (1.0 + 0.12 * (n - 1)))), 6)
        rows_n.append(row)

    with (DATA_DIR / "optionality_vs_n.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows_n[0].keys()))
        writer.writeheader()
        writer.writerows(rows_n)

    # Attractiveness index A -> Poisson(lambda(A))
    rows_a = []
    a_grid = np.linspace(0.0, 10.0, 21)
    for a_val in a_grid:
        lam = 0.35 * float(np.exp(0.32 * a_val))
        pool = rng.poisson(lam, size=n_trials)
        row_a: dict[str, float] = {
            "attractiveness_A": round(float(a_val), 2),
            "mean_pool": round(float(np.mean(pool)), 4),
        }
        for p in p_values:
            kept = np.array([rng.binomial(k, p) if k > 0 else 0 for k in pool])
            tag = str(int(round(p * 100)))
            row_a[f"p_superposition_p{tag}"] = round(float(np.mean(kept >= 2)), 6)
        rows_a.append(row_a)

    with (DATA_DIR / "optionality_vs_A.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows_a[0].keys()))
        writer.writeheader()
        writer.writerows(rows_a)

    # Heterogeneous Poisson-binomial vs negatively correlated time-budget retention (mean p = 0.45)
    rows_het = []
    p_base = 0.45
    eta_budget = 0.20
    for n in range(1, 11):
        # Heterogeneous p_i ~ Beta(2.25, 2.75) (mean 0.45)
        probs_het = rng.beta(2.25, 2.75, size=(n_trials, n))
        kept_het = np.sum(rng.random((n_trials, n)) < probs_het, axis=1)

        # Sequential negatively correlated time-budget: p_eff(k) = p_base / (1 + eta_budget * k)
        kept_corr = np.zeros(n_trials, dtype=int)
        for _ in range(n):
            p_eff = p_base / (1.0 + eta_budget * kept_corr)
            kept_corr += (rng.random(n_trials) < p_eff).astype(int)

        exact_hom = 0.0 if n < 2 else float(1.0 - (1.0 - p_base) ** n - n * p_base * (1.0 - p_base) ** (n - 1))
        rows_het.append({
            "n_partners": n,
            "homog_exact": round(exact_hom, 6),
            "hetero_poisson_bin": round(float(np.mean(kept_het >= 2)), 6),
            "budget_neg_corr": round(float(np.mean(kept_corr >= 2)), 6),
            "budget_mean_kept": round(float(np.mean(kept_corr)), 4),
        })

    with (DATA_DIR / "optionality_heterogeneity.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows_het[0].keys()))
        writer.writeheader()
        writer.writerows(rows_het)

    return {
        "seed": SEED_OPTIONALITY,
        "n_trials": n_trials,
        "p_superposition_n5_p45_exact": rows_n[4]["exact_p45"],
        "p_superposition_n5_p45_mc": rows_n[4]["mc_p45"],
        "p_superposition_A2_p45": rows_a[4]["p_superposition_p45"],
        "p_superposition_A8_p45": rows_a[16]["p_superposition_p45"],
        "budget_n5_superposition": rows_het[4]["budget_neg_corr"],
        "hetero_n5_superposition": rows_het[4]["hetero_poisson_bin"],
    }


def _run_cascade_trial(
    rng: np.random.Generator,
    n: int,
    q: float,
    topology: str,
    tx_prob: float = 0.72,
    collapse_frac_threshold: float = 0.60,
) -> tuple[bool, float]:
    """Run one finite-network cascade trial from a single initially poked vertex."""
    adj = np.zeros((n, n), dtype=bool)
    if topology == "erdos_renyi":
        upper = rng.random((n, n)) < q
        upper = np.triu(upper, 1)
        adj = upper | upper.T
    elif topology == "clustered":
        half = n // 2
        for i in range(n):
            for j in range(i + 1, n):
                same_group = (i < half and j < half) or (i >= half and j >= half)
                p_edge = min(1.0, 1.8 * q) if same_group else 0.45 * q
                if rng.random() < p_edge:
                    adj[i, j] = adj[j, i] = True
    elif topology == "hub_mediated":
        for i in range(1, n):
            if rng.random() < min(1.0, 1.6 * q):
                adj[0, i] = adj[i, 0] = True
        for i in range(1, n):
            for j in range(i + 1, n):
                if rng.random() < 0.35 * q:
                    adj[i, j] = adj[j, i] = True

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
    return frac >= collapse_frac_threshold, frac


def simulate_cascade_percolation() -> dict:
    """Experiment 4: Finite-network cascade across topologies and p_tx sensitivity."""
    rng = np.random.default_rng(SEED_CASCADE)
    n_trials = 1500
    n_partners = 8
    q_grid = np.linspace(0.0, 1.0, 21)
    topologies = ["erdos_renyi", "clustered", "hub_mediated"]

    rows = []
    for q in q_grid:
        row: dict[str, float] = {
            "edge_density_q": round(float(q), 3),
            "R0_branching": round(float((n_partners - 1) * q * 0.72), 4),
        }
        for topo in topologies:
            cascades = 0
            frac_sum = 0.0
            for _ in range(n_trials):
                tot, frac = _run_cascade_trial(rng, n_partners, float(q), topo, tx_prob=0.72)
                cascades += int(tot)
                frac_sum += frac
            row[f"cascade_{topo}"] = round(cascades / n_trials, 6)
            row[f"mean_exposed_{topo}"] = round(frac_sum / n_trials, 6)
        rows.append(row)

    with (DATA_DIR / "cascade_percolation.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    # Sensitivity across transmission probability p_tx in {0.40, 0.72, 0.90}
    rows_ptx = []
    for q in q_grid:
        row_p: dict[str, float] = {"edge_density_q": round(float(q), 3)}
        for ptx in [0.40, 0.72, 0.90]:
            cascades = 0
            for _ in range(n_trials):
                tot, _ = _run_cascade_trial(rng, n_partners, float(q), "erdos_renyi", tx_prob=ptx)
                cascades += int(tot)
            tag = str(int(round(ptx * 100)))
            row_p[f"cascade_ptx{tag}"] = round(cascades / n_trials, 6)
        rows_ptx.append(row_p)

    with (DATA_DIR / "cascade_ptx_sensitivity.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows_ptx[0].keys()))
        writer.writeheader()
        writer.writerows(rows_ptx)

    r0_unity_q = 1.0 / ((n_partners - 1) * 0.72)
    return {
        "seed": SEED_CASCADE,
        "n_partners": n_partners,
        "n_trials": n_trials,
        "tx_prob": 0.72,
        "q_R0_unity_ref": round(r0_unity_q, 4),
        "cascade_er_q02": rows[4]["cascade_erdos_renyi"],
        "cascade_er_q06": rows[12]["cascade_erdos_renyi"],
    }


def simulate_uncertainty_sweep() -> dict:
    """Experiment 3: Unitary-rotated L = U^dagger D_L U Robertson and Schrodinger sweep."""
    rng = np.random.default_rng(SEED_UNCERTAINTY)
    n_samples_per_cell = 200
    rows = []
    robertson_violations = 0
    schrodinger_violations = 0
    min_rob_ratio = 1e9
    min_sch_ratio = 1e9

    for d in [2, 3, 4, 5]:
        op_r = np.diag(np.arange(1, d + 1, dtype=complex))
        d_l = np.diag(np.linspace(-1.0, 1.0, d).astype(complex))
        for gamma in [0.0, 0.25, 0.75, 1.50]:
            for _ in range(n_samples_per_cell):
                a = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
                h_gen = 0.5 * (a + a.conj().T)
                norm_h = max(1e-8, float(np.linalg.norm(h_gen, ord=2)))
                h_gen = h_gen / norm_h
                u_mat = build_unitary_context(d, gamma, h_gen)
                op_l = u_mat.conj().T @ d_l @ u_mat

                psi = rng.normal(size=d) + 1j * rng.normal(size=d)
                psi = psi / np.linalg.norm(psi)

                m = uncertainty_metrics(op_r, op_l, psi)
                if m["product"] + 1e-11 < m["robertson_bound"]:
                    robertson_violations += 1
                if m["product"] + 1e-11 < m["schrodinger_bound"]:
                    schrodinger_violations += 1
                if m["robertson_bound"] > 1e-9:
                    min_rob_ratio = min(min_rob_ratio, m["product"] / m["robertson_bound"])
                if m["schrodinger_bound"] > 1e-9:
                    min_sch_ratio = min(min_sch_ratio, m["product"] / m["schrodinger_bound"])

                rows.append({
                    "dim": d,
                    "gamma": gamma,
                    "delta_R": round(m["delta_R"], 6),
                    "delta_L": round(m["delta_L"], 6),
                    "product": round(m["product"], 6),
                    "robertson_bound": round(m["robertson_bound"], 6),
                    "cov_term": round(m["cov_term"], 6),
                    "schrodinger_bound": round(m["schrodinger_bound"], 6),
                })

    with (DATA_DIR / "uncertainty_sweep.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    nonzero_gamma = [r for r in rows if r["gamma"] > 0.0]
    return {
        "seed": SEED_UNCERTAINTY,
        "total_samples": len(rows),
        "robertson_violations": robertson_violations,
        "schrodinger_violations": schrodinger_violations,
        "min_ratio_robertson": round(min_rob_ratio, 4),
        "min_ratio_schrodinger": round(min_sch_ratio, 4),
        "median_product_nonzero_gamma": round(float(np.median([r["product"] for r in nonzero_gamma])), 4),
        "median_robertson_nonzero_gamma": round(float(np.median([r["robertson_bound"] for r in nonzero_gamma])), 4),
        "median_schrodinger_nonzero_gamma": round(float(np.median([r["schrodinger_bound"] for r in nonzero_gamma])), 4),
    }


def main() -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    summary = {
        "role_aggregation": simulate_role_aggregation(),
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
