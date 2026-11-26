"""Generate publication-quality PDF and SVG figures from simulation CSV outputs."""

from __future__ import annotations

import csv
from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "paper" / "data"
FIG_DIR = ROOT / "paper" / "figures"

# Clean editorial typography and palette aligned with the monograph
PALETTE = {
    "ink": "#141416",
    "slate": "#334155",
    "navy": "#2B3A67",
    "plum": "#5B3E6B",
    "teal": "#2A6F78",
    "amber": "#B45309",
    "muted": "#64748B",
    "grid": "#E2E8F0",
}


def configure_style() -> None:
    mpl.rcParams.update({
        "font.family": "serif",
        "font.serif": ["DejaVu Serif", "Computer Modern Roman", "Times"],
        "mathtext.fontset": "cm",
        "font.size": 9.5,
        "axes.titlesize": 10.5,
        "axes.titleweight": "bold",
        "axes.labelsize": 9.5,
        "axes.edgecolor": PALETTE["slate"],
        "axes.linewidth": 0.7,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "legend.fontsize": 8.2,
        "legend.frameon": True,
        "legend.facecolor": "#FFFFFF",
        "legend.edgecolor": PALETTE["grid"],
        "grid.color": PALETTE["grid"],
        "grid.linewidth": 0.6,
        "savefig.dpi": 300,
        "savefig.bbox": "tight",
        "svg.fonttype": "path",
    })


def read_csv(path: Path) -> dict[str, np.ndarray]:
    with path.open("r", newline="") as f:
        reader = csv.DictReader(f)
        cols: dict[str, list[str]] = {k: [] for k in (reader.fieldnames or [])}
        for row in reader:
            for k, v in row.items():
                cols[k].append(v)
    out: dict[str, np.ndarray] = {}
    for k, vals in cols.items():
        try:
            out[k] = np.array(vals, dtype=float)
        except ValueError:
            out[k] = np.array(vals, dtype=str)
    return out


def save_both(fig: plt.Figure, stem: str) -> None:
    fig.savefig(FIG_DIR / f"{stem}.pdf")
    fig.savefig(FIG_DIR / f"{stem}.svg")
    plt.close(fig)


def plot_markov_drift() -> None:
    d = read_csv(DATA_DIR / "markov_drift.csv")
    fig, (ax1, ax2) = plt.subplots(
        2, 1, figsize=(6.5, 4.4), sharex=True, gridspec_kw={"height_ratios": [2.2, 1.0]}
    )

    days = d["day"]
    ax1.plot(days, d["w1"], label=r"$G_1$ (primary baseline)", color=PALETTE["navy"], lw=1.4)
    ax1.plot(days, d["w2"], label=r"$G_2$ (emotional support)", color=PALETTE["plum"], lw=1.4)
    ax1.plot(days, d["w3"], label=r"$G_3$ (financial support)", color=PALETTE["teal"], lw=1.2, ls="--")
    ax1.plot(days, d["w4"], label=r"$G_4$ (weekend entertainment)", color=PALETTE["amber"], lw=1.2, ls="-.")
    ax1.set_ylabel(r"Attention weight $w_i(t)$ (dimensionless)")
    ax1.set_ylim(0.0, 0.72)
    ax1.grid(True, alpha=0.8)
    ax1.legend(loc="upper right", ncol=2)
    ax1.set_title("Synthetic 90-Day Attention-Weight Drift Under Periodic Regime Switching")

    ax2.plot(days, d["entropy_bits"], color=PALETTE["ink"], lw=1.2)
    ax2.axhline(2.0, color=PALETTE["muted"], lw=0.8, ls=":", label=r"Uniform cap ($\log_2 4 = 2$ bits)")
    ax2.set_ylabel("Entropy (bits)")
    ax2.set_xlabel("Time $t$ (days)")
    ax2.set_ylim(1.1, 2.15)
    ax2.grid(True, alpha=0.8)
    ax2.legend(loc="lower right")

    fig.tight_layout()
    save_both(fig, "fig_markov_drift")


def plot_optionality_and_collapse() -> None:
    dn = read_csv(DATA_DIR / "optionality_vs_n.csv")
    da = read_csv(DATA_DIR / "optionality_vs_A.csv")

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.8, 3.1))

    n = dn["n_partners"]
    ax1.plot(n, dn["exact_p25"], color=PALETTE["teal"], lw=1.3, label=r"$p=0.25$ (analytic)")
    ax1.scatter(n, dn["mc_p25"], color=PALETTE["teal"], s=16, zorder=4)
    ax1.plot(n, dn["exact_p45"], color=PALETTE["navy"], lw=1.5, label=r"$p=0.45$ (analytic)")
    ax1.scatter(n, dn["mc_p45"], color=PALETTE["navy"], s=16, zorder=4)
    ax1.plot(n, dn["exact_p65"], color=PALETTE["plum"], lw=1.3, label=r"$p=0.65$ (analytic)")
    ax1.scatter(n, dn["mc_p65"], color=PALETTE["plum"], s=16, zorder=4)
    ax1.plot(n, dn["collapse_hazard_30d"], color=PALETTE["amber"], lw=1.2, ls="--", label="30-day collapse hazard")
    ax1.set_xlabel("Viable partner count $n$ (partners)")
    ax1.set_ylabel("Probability (dimensionless)")
    ax1.set_title("(a) Superposition & Collapse Hazard vs. $n$")
    ax1.set_xticks(range(1, 11))
    ax1.set_ylim(-0.03, 1.05)
    ax1.grid(True, alpha=0.8)
    ax1.legend(loc="lower right", fontsize=7.5)

    a = da["attractiveness_A"]
    ax2.plot(a, da["p_superposition_p25"], color=PALETTE["teal"], lw=1.3, marker="o", ms=3, label=r"$p=0.25$")
    ax2.plot(a, da["p_superposition_p45"], color=PALETTE["navy"], lw=1.5, marker="s", ms=3, label=r"$p=0.45$")
    ax2.plot(a, da["p_superposition_p65"], color=PALETTE["plum"], lw=1.3, marker="^", ms=3, label=r"$p=0.65$")
    ax2.set_xlabel(r"Perceived attractiveness index $A$ (0 to 10 scale)")
    ax2.set_ylabel(r"$\mathbb{P}(\mathrm{superposition})$ (dimensionless)")
    ax2.set_title(r"(b) Superposition vs. Optionality Index $A$")
    ax2.set_ylim(-0.03, 1.05)
    ax2.grid(True, alpha=0.8)
    ax2.legend(loc="lower right", fontsize=7.8)

    fig.tight_layout()
    save_both(fig, "fig_collapse_vs_n_A")


def plot_cascade_percolation() -> None:
    d = read_csv(DATA_DIR / "cascade_percolation.csv")
    dp = read_csv(DATA_DIR / "cascade_ptx_sensitivity.csv")
    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(9.6, 3.0))

    q = d["edge_density_q"]
    q_crit = 1.0 / (7.0 * 0.72)

    ax1.plot(q, d["cascade_erdos_renyi"], color=PALETTE["navy"], lw=1.5, marker="o", ms=3, label="Homogeneous graph")
    ax1.plot(q, d["cascade_clustered"], color=PALETTE["plum"], lw=1.4, marker="s", ms=3, label="Clustered circles")
    ax1.plot(q, d["cascade_hub_mediated"], color=PALETTE["amber"], lw=1.4, marker="^", ms=3, label="Hub-mediated")
    ax1.axvline(q_crit, color=PALETTE["muted"], lw=0.9, ls="--", label=rf"Branching $R_0=1$ ($q={q_crit:.2f}$)")
    ax1.set_xlabel(r"Edge density $q$")
    ax1.set_ylabel(r"$\mathbb{P}(\mathrm{total\ cascade})$")
    ax1.set_title(r"(a) Topology ($n=8$, $p_{\mathrm{tx}}=0.72$)")
    ax1.set_ylim(-0.03, 1.05)
    ax1.grid(True, alpha=0.8)
    ax1.legend(loc="lower right", fontsize=7.0)

    ax2.plot(q, d["mean_exposed_erdos_renyi"], color=PALETTE["navy"], lw=1.5, label="Homogeneous graph")
    ax2.plot(q, d["mean_exposed_clustered"], color=PALETTE["plum"], lw=1.4, label="Clustered circles")
    ax2.plot(q, d["mean_exposed_hub_mediated"], color=PALETTE["amber"], lw=1.4, label="Hub-mediated")
    ax2.axhline(0.60, color=PALETTE["muted"], lw=0.9, ls=":", label="Cascade threshold (0.60)")
    ax2.set_xlabel(r"Edge density $q$")
    ax2.set_ylabel("Mean exposed fraction")
    ax2.set_title("(b) Mean Informed Fraction")
    ax2.set_ylim(0.05, 1.05)
    ax2.grid(True, alpha=0.8)
    ax2.legend(loc="lower right", fontsize=7.0)

    qp = dp["edge_density_q"]
    ax3.plot(qp, dp["cascade_ptx40"], color=PALETTE["teal"], lw=1.4, marker="o", ms=3, label=r"$p_{\mathrm{tx}}=0.40$")
    ax3.plot(qp, dp["cascade_ptx72"], color=PALETTE["navy"], lw=1.5, marker="s", ms=3, label=r"$p_{\mathrm{tx}}=0.72$")
    ax3.plot(qp, dp["cascade_ptx90"], color=PALETTE["plum"], lw=1.4, marker="^", ms=3, label=r"$p_{\mathrm{tx}}=0.90$")
    ax3.set_xlabel(r"Edge density $q$")
    ax3.set_ylabel(r"$\mathbb{P}(\mathrm{total\ cascade})$")
    ax3.set_title(r"(c) Transmission Sensitivity ($p_{\mathrm{tx}}$)")
    ax3.set_ylim(-0.03, 1.05)
    ax3.grid(True, alpha=0.8)
    ax3.legend(loc="lower right", fontsize=7.2)

    fig.tight_layout()
    save_both(fig, "fig_cascade_percolation")


def plot_uncertainty_sweep() -> None:
    d = read_csv(DATA_DIR / "uncertainty_sweep.csv")
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.8, 3.1))

    r_bound = d["robertson_bound"]
    s_bound = d["schrodinger_bound"]
    prod = d["product"]
    gamma = d["gamma"]

    colors = {
        0.0: PALETTE["muted"],
        0.25: PALETTE["teal"],
        0.75: PALETTE["navy"],
        1.5: PALETTE["plum"],
    }
    for g_val in [0.0, 0.25, 0.75, 1.50]:
        mask = np.isclose(gamma, g_val)
        ax1.scatter(
            s_bound[mask],
            prod[mask],
            s=8,
            alpha=0.45,
            color=colors[g_val],
            edgecolors="none",
            label=rf"$\gamma = {g_val:.2f}$",
        )
    max_b = float(np.max(s_bound)) * 1.05
    xs = np.linspace(0.0, max_b, 100)
    ax1.plot(xs, xs, color=PALETTE["ink"], lw=1.1, ls="--", label=r"Bound $\Delta R \Delta L = B_S$")
    ax1.set_xlabel(r"Schrodinger bound $B_S = \sqrt{|\mathrm{Cov}|^2 + \frac{1}{4}|\langle[\hat{R},\hat{L}]\rangle|^2}$")
    ax1.set_ylabel(r"Observed product $\Delta R \cdot \Delta L$")
    ax1.set_title(r"(a) Inequality Compliance ($N=3200$ states)")
    ax1.set_xlim(0.0, max_b)
    ax1.set_ylim(0.0, float(np.percentile(prod, 99.5)) * 1.1)
    ax1.grid(True, alpha=0.8)
    ax1.legend(loc="upper left", fontsize=7.0)

    # Compare observed product, Schrodinger bound, and Robertson bound by dimension d
    dims = np.array([2, 3, 4, 5], dtype=float)
    med_prod = [float(np.median(prod[np.isclose(d["dim"], dv)])) for dv in dims]
    med_sch = [float(np.median(s_bound[np.isclose(d["dim"], dv)])) for dv in dims]
    med_rob = [float(np.median(r_bound[np.isclose(d["dim"], dv)])) for dv in dims]

    w = 0.24
    ax2.bar(dims - w, med_rob, width=w, color=PALETTE["teal"], label="Robertson bound")
    ax2.bar(dims, med_sch, width=w, color=PALETTE["navy"], label="Schrodinger bound")
    ax2.bar(dims + w, med_prod, width=w, color=PALETTE["plum"], label=r"Observed $\Delta R \cdot \Delta L$")
    ax2.set_xticks(dims)
    ax2.set_xlabel("State space dimension $d$ (partners)")
    ax2.set_ylabel("Median magnitude")
    ax2.set_title("(b) Bound Tightness by Dimension $d$")
    ax2.grid(True, axis="y", alpha=0.8)
    ax2.legend(loc="upper right", fontsize=7.0)

    fig.tight_layout()
    save_both(fig, "fig_uncertainty_bound")


def plot_role_aggregation() -> None:
    d = read_csv(DATA_DIR / "role_aggregation.csv")
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.8, 3.0))

    # Exact benchmark scores from Worked Example / M_4x5 aggregation schemes
    partners = np.array([1, 2, 3, 4], dtype=float)
    g_vis = [0.4167, 0.2225, 0.1716, 0.1893]
    g_sup = [0.2169, 0.3508, 0.2865, 0.1458]
    w = 0.34
    ax1.bar(partners - w / 2, g_vis, width=w, color=PALETTE["navy"], label=r"Visibility weights $\alpha_{\mathrm{vis}}$")
    ax1.bar(partners + w / 2, g_sup, width=w, color=PALETTE["plum"], label=r"Support weights $\alpha_{\mathrm{sup}}$")
    ax1.set_xticks(partners)
    ax1.set_xticklabels([r"$G_1$", r"$G_2$", r"$G_3$", r"$G_4$"])
    ax1.set_xlabel("Partner")
    ax1.set_ylabel(r"Composite score $G_i(\alpha)$")
    ax1.set_title("(a) Rank Reversal Under Scheme Change")
    ax1.set_ylim(0.0, 0.50)
    ax1.grid(True, axis="y", alpha=0.8)
    ax1.legend(loc="upper right", fontsize=7.2)

    top_p = d["top_partner"]
    counts = [int(np.sum(np.isclose(top_p, k))) for k in [1, 2, 3, 4]]
    shares = [c / len(top_p) for c in counts]
    ax2.bar(partners, shares, width=0.52, color=[PALETTE["navy"], PALETTE["plum"], PALETTE["teal"], PALETTE["amber"]])
    for x, s in zip(partners, shares):
        ax2.text(x, s + 0.012, f"{100*s:.1f}%", ha="center", va="bottom", fontsize=7.8)
    ax2.set_xticks(partners)
    ax2.set_xticklabels([r"$G_1$", r"$G_2$", r"$G_3$", r"$G_4$"])
    ax2.set_xlabel("Partner")
    ax2.set_ylabel("Top-1 rank frequency ($N=1000$)")
    ax2.set_title(r"(b) Simplex Top-Rank Shares ($\alpha \sim \mathrm{Dir}(1,\ldots,1)$)")
    ax2.set_ylim(0.0, 0.42)
    ax2.grid(True, axis="y", alpha=0.8)

    fig.tight_layout()
    save_both(fig, "fig_role_aggregation")


def plot_optionality_extensions() -> None:
    d = read_csv(DATA_DIR / "optionality_heterogeneity.csv")
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.8, 3.0))

    n = d["n_partners"]
    ax1.plot(n, d["homog_exact"], color=PALETTE["navy"], lw=1.5, marker="o", ms=3, label="Homogeneous binomial ($p=0.45$)")
    ax1.plot(n, d["hetero_poisson_bin"], color=PALETTE["teal"], lw=1.4, ls="--", marker="s", ms=3, label="Heterogeneous Poisson binomial")
    ax1.plot(n, d["budget_neg_corr"], color=PALETTE["amber"], lw=1.5, ls="-.", marker="^", ms=3, label="Capacity-constrained ($B_{\\max}=3$)")
    ax1.set_xlabel("Viable pool size $n$")
    ax1.set_ylabel(r"$\mathbb{P}(K \geq 2)$")
    ax1.set_title("(a) Superposition Beyond i.i.d. Binomial")
    ax1.set_xticks(range(1, 11))
    ax1.set_ylim(-0.03, 1.05)
    ax1.grid(True, alpha=0.8)
    ax1.legend(loc="lower right", fontsize=7.0)

    ax2.plot(n, n * 0.45, color=PALETTE["navy"], lw=1.3, ls="--", label="Unconstrained mean $np$")
    ax2.plot(n, d["budget_mean_kept"], color=PALETTE["amber"], lw=1.5, marker="^", ms=3, label="Budget-capped mean $\\mathbb{E}[K]$")
    ax2.axhline(3.0, color=PALETTE["muted"], lw=0.9, ls=":", label="Hard time cap ($B_{\\max}=3$)")
    ax2.set_xlabel("Viable pool size $n$")
    ax2.set_ylabel("Expected active partners")
    ax2.set_title("(b) Sublinear Growth Under Attention Cap")
    ax2.set_xticks(range(1, 11))
    ax2.set_ylim(0.0, 4.8)
    ax2.grid(True, alpha=0.8)
    ax2.legend(loc="upper left", fontsize=7.2)

    fig.tight_layout()
    save_both(fig, "fig_optionality_extensions")


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    configure_style()
    plot_markov_drift()
    plot_optionality_and_collapse()
    plot_cascade_percolation()
    plot_uncertainty_sweep()
    plot_role_aggregation()
    plot_optionality_extensions()


if __name__ == "__main__":
    main()
