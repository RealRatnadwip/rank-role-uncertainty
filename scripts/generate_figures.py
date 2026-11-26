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
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.8, 3.0))

    q = d["edge_density_q"]
    q_crit = 1.0 / (7.0 * 0.72)

    ax1.plot(q, d["cascade_erdos_renyi"], color=PALETTE["navy"], lw=1.5, marker="o", ms=3, label="Homogeneous graph")
    ax1.plot(q, d["cascade_clustered"], color=PALETTE["plum"], lw=1.4, marker="s", ms=3, label="Clustered circles")
    ax1.plot(q, d["cascade_hub_mediated"], color=PALETTE["amber"], lw=1.4, marker="^", ms=3, label="Hub-mediated")
    ax1.axvline(q_crit, color=PALETTE["muted"], lw=0.9, ls="--", label=rf"Analytic $q_c \approx {q_crit:.2f}$")
    ax1.set_xlabel(r"Shared-friend edge density $q$ (dimensionless)")
    ax1.set_ylabel(r"$\mathbb{P}(\mathrm{total\ cascade})$ (dimensionless)")
    ax1.set_title(r"(a) Cascade Transition ($n=8$, $p_{\mathrm{tx}}=0.72$)")
    ax1.set_ylim(-0.03, 1.05)
    ax1.grid(True, alpha=0.8)
    ax1.legend(loc="lower right", fontsize=7.5)

    ax2.plot(q, d["mean_exposed_erdos_renyi"], color=PALETTE["navy"], lw=1.5, label="Homogeneous graph")
    ax2.plot(q, d["mean_exposed_clustered"], color=PALETTE["plum"], lw=1.4, label="Clustered circles")
    ax2.plot(q, d["mean_exposed_hub_mediated"], color=PALETTE["amber"], lw=1.4, label="Hub-mediated")
    ax2.axhline(0.60, color=PALETTE["muted"], lw=0.9, ls=":", label="Cascade threshold (0.60)")
    ax2.set_xlabel(r"Shared-friend edge density $q$ (dimensionless)")
    ax2.set_ylabel("Mean exposed fraction (dimensionless)")
    ax2.set_title("(b) Mean Fraction of Informed Partners")
    ax2.set_ylim(0.05, 1.05)
    ax2.grid(True, alpha=0.8)
    ax2.legend(loc="lower right", fontsize=7.5)

    fig.tight_layout()
    save_both(fig, "fig_cascade_percolation")


def plot_uncertainty_sweep() -> None:
    d = read_csv(DATA_DIR / "uncertainty_sweep.csv")
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.8, 3.1))

    kappa = d["kappa_bound"]
    prod = d["product"]
    gamma = d["gamma"]

    colors = {0.25: PALETTE["teal"], 0.75: PALETTE["navy"], 1.5: PALETTE["plum"]}
    for g_val in [0.25, 0.75, 1.50]:
        mask = np.isclose(gamma, g_val)
        ax1.scatter(
            kappa[mask],
            prod[mask],
            s=8,
            alpha=0.45,
            color=colors[g_val],
            edgecolors="none",
            label=rf"$\gamma = {g_val:.2f}$",
        )
    max_k = float(np.max(kappa)) * 1.05
    xs = np.linspace(0.0, max_k, 100)
    ax1.plot(xs, xs, color=PALETTE["ink"], lw=1.1, ls="--", label=r"Tight bound $\Delta R \cdot \Delta L = \kappa$")
    ax1.set_xlabel(r"Commutator lower bound $\kappa = \frac{1}{2}|\mathrm{Im}\langle\Psi|[\hat{R},\hat{L}]|\Psi\rangle|$")
    ax1.set_ylabel(r"Observed product $\Delta R \cdot \Delta L$")
    ax1.set_title(r"(a) Inequality Compliance ($N=2400$ states)")
    ax1.set_xlim(0.0, max_k)
    ax1.set_ylim(0.0, float(np.percentile(prod, 99.5)) * 1.1)
    ax1.grid(True, alpha=0.8)
    ax1.legend(loc="upper left", fontsize=7.5)

    # Box/violin-like summary by dimension d
    dims = [2, 3, 4, 5]
    data_by_dim = [prod[np.isclose(d["dim"], dim_val)] for dim_val in dims]
    bp = ax2.boxplot(
        data_by_dim,
        positions=dims,
        widths=0.45,
        patch_artist=True,
        showfliers=False,
        medianprops={"color": PALETTE["ink"], "linewidth": 1.3},
        whiskerprops={"color": PALETTE["slate"], "linewidth": 0.9},
        capprops={"color": PALETTE["slate"], "linewidth": 0.9},
    )
    for box in bp["boxes"]:
        box.set_facecolor("#E2E8F0")
        box.set_edgecolor(PALETTE["navy"])
        box.set_linewidth(0.9)
    ax2.set_xlabel("State space dimension $d$ (partners)")
    ax2.set_ylabel(r"Uncertainty product $\Delta R \cdot \Delta L$")
    ax2.set_title("(b) Dispersion Product Across Dimension $d$")
    ax2.grid(True, axis="y", alpha=0.8)

    fig.tight_layout()
    save_both(fig, "fig_uncertainty_bound")


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    configure_style()
    plot_markov_drift()
    plot_optionality_and_collapse()
    plot_cascade_percolation()
    plot_uncertainty_sweep()


if __name__ == "__main__":
    main()
