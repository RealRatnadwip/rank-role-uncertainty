"""Automated invariant and correctness tests for RST mathematical models and simulations."""

from __future__ import annotations

import csv
import math
import sys
import unittest
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import run_simulations as sim  # noqa: E402


class TestMathematicalInvariants(unittest.TestCase):
    def test_role_matrix_normalization_and_zero_column(self) -> None:
        m = np.array([
            [2.0, 0.0, 3.0],
            [6.0, 0.0, 1.0],
        ])
        m_norm = sim.normalize_role_matrix_cols(m)
        self.assertTrue(np.all(m_norm >= 0.0))
        self.assertAlmostEqual(float(np.sum(m_norm[:, 0])), 1.0, places=12)
        self.assertAlmostEqual(float(np.sum(m_norm[:, 2])), 1.0, places=12)
        self.assertTrue(np.allclose(m_norm[:, 1], 0.0))

    def test_ranking_and_unique_vs_shared_max(self) -> None:
        w99 = np.array([0.99, 0.01])
        self.assertTrue(np.all(w99 < 1.0))
        ranks = sim.ordinal_ranks_desc(w99)
        self.assertListEqual(ranks.tolist(), [1, 2])

        w_tied = np.array([0.45, 0.45, 0.10])
        ranks_tied = sim.ordinal_ranks_desc(w_tied)
        self.assertListEqual(ranks_tied.tolist(), [1, 1, 3])

    def test_projection_and_removal_renormalization(self) -> None:
        psi = np.array([0.6 + 0.0j, 0.8 * 1j, 0.0 + 0.0j])
        proj = sim.project_and_normalize(psi, np.array([True, False, False]))
        self.assertAlmostEqual(float(np.linalg.norm(proj)), 1.0, places=12)
        self.assertAlmostEqual(abs(proj[0]), 1.0, places=12)

        with self.assertRaises(ValueError):
            sim.project_and_normalize(psi, np.array([False, False, True]))

        w = np.array([0.45, 0.35, 0.20])
        w_after = sim.remove_partner_weights(w, 1)
        self.assertAlmostEqual(w_after[1], 0.0, places=12)
        self.assertAlmostEqual(float(np.sum(w_after)), 1.0, places=12)
        self.assertAlmostEqual(w_after[0], 0.45 / 0.65, places=12)

        with self.assertRaises(ValueError):
            sim.remove_partner_weights(np.array([1.0, 0.0]), 0)

    def test_markov_kernels_stochastic_and_stationary(self) -> None:
        p_wd, p_we, p_st = sim.markov_regime_kernels()
        for mat in (p_wd, p_we, p_st):
            self.assertTrue(np.all(mat >= 0.0))
            self.assertTrue(np.allclose(mat.sum(axis=1), 1.0, atol=1e-12))

        joint = sim.build_joint_regime_chain(p_st=0.15)
        self.assertEqual(joint.shape, (12, 12))
        self.assertTrue(np.all(joint >= 0.0))
        self.assertTrue(np.allclose(joint.sum(axis=1), 1.0, atol=1e-12))

    def test_unitary_commutativity_at_zero_and_schrodinger_2d_3d(self) -> None:
        rng = np.random.default_rng(12345)
        op_r = np.diag([1.0, 2.0, 3.0]).astype(complex)
        d_l = np.diag([-1.0, 0.0, 1.0]).astype(complex)
        a = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
        h = 0.5 * (a + a.conj().T)

        u0 = sim.build_unitary_context(3, 0.0, h)
        self.assertTrue(np.allclose(u0.conj().T @ u0, np.eye(3), atol=1e-12))
        l0 = u0.conj().T @ d_l @ u0
        self.assertTrue(np.allclose(op_r @ l0 - l0 @ op_r, 0.0, atol=1e-12))

        u1 = sim.build_unitary_context(3, 0.85, h)
        self.assertTrue(np.allclose(u1.conj().T @ u1, np.eye(3), atol=1e-12))
        l1 = u1.conj().T @ d_l @ u1
        self.assertTrue(np.allclose(l1, l1.conj().T, atol=1e-12))

        psi = np.array([0.36, 0.48, 0.80], dtype=complex)
        m = sim.uncertainty_metrics(op_r, l1, psi)
        self.assertGreaterEqual(m["product"] + 1e-12, m["schrodinger_bound"])
        self.assertGreaterEqual(m["schrodinger_bound"] + 1e-12, m["robertson_bound"])


class TestSimulationOutputs(unittest.TestCase):
    def test_generated_csv_invariants(self) -> None:
        data_dir = ROOT / "paper" / "data"
        if not (data_dir / "summary.json").exists():
            self.skipTest("Run make figures before testing generated CSV artifacts.")

        # 1. Markov drift CSV weights sum to 1 and remain in [0, 1]
        with (data_dir / "markov_drift.csv").open() as f:
            for row in csv.DictReader(f):
                ws = [float(row[f"w{i}"]) for i in range(1, 5)]
                self.assertTrue(all(0.0 <= w <= 1.0 for w in ws))
                self.assertAlmostEqual(sum(ws), 1.0, places=4)

        # 2. Uncertainty sweep obeys Schrodinger >= Robertson and product >= Schrodinger
        with (data_dir / "uncertainty_sweep.csv").open() as f:
            rows = list(csv.DictReader(f))
        self.assertGreaterEqual(len(rows), 2400)
        for row in rows:
            prod = float(row["product"])
            rob = float(row["robertson_bound"])
            sch = float(row["schrodinger_bound"])
            gamma = float(row["gamma"])
            if gamma == 0.0:
                self.assertAlmostEqual(rob, 0.0, places=6)
            self.assertGreaterEqual(sch + 1e-6, rob)
            self.assertGreaterEqual(prod + 1e-6, sch)

        # 3. Cascade probabilities bounded in [0, 1]
        with (data_dir / "cascade_percolation.csv").open() as f:
            for row in csv.DictReader(f):
                for key in ("cascade_erdos_renyi", "cascade_clustered", "cascade_hub_mediated",
                            "mean_exposed_erdos_renyi", "mean_exposed_clustered", "mean_exposed_hub_mediated"):
                    val = float(row[key])
                    self.assertTrue(0.0 <= val <= 1.0)

        # 4. Binomial Monte Carlo tracks exact expectation within 5 sigma
        with (data_dir / "optionality_vs_n.csv").open() as f:
            for row in csv.DictReader(f):
                for tag in ("25", "45", "65"):
                    ex = float(row[f"exact_p{tag}"])
                    mc = float(row[f"mc_p{tag}"])
                    se = math.sqrt(max(ex * (1.0 - ex), 1e-4) / 4000.0)
                    self.assertLessEqual(abs(mc - ex), 5.0 * se)


if __name__ == "__main__":
    unittest.main()
