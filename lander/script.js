/* Relational Superposition Theory // Monochrome Plate Interactions */

(function () {
  "use strict";

  const BASE_WEIGHTS = [0.38, 0.29, 0.18, 0.15];
  const ROLES = ["r1", "r2", "r3", "r4"];
  let currentWeights = [...BASE_WEIGHTS];
  let collapsedIndex = null;
  let gammaZero = false;

  const badgeEl = document.getElementById("stateBadge");
  const entropyEl = document.getElementById("entropyReadout");
  const gammaEl = document.getElementById("gammaReadout");
  const roleAxisEl = document.getElementById("roleAxisGroup");
  const pokeBtn = document.getElementById("pokeBtn");
  const gammaBtn = document.getElementById("gammaBtn");
  const resetBtn = document.getElementById("resetBtn");

  function shannonEntropy(weights) {
    return weights.reduce((acc, w) => (w <= 0 ? acc : acc - w * Math.log2(w)), 0);
  }

  function renderPlate() {
    for (let i = 0; i < 4; i++) {
      const idx = i + 1;
      const w = currentWeights[i];
      const arc = document.getElementById(`arc${idx}`);
      const label = document.getElementById(`wlabel${idx}`);
      const node = document.getElementById(`node${idx}`);
      const bar = document.getElementById(`bar${idx}`);
      const pct = document.getElementById(`pct${idx}`);

      if (label) {
        label.textContent = `G${idx} // ${ROLES[i]} // ${w.toFixed(2)}`;
        label.setAttribute("fill", collapsedIndex === i ? "#FFFFFF" : (w > 0 ? "#B8B8BE" : "#44444A"));
      }
      if (arc) {
        arc.setAttribute("stroke-width", w > 0 ? (0.9 + 1.8 * w).toFixed(2) : "0.6");
        arc.setAttribute("stroke", collapsedIndex === i ? "#FFFFFF" : (w > 0 ? "#B8B8BE" : "#28282C"));
      }
      if (node) {
        node.setAttribute("fill", w > 0 ? "#F2F2F2" : "#323236");
      }
      if (bar) {
        bar.style.width = `${Math.round(w * 100)}%`;
      }
      if (pct) {
        pct.textContent = w.toFixed(2);
      }
    }

    if (roleAxisEl) {
      roleAxisEl.setAttribute("transform", gammaZero ? "rotate(0 180 110)" : "rotate(-28 180 110)");
    }
    if (entropyEl) {
      entropyEl.textContent = `H(w) = ${shannonEntropy(currentWeights).toFixed(3)} bits`;
    }
    if (gammaEl) {
      if (collapsedIndex !== null) {
        gammaEl.textContent = "collapsed eigenstate";
      } else {
        gammaEl.textContent = gammaZero ? "gamma = 0.00 (k_R = 0)" : "gamma = 0.75 (k_R > 0)";
      }
    }
    if (badgeEl) {
      if (collapsedIndex !== null) {
        badgeEl.textContent = `COLLAPSED -> G${collapsedIndex + 1}`;
        badgeEl.classList.add("is-collapsed");
      } else {
        badgeEl.textContent = "SUPERPOSED";
        badgeEl.classList.remove("is-collapsed");
      }
    }
    if (gammaBtn) {
      gammaBtn.textContent = gammaZero ? "Restore gamma = 0.75" : "Toggle gamma = 0";
    }
  }

  function sampleOutcome(weights) {
    const u = Math.random();
    let acc = 0;
    for (let i = 0; i < weights.length; i++) {
      acc += weights[i];
      if (u <= acc) return i;
    }
    return 0;
  }

  if (pokeBtn) {
    pokeBtn.addEventListener("click", () => {
      const winner = sampleOutcome(currentWeights);
      collapsedIndex = winner;
      currentWeights = currentWeights.map((_, idx) => (idx === winner ? 1.0 : 0.0));
      renderPlate();
    });
  }

  if (gammaBtn) {
    gammaBtn.addEventListener("click", () => {
      gammaZero = !gammaZero;
      renderPlate();
    });
  }

  if (resetBtn) {
    resetBtn.addEventListener("click", () => {
      currentWeights = [...BASE_WEIGHTS];
      collapsedIndex = null;
      gammaZero = false;
      renderPlate();
    });
  }

  /* Footer repository last-updated status via GitHub API with offline fallback */
  const statusEl = document.getElementById("updateStatus");
  if (statusEl && typeof fetch === "function") {
    const fallbackDate = statusEl.getAttribute("data-fallback-date") || "2026-11-26";
    const apiUrl = "https://api.github.com/repos/RealRatnadwip/rank-role-uncertainty/commits?per_page=1";
    fetch(apiUrl, { headers: { Accept: "application/vnd.github+json" } })
      .then((res) => (res.ok ? res.json() : null))
      .then((data) => {
        if (Array.isArray(data) && data.length > 0) {
          const item = data[0];
          const sha = (item.sha || "").slice(0, 7);
          const rawDate = item.commit && item.commit.committer ? item.commit.committer.date : "";
          const isoDate = rawDate ? rawDate.slice(0, 10) : fallbackDate;
          if (sha) {
            statusEl.textContent = `Last updated: ${isoDate} (${sha}, v1.1)`;
            return;
          }
        }
        statusEl.textContent = `Last updated: ${fallbackDate} (v1.1)`;
      })
      .catch(() => {
        statusEl.textContent = `Last updated: ${fallbackDate} (v1.1)`;
      });
  }

  renderPlate();
})();
