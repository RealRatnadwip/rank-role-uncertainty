/* Relational Superposition Theory // Monochrome Plate & Live Status */

(function () {
  "use strict";

  const BASE_WEIGHTS = [0.38, 0.29, 0.18, 0.15];
  const ROLES = ["r1", "r2", "r3", "r4"];
  let currentWeights = [...BASE_WEIGHTS];
  let collapsedIndex = null;

  const badgeEl = document.getElementById("stateBadge");
  const entropyEl = document.getElementById("entropyReadout");
  const regimeEl = document.getElementById("regimeReadout");
  const pokeBtn = document.getElementById("pokeBtn");
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

    if (entropyEl) {
      entropyEl.textContent = `H(w) = ${shannonEntropy(currentWeights).toFixed(3)} bits`;
    }
    if (regimeEl) {
      regimeEl.textContent = collapsedIndex !== null ? "POST-POKE EIGENSTATE" : "PRE-POKE MIXTURE";
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

  if (resetBtn) {
    resetBtn.addEventListener("click", () => {
      currentWeights = [...BASE_WEIGHTS];
      collapsedIndex = null;
      renderPlate();
    });
  }

  function pad2(n) {
    return String(n).padStart(2, "0");
  }

  function formatUtc24(isoStr) {
    const d = new Date(isoStr);
    if (Number.isNaN(d.getTime())) return "2026-11-26 23:12:10 UTC";
    const datePart = `${d.getUTCFullYear()}-${pad2(d.getUTCMonth() + 1)}-${pad2(d.getUTCDate())}`;
    const timePart = `${pad2(d.getUTCHours())}:${pad2(d.getUTCMinutes())}:${pad2(d.getUTCSeconds())}`;
    return `${datePart} ${timePart} UTC`;
  }

  /* Dynamically update footer timestamp (24h HH:MM:SS) from GitHub repository */
  const statusEl = document.getElementById("updateStatus");
  if (statusEl) {
    const fallbackIso = statusEl.getAttribute("data-fallback-ts") || "2026-11-26T23:12:10Z";
    const fallbackFormatted = formatUtc24(fallbackIso);

    if (typeof fetch === "function") {
      const apiUrl = "https://api.github.com/repos/RealRatnadwip/rank-role-uncertainty/commits?per_page=1";
      fetch(apiUrl, {
        cache: "no-store",
        headers: { Accept: "application/vnd.github+json" }
      })
        .then((res) => (res.ok ? res.json() : null))
        .then((data) => {
          if (Array.isArray(data) && data.length > 0) {
            const item = data[0];
            const sha = (item.sha || "").slice(0, 7);
            const rawDate =
              (item.commit && item.commit.committer && item.commit.committer.date) ||
              (item.commit && item.commit.author && item.commit.author.date) ||
              fallbackIso;
            const formatted = formatUtc24(rawDate);
            if (sha) {
              statusEl.textContent = `Last updated: ${formatted} (${sha}, v1.1)`;
              return;
            }
          }
          statusEl.textContent = `Last updated: ${fallbackFormatted} (v1.1)`;
        })
        .catch(() => {
          statusEl.textContent = `Last updated: ${fallbackFormatted} (v1.1)`;
        });
    } else {
      statusEl.textContent = `Last updated: ${fallbackFormatted} (v1.1)`;
    }
  }

  renderPlate();
})();
