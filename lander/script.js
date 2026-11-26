/* Relational Superposition Theory // Lander Interactions */

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
  const pokeBtn = document.getElementById("pokeBtn");
  const gammaBtn = document.getElementById("gammaBtn");
  const resetBtn = document.getElementById("resetBtn");

  function shannonEntropy(weights) {
    return weights.reduce((acc, w) => {
      if (w <= 0) return acc;
      return acc - w * Math.log2(w);
    }, 0);
  }

  function renderSchematic() {
    for (let i = 0; i < 4; i++) {
      const idx = i + 1;
      const w = currentWeights[i];
      const edge = document.getElementById(`edge${idx}`);
      const label = document.getElementById(`wlabel${idx}`);
      const node = document.getElementById(`node${idx}`);
      const circle = node ? node.querySelector("circle") : null;

      if (label) {
        label.textContent = `${ROLES[i]} // ${w.toFixed(2)}`;
      }
      if (edge) {
        const opacity = w > 0 ? Math.max(0.22, w) : 0.06;
        const strokeWidth = w > 0 ? (0.8 + 1.8 * w).toFixed(2) : "0.6";
        edge.setAttribute("stroke-width", strokeWidth);
        edge.setAttribute(
          "stroke",
          collapsedIndex === i ? "rgba(159, 132, 172, 0.95)" : `rgba(234, 234, 234, ${opacity.toFixed(2)})`
        );
      }
      if (circle) {
        circle.setAttribute("opacity", w > 0 ? "1" : "0.28");
        circle.setAttribute(
          "stroke",
          collapsedIndex === i ? "#EAEAEA" : (w > 0 ? "rgba(255,255,255,0.45)" : "rgba(255,255,255,0.16)")
        );
      }
    }

    if (entropyEl) {
      entropyEl.textContent = `${shannonEntropy(currentWeights).toFixed(3)} bits`;
    }
    if (gammaEl) {
      if (collapsedIndex !== null) {
        gammaEl.textContent = "0.00 (collapsed eigenstate)";
      } else {
        gammaEl.textContent = gammaZero ? "0.00 (commuting, k_R = 0)" : "0.75 (non-commuting, k_R > 0)";
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
      renderSchematic();
    });
  }

  if (gammaBtn) {
    gammaBtn.addEventListener("click", () => {
      gammaZero = !gammaZero;
      renderSchematic();
    });
  }

  if (resetBtn) {
    resetBtn.addEventListener("click", () => {
      currentWeights = [...BASE_WEIGHTS];
      collapsedIndex = null;
      gammaZero = false;
      renderSchematic();
    });
  }

  /* Scroll reveal with immediate hero visibility and graceful fallback */
  const heroEl = document.querySelector(".hero");
  if (heroEl) heroEl.classList.add("is-visible");

  const revealNodes = document.querySelectorAll(".reveal");
  if ("IntersectionObserver" in window) {
    const observer = new IntersectionObserver(
      (entries) => {
        entries.forEach((entry) => {
          if (entry.isIntersecting) {
            entry.target.classList.add("is-visible");
            observer.unobserve(entry.target);
          }
        });
      },
      { threshold: 0.12 }
    );
    revealNodes.forEach((el) => observer.observe(el));
  } else {
    revealNodes.forEach((el) => el.classList.add("is-visible"));
  }

  /* Footer repository last-updated status via public GitHub API with offline fallback */
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

  renderSchematic();
})();
