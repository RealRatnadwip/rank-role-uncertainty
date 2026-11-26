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
  const roleAxisEl = document.getElementById("roleAxisGroup");
  const pokeBtn = document.getElementById("pokeBtn");
  const gammaBtn = document.getElementById("gammaBtn");
  const resetBtn = document.getElementById("resetBtn");

  function shannonEntropy(weights) {
    return weights.reduce((acc, w) => (w <= 0 ? acc : acc - w * Math.log2(w)), 0);
  }

  function renderSchematic() {
    for (let i = 0; i < 4; i++) {
      const idx = i + 1;
      const w = currentWeights[i];
      const arc = document.getElementById(`arc${idx}`);
      const label = document.getElementById(`wlabel${idx}`);
      const node = document.getElementById(`node${idx}`);

      if (label) {
        label.textContent = `G${idx} // ${ROLES[i]} // w=${w.toFixed(2)}`;
        label.setAttribute(
          "fill",
          collapsedIndex === i ? "#EAEAEA" : (w > 0 ? (idx === 2 ? "#B892CC" : "#9E9EA8") : "#46464F")
        );
      }
      if (arc) {
        const strokeWidth = w > 0 ? (0.75 + 1.5 * w).toFixed(2) : "0.5";
        const alpha = w > 0 ? Math.max(0.22, w) : 0.06;
        arc.setAttribute("stroke-width", strokeWidth);
        arc.setAttribute(
          "stroke",
          collapsedIndex === i ? "rgba(184, 146, 204, 0.95)" : `rgba(234, 234, 234, ${alpha.toFixed(2)})`
        );
      }
      if (node) {
        node.setAttribute("opacity", w > 0 ? "1" : "0.24");
      }
    }

    if (roleAxisEl) {
      roleAxisEl.setAttribute("transform", gammaZero ? "rotate(0 500 250)" : "rotate(-26 500 250)");
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
        badgeEl.textContent = `STATE: COLLAPSED -> G${collapsedIndex + 1}`;
        badgeEl.classList.add("is-collapsed");
      } else {
        badgeEl.textContent = "STATE: SUPERPOSED";
        badgeEl.classList.remove("is-collapsed");
      }
    }
    if (gammaBtn) {
      gammaBtn.textContent = gammaZero ? "[ Restore gamma = 0.75 ]" : "[ Toggle gamma = 0 ]";
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

  /* Custom editorial cursor for fine desktop pointers */
  const dot = document.getElementById("cursorDot");
  const ring = document.getElementById("cursorRing");
  if (dot && ring && window.matchMedia("(hover: hover) and (pointer: fine)").matches) {
    let mouseX = 0;
    let mouseY = 0;
    let ringX = 0;
    let ringY = 0;
    let rafActive = false;

    document.addEventListener("mousemove", (e) => {
      mouseX = e.clientX;
      mouseY = e.clientY;
      dot.style.left = `${mouseX}px`;
      dot.style.top = `${mouseY}px`;
      document.body.classList.add("cursor-active");
      if (!rafActive) {
        rafActive = true;
        requestAnimationFrame(tickCursor);
      }
    });

    function tickCursor() {
      ringX += (mouseX - ringX) * 0.22;
      ringY += (mouseY - ringY) * 0.22;
      ring.style.left = `${ringX}px`;
      ring.style.top = `${ringY}px`;
      if (Math.abs(mouseX - ringX) > 0.2 || Math.abs(mouseY - ringY) > 0.2) {
        requestAnimationFrame(tickCursor);
      } else {
        rafActive = false;
      }
    }

    document.querySelectorAll("a, button").forEach((el) => {
      el.addEventListener("mouseenter", () => document.body.classList.add("cursor-hover"));
      el.addEventListener("mouseleave", () => document.body.classList.remove("cursor-hover"));
    });
  }

  /* Immediate hero reveal + scroll observer for subsequent blocks */
  document.querySelectorAll("#hero .reveal-item").forEach((el) => el.classList.add("visible"));

  const revealTargets = document.querySelectorAll(".reveal-item, .sep");
  if ("IntersectionObserver" in window) {
    const observer = new IntersectionObserver(
      (entries) => {
        entries.forEach((entry) => {
          if (entry.isIntersecting) {
            entry.target.classList.add("visible");
            observer.unobserve(entry.target);
          }
        });
      },
      { threshold: 0.1 }
    );
    revealTargets.forEach((el) => {
      if (!el.classList.contains("visible")) {
        observer.observe(el);
      }
    });
  } else {
    revealTargets.forEach((el) => el.classList.add("visible"));
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

  renderSchematic();
})();
