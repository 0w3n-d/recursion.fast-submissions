// recursion.fast: the home page's hero figure, one evaluation drawn from the season's chain lengths.
// Each arm is one Keccak-256 chain (its length is the chain's length, to one scale; the open dot at
// its outer end is its fresh start). Clockwise from the top, the chains join one spiral, the running
// proof: step 1 takes two chains, every later step one. The spiral keeps one width and turns into the
// core, the last proof. Drawn once; CSS scales it.
'use strict';
(function () {
  // A copy of `[stream] lengths` in the core's harness/season.toml at the pin: M + 1 = 97 values,
  // step 1's two chains, then one per step (the same in every evaluation; the starts are fresh per
  // evaluation). When the season changes them, change them here and set the <svg> viewBox in
  // index.html to the one draw() computes (the browser's console shows it), so nothing moves on load.
  const LENGTHS = [
    202109, 151388, 556082, 207817, 394830, 542490, 355707, 348583, 331757, 353644,
    279314, 263002, 545955, 314021, 152163, 159823, 145404, 176242, 186633, 224157,
    174590, 287231, 165190, 164913, 197040, 150598, 167100, 136058, 292052, 236696,
    491493, 298824, 489211, 404649, 254274, 186064, 201614, 580522, 329791, 750780,
    149611, 146725, 986256, 684942, 195865, 270010, 202428, 324889, 501473, 260038,
    238449, 448940, 298915, 370193, 204450, 446253, 432030, 522345, 278618, 155263,
    158119, 237412, 442472, 284980, 162386, 210558, 148933, 641165, 980030, 791452,
    133460, 429685, 251011, 182656, 301491, 151149, 181150, 194910, 205798, 1011610,
    346439, 597766, 389391, 656622, 403982, 153100, 149058, 319683, 155616, 638315,
    237618, 218729, 328702, 662587, 377019, 150940, 206820,
  ];
  // common.js's helper when it is loaded (it is, before this file); a local one otherwise
  const svg = (window.RF && window.RF.svg) || function (tag, attrs) {
    const n = document.createElementNS('http://www.w3.org/2000/svg', tag);
    for (const [k, v] of Object.entries(attrs || {})) n.setAttribute(k, String(v));
    return n;
  };
  const f = x => Math.round(x * 100) / 100;

  function draw(s) {
    const C = 200, CORE = 13;             // the centre (C, C) and the core's radius
    const R1 = 84, R2 = 32;               // the proof's radius at step 1 and at step 96
    const K = LENGTHS.length, M = K - 1;  // 97 chains, 96 steps
    const GAP = 4;                        // empty slots at the top, between the last step and the first
    const da = 2 * Math.PI / (M + GAP);
    const stepAng = i => -Math.PI / 2 + (GAP / 2 + i - 0.5) * da;   // step i = 1 … 96, clockwise
    const a1 = stepAng(1), aM = stepAng(M), aEnd = aM + Math.PI / 2;
    // the proof's radius: linear in the angle to step 96, then a quarter turn into the core that
    // leaves step 96 with the same slope (a cubic Hermite curve), ending under the core's disc
    const slope = (R2 - R1) / (aM - a1), rIn = 4;
    const rad = a => {
      if (a <= aM) return R1 + slope * (a - a1);
      const t = (a - aM) / (aEnd - aM), t2 = t * t, t3 = t2 * t;
      return (2 * t3 - 3 * t2 + 1) * R2 + (t3 - 2 * t2 + t) * slope * (aEnd - aM)
        + (-2 * t3 + 3 * t2) * rIn + (t3 - t2) * -1.2 * (R2 - rIn);
    };
    const pt = (a, r) => [C + r * Math.cos(a), C + r * Math.sin(a)];
    const d = ps => 'M' + ps.map(p => f(p[0]) + ' ' + f(p[1])).join('L');

    // the proof: one spiral of one width, sampled finely, and the arc length at each step
    const N = 900, thread = [], at = [0];
    for (let j = 0; j <= N; j++) {
      const a = a1 + (aEnd - a1) * j / N;
      thread.push(pt(a, rad(a)));
      if (j) at.push(at[j - 1] + Math.hypot(thread[j][0] - thread[j - 1][0], thread[j][1] - thread[j - 1][1]));
    }
    const len = at[N], frac = a => at[Math.round((a - a1) / (aEnd - a1) * N)] / len;

    // the chains: arms of one pitch (log spirals, which never cross), each leaving the proof
    // backwards and outwards from its step; an arm's arc length is its chain's length
    const PITCH = 0.62, sp = Math.sin(PITCH), tp = Math.tan(PITCH);
    // chain k joins at step max(1, k); step 1's two chains leave half a slot apart
    const root = k => k < 2 ? [stepAng(1) + (k - 0.5) * 0.5 * da, rad(stepAng(1))] : [stepAng(k), rad(stepAng(k))];
    let L = Infinity;                      // the longest scale that keeps every start inside r = 196
    for (let k = 0; k < K; k++) L = Math.min(L, (196 - root(k)[1] - 2) / sp / (LENGTHS[k] / 2 ** 20));
    const T = 2;                           // seconds for the whole fold
    const arms = svg('g', { class: 'arms' });
    const box = [C, C, C, C];
    const grow = ([x, y]) => { box[0] = Math.min(box[0], x); box[1] = Math.min(box[1], y); box[2] = Math.max(box[2], x); box[3] = Math.max(box[3], y); };
    thread.forEach(grow);
    for (let k = 0; k < K; k++) {
      const [a0, r00] = root(k), r0 = r00 + 2.5, r1 = r0 + sp * L * LENGTHS[k] / 2 ** 20;
      const ps = [];
      for (let j = 0; j <= 48; j++) {
        const r = r0 * (r1 / r0) ** (j / 48);
        ps.push(pt(a0 - Math.log(r / r0) / tp, r));
      }
      ps.forEach(grow);
      const end = ps[ps.length - 1];
      // one group per chain (its arm and its start), animated as one
      const arm = svg('g');
      arm.style.setProperty('--d', f(T * frac(stepAng(Math.max(1, k)))) + 's');
      arm.append(svg('path', { d: d(ps.reverse()) }), svg('circle', { cx: f(end[0]), cy: f(end[1]), r: 1.5 }));
      arms.append(arm);
    }
    const proof = svg('path', { class: 'proof', d: d(thread) });
    proof.style.setProperty('--len', f(len));
    proof.style.setProperty('--t', T + 's');
    const core = svg('g', { class: 'core' });
    core.style.setProperty('--d', T + 's');
    core.append(svg('circle', { cx: C, cy: C, r: CORE }));
    const pi = svg('text', { x: C, y: C + 4.8, 'text-anchor': 'middle' });
    pi.textContent = '\u03c0';
    core.append(pi);

    // the chains fade toward their starts (never below 3:1 against the page; hero.css)
    const defs = svg('defs');
    const g = svg('radialGradient', { id: 'hero-fade', gradientUnits: 'userSpaceOnUse', cx: C, cy: C, r: 200 });
    g.append(svg('stop', { offset: '0.08', class: 'f0' }), svg('stop', { offset: '1', class: 'f1' }));
    defs.append(g);
    s.replaceChildren(defs, arms, proof, core);
    // the drawing's bounds and a margin; index.html carries the same viewBox
    const m = 4, vb = [box[0] - m, box[1] - m, box[2] - box[0] + 2 * m, box[3] - box[1] + 2 * m].map(f).join(' ');
    if (s.getAttribute('viewBox') !== vb) {
      console.warn('hero: the viewBox in index.html should be "' + vb + '"');
      s.setAttribute('viewBox', vb);
    }
    s.classList.add('play');
  }

  document.addEventListener('DOMContentLoaded', () => {
    const s = document.querySelector('#hero svg');
    if (s) draw(s);
  });
})();
