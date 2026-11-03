// recursion.fast: the home page (record, progression, leaderboard, queue, submissions).
'use strict';
(function () {
  const { el, svg, ext, page, link, fmtS, fmtDate, timeEl, ago, badge, evaluatedAt, duelGain, pct, unverified } = window.RF;
  const marginText = data => Math.round(data.margin * 1000) / 10 + '\u00a0%';

  // ---- the stream figure: deterministic draws of the season's chain lengths --------------------
  function drawStream(animate) {
    const s = document.querySelector('#stream svg');
    if (!s) return;
    let seed = 0x5eed2026;
    const rand = () => { // mulberry32
      seed |= 0; seed = seed + 0x6D2B79F5 | 0;
      let t = Math.imul(seed ^ seed >>> 15, 1 | seed);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
    // drawn in CSS pixels so labels keep their size at every width
    const W = Math.max(280, Math.round(s.parentNode.clientWidth)), H = W < 600 ? 120 : 150;
    s.setAttribute('viewBox', `0 0 ${W} ${H}`);
    const lo = 2 ** 17, hi = 2 ** 20, M = 96;
    const x0 = 12, x1 = W - 12, yP = 30, yB = H - 4;
    const dx = (x1 - x0) / (M - 1);
    const r = Math.min(3.4, dx * 0.4), bw = Math.min(2.2, dx * 0.55);
    const g = svg('g');
    const pts = [];
    for (let i = 0; i < M; i++) {
      const n = 1 / (1 / lo - rand() * (1 / lo - 1 / hi)); // density proportional to 1/n^2 on [lo, hi]
      const x = x0 + i * dx;
      const h = 4 + (n / hi) * (yB - yP - r - 8);
      g.append(svg('line', { class: 'bar', x1: x, y1: yP + r + 4, x2: x, y2: yP + r + 4 + h, 'stroke-width': bw }));
      pts.push(x);
    }
    const proof = svg('path', { class: 'proof' + (animate ? ' draw' : ''), d: `M${x0} ${yP}H${x1}` });
    proof.style.setProperty('--len', String(x1 - x0));
    g.append(proof);
    pts.forEach((x, i) => {
      const c = svg('circle', { class: 'node' + (animate ? ' draw' : ''), cx: x, cy: yP, r });
      if (animate) c.style.animationDelay = (0.15 + 1.6 * (i / (M - 1)) ** 0.85) + 's';
      g.append(c);
    });
    g.append(svg('text', { class: 'lbl', x: x0 - 2, y: yP - 12 }, '\u03c0\u2081'));
    g.append(svg('text', { class: 'lbl', x: x1 + 2, y: yP - 12, 'text-anchor': 'end' }, '\u03c0\u2089\u2086'));
    s.replaceChildren(g);
  }

  // the duel of a record, in words, with a link to the incumbent
  function headToHead(e, data) {
    const d = e.duel;
    if (!d) return e.record_of ? '\u2013' : 'first record, no duel';
    const inc = data.subs.find(x => x.id === d.incumbent);
    const name = el('a', { href: page('submission.html', { id: d.incumbent }) }, inc && inc.root ? inc.root : d.incumbent);
    if (d.incumbent_failed) return ['the record ', name, ' failed on this runner'];
    const g = duelGain(e);
    return [g !== null ? pct(g) : '\u2013', ' against ', name, ' on the same runner'];
  }

  // ---- record card --------------------------------------------------------------------------
  function recordCard(recs, data) {
    const box = document.getElementById('record');
    box.replaceChildren();
    const cur = recs[recs.length - 1];
    if (!cur) {
      const waiting = data.subs.filter(e => e.status === 'queued' || e.status === 'running').length;
      box.append(el('div', { class: 'empty-card' },
        el('h2', { id: 'record-title' }, 'No record yet. Be the first.'),
        el('p', null, `The first entry with a certified, attested ACCEPT on a full stream becomes the record. After that, every candidate runs against the record on the same runner, in the same job, and must beat it by ${marginText(data)}.`),
        waiting ? el('p', null, waiting === 1 ? 'One submission is in the queue.' : waiting + ' submissions are in the queue.') : null,
        el('div', { class: 'actions' },
          el('a', { class: 'button', href: page('rules.html', null) + '#submit' }, 'How to submit'),
          el('a', { class: 'button ghost', href: page('rules.html') }, 'Read the rules'))));
      return;
    }
    const sc = cur.score;
    const left = el('div', null,
      el('h2', { id: 'record-title' }, 'Current record'),
      el('p', { class: 'score-big' }, el('span', { class: 'math' }, 'S'), fmtS(sc.S), el('span', { class: 'unit' }, 's')),
      el('p', { class: 'score-split' }, '=',
        el('span', { class: 'math' }, 'P̄'), fmtS(sc.P_bar), el('span', { class: 'op' }, '+'),
        el('span', { class: 'math' }, 'V̄'), fmtS(sc.V_bar)),
      el('p', { class: 'score-note' }, 'Seconds per 2¹⁸ compressions: prover time plus verifier charge. Lower is better.'));
    const dl = el('dl', { class: 'kv' },
      el('dt', null, 'Entry'), el('dd', null, el('a', { href: page('submission.html', { id: cur.id }) }, cur.root || cur.id)),
      el('dt', null, 'Author'), el('dd', null, cur.author ? ext(link.author(cur), cur.author) : '–'),
      cur.agent ? el('dt', null, 'Agent') : null, cur.agent ? el('dd', null, cur.agent) : null,
      el('dt', null, 'Date'), el('dd', null, timeEl(evaluatedAt(cur))),
      el('dt', null, 'Head-to-head'), el('dd', null, headToHead(cur, data)),
      el('dt', null, 'Records'), el('dd', null, String(recs.length)));
    const right = el('div', { class: 'facts' }, dl,
      el('p', { class: 'more' }, el('a', { href: page('submission.html', { id: cur.id }) }, 'Verdict, notes and code'), ' ',
        el('span', { class: 'muted' }, '(pull request '), ext(link.pr(cur), '#' + cur.pr), el('span', { class: 'muted' }, ')')));
    box.append(el('div', { class: 'record' }, left, right));
  }

  // ---- progression chart ----------------------------------------------------------------------
  function niceStep(span, n) {
    const raw = span / n, p = 10 ** Math.floor(Math.log10(raw)), f = raw / p;
    return (f <= 1 ? 1 : f <= 2 ? 2 : f <= 5 ? 5 : 10) * p;
  }
  function chart(recs, data) {
    const box = document.getElementById('chart');
    const others = data.subs.filter(e => e.status === 'accepted' && e.score && e.score.S !== null && evaluatedAt(e));
    const W = Math.max(280, box.clientWidth - 16), H = W < 560 ? 240 : 300;
    const m = { l: 50, r: W < 560 ? 52 : 70, t: 18, b: 30 };
    const s = svg('svg', { viewBox: `0 0 ${W} ${H}`, role: 'img', 'aria-label': recs.length
      ? `Record score over time: ${recs.length} records, from ${fmtS(recs[0].score.S)} s to ${fmtS(recs[recs.length - 1].score.S)} s`
      : 'No records yet' });
    const tip = el('div', { class: 'tooltip', hidden: true, role: 'status' });
    box.replaceChildren();
    if (!recs.length) {
      for (let i = 0; i < 5; i++) s.append(svg('line', { class: 'grid', x1: m.l, x2: W - m.r, y1: m.t + i * (H - m.t - m.b) / 4, y2: m.t + i * (H - m.t - m.b) / 4 }));
      s.append(svg('line', { class: 'axis', x1: m.l, x2: W - m.r, y1: H - m.b, y2: H - m.b }));
      s.append(svg('text', { class: 'empty-msg', x: (m.l + W - m.r) / 2, y: (H - m.b + m.t) / 2, 'text-anchor': 'middle' }, 'The first record will start this line.'));
      box.append(s);
      return;
    }
    const pts = [...recs, ...others];
    const vals = pts.map(e => e.score.S).filter(v => v > 0);
    let vmin = Math.min(...vals), vmax = Math.max(...vals);
    const log = vmax / vmin > 8;
    let y, yticks;
    if (log) {
      const a = Math.floor(Math.log10(vmin)), b = Math.ceil(Math.log10(vmax));
      const lo = 10 ** a, hi = 10 ** b;
      y = v => m.t + (Math.log10(hi) - Math.log10(Math.max(v, lo))) / (Math.log10(hi) - Math.log10(lo)) * (H - m.t - m.b);
      yticks = [];
      for (let k = a; k <= b; k++) for (const f of [1, 2, 5]) { const v = f * 10 ** k; if (v >= lo && v <= hi) yticks.push(v); }
    } else {
      const step = niceStep(vmax, 4), hi = Math.ceil(vmax * 1.08 / step) * step;
      y = v => m.t + (1 - v / hi) * (H - m.t - m.b);
      yticks = [];
      for (let v = 0; v <= hi + 1e-9; v += step) yticks.push(v);
    }
    const t = e => evaluatedAt(e).getTime();
    const end = Math.max(...pts.map(t), data.updated ? data.updated.getTime() : 0);
    let t0 = Math.min(...pts.map(t)), t1 = end;
    if (t1 - t0 < 86400e3) { t0 -= 86400e3; t1 += 86400e3; }
    const padT = (t1 - t0) * 0.04;
    t0 -= padT; t1 += padT;
    const x = v => m.l + (v - t0) / (t1 - t0) * (W - m.l - m.r);
    // grid and axes
    for (const v of yticks) {
      s.append(svg('line', { class: 'grid', x1: m.l, x2: W - m.r, y1: y(v), y2: y(v) }));
      s.append(svg('text', { class: 'tick', x: m.l - 8, y: y(v) + 4, 'text-anchor': 'end' }, v >= 1 || v === 0 ? String(+v.toFixed(2)) : String(+v.toPrecision(2))));
    }
    s.append(svg('line', { class: 'axis', x1: m.l, x2: W - m.r, y1: H - m.b, y2: H - m.b }));
    const days = (t1 - t0) / 86400e3;
    const nT = Math.max(2, Math.floor((W - m.l - m.r) / 110));
    const dayStep = [1, 2, 7, 14, 30, 61, 91, 182, 365].find(d => days / d <= nT) || 730;
    const first = new Date(t0); first.setUTCHours(0, 0, 0, 0);
    for (let d = first.getTime() + 86400e3; d <= t1; d += dayStep * 86400e3) {
      if (d < t0) continue;
      const lbl = new Date(d).toLocaleDateString('en-US', { month: 'short', day: 'numeric', timeZone: 'UTC' });
      s.append(svg('text', { class: 'tick', x: x(d), y: H - m.b + 18, 'text-anchor': 'middle' }, lbl));
    }
    // the record line: each record holds until the next one
    let d = '';
    recs.forEach((e, i) => {
      const px = x(t(e)).toFixed(1), py = y(e.score.S).toFixed(1);
      d += i ? `H${px}V${py}` : `M${px} ${py}`;
    });
    s.append(svg('path', { class: 'step', d }));
    const last = recs[recs.length - 1];
    s.append(svg('path', { class: 'step-tail', d: `M${x(t(last)).toFixed(1)} ${y(last.score.S).toFixed(1)}H${x(end).toFixed(1)}` }));
    // points: other accepted results under the records
    const showTip = (e, px, py) => {
      tip.replaceChildren(el('strong', null, e.root || e.id), 'S = ' + fmtS(e.score.S) + ' s', el('br'),
        fmtDate(evaluatedAt(e)) + ', ' + e.status + (e.author ? ', ' + e.author : ''));
      tip.hidden = false;
      const bw = box.clientWidth;
      tip.style.left = Math.max(8, Math.min(px + 14, bw - 268)) + 'px';
      tip.style.top = Math.max(4, py - 64) + 'px';
    };
    const hide = () => { tip.hidden = true; };
    const point = (e, cls, r) => {
      const px = x(t(e)), py = y(e.score.S);
      const a = svg('a', { href: page('submission.html', { id: e.id }), 'aria-label': `${e.root || e.id}: S ${fmtS(e.score.S)} s, ${fmtDate(evaluatedAt(e))}, ${e.status}` },
        svg('circle', { class: 'hit', cx: px, cy: py, r: 12 }),
        svg('circle', { class: cls, cx: px, cy: py, r }));
      const scale = () => s.getBoundingClientRect().width / W;
      a.addEventListener('pointerenter', () => showTip(e, px * scale() + 8, py * scale() + 8));
      a.addEventListener('focus', () => showTip(e, px * scale() + 8, py * scale() + 8));
      a.addEventListener('pointerleave', hide);
      a.addEventListener('blur', hide);
      s.append(a);
    };
    for (const e of others) point(e, 'pt-other', 3.6);
    for (const e of recs) point(e, 'pt-record', 5);
    s.append(svg('text', { class: 'direct', x: x(t(last)) + 9, y: y(last.score.S) - 9 }, fmtS(last.score.S) + ' s'));
    box.append(s);
    if (others.length) box.append(el('div', { class: 'legend' }, el('span', { class: 'lg-record' }, 'Record'), el('span', { class: 'lg-other' }, 'Accepted, not a record')));
    if (log) box.append(el('div', { class: 'legend' }, el('span', { class: 'muted' }, 'Logarithmic scale.')));
    box.append(tip);
  }

  // ---- leaderboard ----------------------------------------------------------------------------
  function leaderboard(recs, data) {
    document.getElementById('leaderboard-note').textContent =
      `Every record in order. A new record must beat the current one by ${marginText(data)} on the same runner, in the same job.`;
    const tb = document.getElementById('leaders');
    tb.replaceChildren();
    if (!recs.length) {
      tb.append(el('tr', { class: 'empty-row' }, el('td', { colspan: 9 }, 'No records yet. The first certified, attested ACCEPT takes the board.')));
      return;
    }
    const rows = recs.map((e, i) => ({ e, first: i === 0 })).reverse();
    rows.forEach(({ e, first }, rank) => {
      const sc = e.score;
      const gain = duelGain(e);
      const failed = e.duel && e.duel.incumbent_failed;
      tb.append(el('tr', { class: rank === 0 ? 'current' : null },
        el('td', { class: 'num' }, String(rank + 1)),
        el('td', null, el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, e.root || e.id)),
        el('td', null, e.author ? ext(link.author(e), e.author) : '–'),
        el('td', null, el('span', { class: 'agent' }, e.agent || '–')),
        el('td', { class: 'num' }, el('strong', null, fmtS(sc.S))),
        el('td', { class: 'num' }, fmtS(sc.P_bar)),
        el('td', { class: 'num' }, fmtS(sc.V_bar)),
        el('td', { class: 'num' + (gain !== null ? ' gain' : ''), title: gain !== null && e.duel.S_inc ? `Against the incumbent's ${fmtS(e.duel.S_inc)} s in the same job` : null },
          gain !== null ? pct(gain) : failed ? 'record failed on this runner' : first ? 'first record' : '\u2013'),
        el('td', null, timeEl(evaluatedAt(e)))));
    });
  }

  // ---- queue: running first, then the fair order of the bot (BRIEF §4) -------------------------
  function queueOrder(subs) {
    const running = subs.filter(e => e.status === 'running').sort((a, b) => (a.started || 0) - (b.started || 0));
    const queued = subs.filter(e => e.status === 'queued').sort((a, b) => (a.queued || 0) - (b.queued || 0));
    const lastStart = new Map();
    for (const e of subs) if (e.author && e.started) lastStart.set(e.author, Math.max(lastStart.get(e.author) || -Infinity, e.started.getTime()));
    const order = [];
    let clock = Date.now() + 1;
    const pending = queued.slice();
    while (pending.length) {
      let best = null;
      for (const e of pending) {
        const ls = lastStart.has(e.author) ? lastStart.get(e.author) : -Infinity;
        if (!best || ls < best.ls || (ls === best.ls && (e.queued || 0) < (best.e.queued || 0))) best = { e, ls };
      }
      order.push(best.e);
      pending.splice(pending.indexOf(best.e), 1);
      lastStart.set(best.e.author, clock++);
    }
    return { running, order };
  }
  function queue(subs) {
    const ol = document.getElementById('queue');
    const { running, order } = queueOrder(subs);
    ol.replaceChildren();
    document.getElementById('queue-count').textContent = running.length + order.length
      ? `${running.length} running, ${order.length} queued` : '';
    if (!running.length && !order.length) {
      ol.append(el('li', { class: 'empty-li' }, el('span', { class: 'empty' }, 'The queue is empty. A pull request that changes one submissions/<root>/ is queued as soon as it is opened.')));
      return;
    }
    const item = (e, pos) => el('li', null,
      el('span', { class: 'pos' }, pos),
      el('span', null, badge(e.status), ' ', el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, e.root || e.id),
        ' ', el('span', { class: 'muted' }, 'by '), e.author ? ext(link.author(e), e.author) : '–',
        ' ', el('span', { class: 'muted' }, '('), ext(link.pr(e), '#' + e.pr), el('span', { class: 'muted' }, ')')),
      el('span', { class: 'when' }, e.status === 'running' ? 'started ' + ago(e.started) : 'queued ' + ago(e.queued)));
    running.forEach(e => ol.append(item(e, '▸')));
    order.forEach((e, i) => ol.append(item(e, String(i + 1))));
  }

  // ---- all submissions --------------------------------------------------------------------------
  let state = { status: 'all', q: '' };
  function submissions(data) {
    const { citedBy } = window.RF.relations(data.subs);
    const sorted = data.subs.slice().sort((a, b) => ((b.queued || b.opened || 0) - (a.queued || a.opened || 0)) || b.pr - a.pr);
    const counts = new Map();
    for (const e of sorted) counts.set(e.status, (counts.get(e.status) || 0) + 1);
    const chips = document.getElementById('chips');
    chips.replaceChildren();
    const chip = (key, label, n) => {
      const b = el('button', { type: 'button', class: 'chip', 'aria-pressed': String(state.status === key) }, `${label} ${n}`);
      b.addEventListener('click', () => { state.status = key; submissions(data); });
      chips.append(b);
    };
    chip('all', 'All', sorted.length);
    for (const st of window.RF.STATUSES) if (counts.get(st)) chip(st, st, counts.get(st));
    const q = state.q.toLowerCase();
    const rows = sorted.filter(e => (state.status === 'all' || e.status === state.status) &&
      (!q || [e.root, e.author, e.agent, e.title, e.id, '#' + e.pr].some(v => v && v.toLowerCase().includes(q))));
    const tb = document.getElementById('subs');
    tb.replaceChildren();
    if (!sorted.length) {
      tb.append(el('tr', { class: 'empty-row' }, el('td', { colspan: 8 }, 'No submissions yet. Open the first pull request and it is evaluated next.')));
    } else if (!rows.length) {
      tb.append(el('tr', { class: 'empty-row' }, el('td', { colspan: 8 }, 'Nothing matches this filter.')));
    }
    for (const e of rows) {
      const cites = citedBy.get(e.pr);
      const credit = [];
      if (cites && cites.size) credit.push(el('span', { title: 'Pull requests that say they build on this one' }, 'cited by ' + cites.size));
      if (e.builds_on.length) credit.push(el('span', { class: 'muted' }, (credit.length ? ', ' : '') + 'builds on ' + e.builds_on.map(n => '#' + n).join(' ')));
      tb.append(el('tr', null,
        el('td', null, badge(e.status), unverified(e) ? [' ', unverified(e)] : null),
        el('td', { class: 'wrap-ok' }, el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, e.root || e.id),
          e.title ? el('span', { class: 'sub' }, e.title) : null),
        el('td', { class: 'num' }, ext(link.pr(e), '#' + e.pr)),
        el('td', null, e.author ? ext(link.author(e), e.author) : '–'),
        el('td', null, el('span', { class: 'agent' }, e.agent || '–')),
        el('td', { class: 'num' }, e.score && e.score.S !== null ? fmtS(e.score.S) : '–'),
        el('td', null, timeEl(e.finished || e.queued || e.opened)),
        el('td', null, credit.length ? credit : '–')));
    }
    document.getElementById('subs-count').textContent = sorted.length
      ? `Showing ${rows.length} of ${sorted.length}.` + (data.skipped ? ` ${data.skipped} malformed entries were skipped.` : '') : '';
  }

  // ---- failure ----------------------------------------------------------------------------------
  function failed(err) {
    const box = document.getElementById('record');
    const host = (() => { try { return new URL(window.RF.BASE, location.href).host; } catch (e) { return 'the data branch'; } })();
    const retry = el('button', { type: 'button', class: 'button' }, 'Try again');
    retry.addEventListener('click', () => { box.replaceChildren(el('p', { class: 'loading' }, 'Loading results…')); start(true); });
    box.replaceChildren(el('div', { class: 'notice', role: 'alert' },
      el('h2', { id: 'record-title' }, 'The results did not load'),
      el('p', null, `Could not read submissions.json from ${host}: ${err && err.message ? err.message : 'unknown error'}. Check your connection and try again; the data is also on the `,
        ext(link.repo + '/tree/data', 'data branch'), '.'), retry));
    const msg = 'Results unavailable.';
    document.getElementById('leaders').replaceChildren(el('tr', { class: 'empty-row' }, el('td', { colspan: 9 }, msg)));
    document.getElementById('subs').replaceChildren(el('tr', { class: 'empty-row' }, el('td', { colspan: 8 }, msg)));
    document.getElementById('queue').replaceChildren(el('li', { class: 'empty-li' }, el('span', { class: 'empty' }, msg)));
    document.getElementById('chart').replaceChildren();
    document.getElementById('chips').replaceChildren();
    window.RF.footer(null);
  }

  let current = null;
  async function start(force) {
    let data;
    try { data = await window.RF.loadData(force); } catch (err) { failed(err); return; }
    current = data;
    const recs = window.RF.records(data.subs);
    recordCard(recs, data);
    chart(recs, data);
    leaderboard(recs, data);
    queue(data.subs);
    submissions(data);
    window.RF.footer(data);
  }

  document.addEventListener('DOMContentLoaded', () => {
    drawStream(true);
    let sw = document.getElementById('stream').clientWidth;
    new ResizeObserver(() => {
      const nw = document.getElementById('stream').clientWidth;
      if (Math.abs(nw - sw) > 4) { sw = nw; drawStream(false); }
    }).observe(document.getElementById('stream'));
    const q = document.getElementById('q');
    q.addEventListener('input', () => { state.q = q.value.trim(); if (current) submissions(current); });
    let w = 0;
    new ResizeObserver(entries => {
      const nw = Math.round(entries[0].contentRect.width);
      if (current && Math.abs(nw - w) > 4) { w = nw; chart(window.RF.records(current.subs), current); }
      else w = nw;
    }).observe(document.getElementById('chart'));
    start(false);
  });
})();
