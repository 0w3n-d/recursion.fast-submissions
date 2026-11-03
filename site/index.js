// recursion.fast: the home page (record, progression, leaderboard, queue, submissions).
'use strict';
(function () {
  const { el, svg, ext, page, link, fmtS, fmtDate, timeEl, ago, badge, evaluatedAt, duelGain, pct, unverified } = window.RF;
  const marginText = data => Math.round(data.margin * 1000) / 10 + '\u00a0%';
  const winsText = data => data.wins === 1 ? 'in one duel' : data.wins === 2 ? 'in two duels in a row' : `in ${data.wins} duels in a row`;

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

  // the duel of an entry, in words, with a link to the incumbent
  function headToHead(e, data, nm) {
    const d = e.duel;
    if (!d) return e.port_of ? 'none (the record re-run at a new pin)' : 'none (no record stood at its pin)';
    const inc = data.subs.find(x => x.id === d.incumbent);
    const name = el('a', { href: page('submission.html', { id: d.incumbent }) }, inc ? nm(inc) : d.incumbent);
    if (d.incumbent_failed) return ['the record ', name, ' failed on this runner'];
    const g = duelGain(e);
    const n = e.duels.filter(x => x.won).length;
    return [pct(g), ' against ', name, ' on the same runner', n > 1 ? ` (the smaller of ${n} duels won)` : ''];
  }
  const short = sha => sha ? sha.slice(0, 7) : 'unknown';

  // ---- record card: the bot's standing record (`record` in submissions.json) ----------------------
  function recordCard(recs, data, nm) {
    const box = document.getElementById('record');
    box.replaceChildren();
    const cur = data.record;
    if (!cur) {
      const waiting = data.subs.filter(e => ['queued', 'running', 'confirming'].includes(e.status)).length;
      const last = recs[recs.length - 1];
      box.append(el('div', { class: 'empty-card' },
        el('h2', null, last ? 'No standing record at this contract pin.' : 'No record yet. Be the first.'),
        last ? el('p', null, `The records so far were set at earlier pins or retired (the leaderboard keeps them). The first certified, comparable, attested ACCEPT at pin ${short(data.core)} becomes the record, without a duel.`)
          : el('p', null, `The first entry with a certified, comparable, attested ACCEPT becomes the record. After that, every candidate runs against the record on the same runner, in the same job, and must beat it by ${marginText(data)}, ${winsText(data)}.`),
        data.unpublished ? el('p', null, 'Nothing has been published yet: the first pull request starts the record book.') : null,
        waiting ? el('p', null, waiting === 1 ? 'One submission is in the queue.' : waiting + ' submissions are in the queue.') : null,
        el('div', { class: 'actions' },
          el('a', { class: 'button', href: page('rules.html') + '#submit' }, 'How to submit'),
          el('a', { class: 'button ghost', href: page('rules.html') }, 'Read the rules'))));
      return;
    }
    const sc = cur.score;
    const left = el('div', null,
      el('h2', null, 'Current record'),
      el('p', { class: 'score-big' }, el('span', { class: 'math' }, 'S'), fmtS(sc.S), el('span', { class: 'unit' }, 's')),
      el('p', { class: 'score-split' }, '=',
        el('span', { class: 'math' }, 'P̄'), fmtS(sc.P_bar), el('span', { class: 'op' }, '+'),
        el('span', { class: 'math' }, 'V̄'), fmtS(sc.V_bar)),
      el('p', { class: 'score-note' }, 'Seconds per 2¹⁸ compressions: prover time plus verifier charge. Lower is better.'));
    const dl = el('dl', { class: 'kv' },
      el('dt', null, 'Entry'), el('dd', null, el('a', { href: page('submission.html', { id: cur.id }) }, nm(cur))),
      el('dt', null, 'Author'), el('dd', null, cur.author ? ext(link.author(cur), cur.author) : '–'),
      cur.agent ? el('dt', null, 'Agent') : null, cur.agent ? el('dd', null, cur.agent) : null,
      el('dt', null, 'Date'), el('dd', null, timeEl(evaluatedAt(cur))),
      el('dt', null, 'Head-to-head'), el('dd', null, headToHead(cur, data, nm)),
      el('dt', null, 'Contract pin'), el('dd', null, cur.harness_commit ? ext(link.core(cur.harness_commit), short(cur.harness_commit)) : '–'));
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
  function chart(recs, data, nm) {
    const box = document.getElementById('chart');
    const others = data.subs.filter(e => e.status === 'accepted' && e.score && e.score.S !== null && e.score.S > 0 && evaluatedAt(e));
    const W = Math.max(280, box.clientWidth - 16), H = W < 560 ? 240 : 300;
    const m = { l: 50, r: W < 560 ? 52 : 70, t: 18, b: 30 };
    const pos = recs.filter(e => e.score.S > 0);
    const s = svg('svg', { viewBox: `0 0 ${W} ${H}`, role: 'img', 'aria-label': pos.length
      ? `Record score over time: ${pos.length} records, from ${fmtS(pos[0].score.S)} s to ${fmtS(pos[pos.length - 1].score.S)} s`
      : 'No records yet' });
    const tip = el('div', { class: 'tooltip', hidden: true, role: 'status' });
    box.replaceChildren();
    if (!pos.length) {
      for (let i = 0; i < 5; i++) s.append(svg('line', { class: 'grid', x1: m.l, x2: W - m.r, y1: m.t + i * (H - m.t - m.b) / 4, y2: m.t + i * (H - m.t - m.b) / 4 }));
      s.append(svg('line', { class: 'axis', x1: m.l, x2: W - m.r, y1: H - m.b, y2: H - m.b }));
      s.append(svg('text', { class: 'empty-msg', x: (m.l + W - m.r) / 2, y: (H - m.b + m.t) / 2, 'text-anchor': 'middle' }, 'The first record will start this line.'));
      box.append(s);
      return;
    }
    const pts = [...pos, ...others.slice(-2000)];
    const vals = pts.map(e => e.score.S);
    const vmin = Math.min(...vals), vmax = Math.max(...vals);
    const log = vmax / vmin > 8;
    let y, yticks;
    if (log) {
      const a = Math.max(-300, Math.floor(Math.log10(vmin))), b = Math.min(300, Math.max(a + 1, Math.ceil(Math.log10(vmax))));
      const lo = 10 ** a, hi = 10 ** b;
      y = v => m.t + (Math.log10(hi) - Math.log10(Math.min(hi, Math.max(v, lo)))) / (Math.log10(hi) - Math.log10(lo)) * (H - m.t - m.b);
      yticks = [];
      const every = Math.max(1, Math.ceil((b - a) / 6));
      for (let k = a; k <= b; k += every) for (const f of (b - a > 3 ? [1] : [1, 2, 5])) { const v = f * 10 ** k; if (v >= lo && v <= hi) yticks.push(v); }
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
    for (const v of yticks) {
      s.append(svg('line', { class: 'grid', x1: m.l, x2: W - m.r, y1: y(v), y2: y(v) }));
      s.append(svg('text', { class: 'tick', x: m.l - 8, y: y(v) + 4, 'text-anchor': 'end' }, v >= 1 && v < 1e6 || v === 0 ? String(+v.toFixed(2)) : v.toExponential(0)));
    }
    s.append(svg('line', { class: 'axis', x1: m.l, x2: W - m.r, y1: H - m.b, y2: H - m.b }));
    const days = (t1 - t0) / 86400e3;
    const nT = Math.max(2, Math.floor((W - m.l - m.r) / 110));
    const dayStep = [1, 2, 7, 14, 30, 61, 91, 182, 365].find(d => days / d <= nT) || Math.ceil(days / nT);
    const first = new Date(t0); first.setUTCHours(0, 0, 0, 0);
    for (let d = first.getTime() + 86400e3; d <= t1; d += dayStep * 86400e3) {
      if (d < t0) continue;
      const lbl = new Date(d).toLocaleDateString('en-US', { month: 'short', day: 'numeric', timeZone: 'UTC' });
      s.append(svg('text', { class: 'tick', x: x(d), y: H - m.b + 18, 'text-anchor': 'middle' }, lbl));
    }
    // the record line: each record holds until the next one at the same pin; a new pin breaks it
    let d = '', prev = null;
    for (const e of pos) {
      const px = x(t(e)).toFixed(1), py = y(e.score.S).toFixed(1);
      d += prev && prev.harness_commit === e.harness_commit ? `H${px}V${py}` : `M${px} ${py}`;
      prev = e;
    }
    s.append(svg('path', { class: 'step', d }));
    const cur = data.record && pos.includes(data.record) ? data.record : null;
    if (cur) s.append(svg('path', { class: 'step-tail', d: `M${x(t(cur)).toFixed(1)} ${y(cur.score.S).toFixed(1)}H${x(end).toFixed(1)}` }));
    const showTip = (e, px, py) => {
      tip.replaceChildren(el('strong', null, nm(e)), 'S = ' + fmtS(e.score.S) + ' s', el('br'),
        fmtDate(evaluatedAt(e)) + ', ' + e.status + (e.author ? ', ' + e.author : ''));
      tip.hidden = false;
      const bw = box.clientWidth;
      tip.style.left = Math.max(8, Math.min(px + 14, bw - 268)) + 'px';
      tip.style.top = Math.max(4, py - 64) + 'px';
    };
    const hide = () => { tip.hidden = true; };
    const point = (e, cls, r) => {
      const px = x(t(e)), py = y(e.score.S);
      const a = svg('a', { href: page('submission.html', { id: e.id }), 'aria-label': `${nm(e)}: S ${fmtS(e.score.S)} s, ${fmtDate(evaluatedAt(e))}, ${e.status}` },
        svg('circle', { class: 'hit', cx: px, cy: py, r: 12 }),
        svg('circle', { class: cls, cx: px, cy: py, r }));
      const scale = () => s.getBoundingClientRect().width / W;
      a.addEventListener('pointerenter', () => showTip(e, px * scale() + 8, py * scale() + 8));
      a.addEventListener('focus', () => showTip(e, px * scale() + 8, py * scale() + 8));
      a.addEventListener('pointerleave', hide);
      a.addEventListener('blur', hide);
      s.append(a);
    };
    for (const e of others.slice(-2000)) point(e, 'pt-other', 3.6);
    for (const e of pos) point(e, e.status === 'retired' ? 'pt-retired' : 'pt-record', 5);
    const lab = cur || pos[pos.length - 1];
    s.append(svg('text', { class: 'direct', x: x(t(lab)) + 9, y: y(lab.score.S) - 9 }, fmtS(lab.score.S) + ' s'));
    box.append(s);
    const hasRetired = pos.some(e => e.status === 'retired');
    if (others.length || hasRetired) box.append(el('div', { class: 'legend' }, el('span', { class: 'lg-record' }, 'Record'),
      hasRetired ? el('span', { class: 'lg-retired' }, 'Retired record') : null,
      others.length ? el('span', { class: 'lg-other' }, 'Accepted, not a record') : null));
    if (log) box.append(el('div', { class: 'legend' }, el('span', { class: 'muted' }, 'Logarithmic scale.')));
    box.append(tip);
  }

  // ---- leaderboard: every record (`record`, `retired`), newest first, grouped by contract pin ------
  function leaderboard(recs, data, nm) {
    document.getElementById('leaderboard-note').textContent =
      `Every record, newest first. A new record must beat the standing one by ${marginText(data)} on the same runner, in the same job, ${winsText(data)}.`;
    const tb = document.getElementById('leaders');
    tb.replaceChildren();
    if (!recs.length) {
      tb.append(el('tr', { class: 'empty-row' }, el('td', { colspan: 9 }, 'No records yet. The first certified, comparable, attested ACCEPT takes the board.')));
      return;
    }
    const numbered = recs.map((e, i) => ({ e, n: i + 1 })).reverse();
    let pin;
    for (const { e, n } of numbered) {
      if (e.harness_commit !== pin) {
        pin = e.harness_commit;
        tb.append(el('tr', { class: 'pin-row' }, el('th', { colspan: 9 },
          'Contract pin ', pin ? ext(link.core(pin), short(pin)) : 'unknown',
          pin && pin === data.core ? ' (current)' : ' (earlier pin)')));
      }
      const sc = e.score;
      const gain = duelGain(e);
      const isCur = data.record && data.record.id === e.id;
      tb.append(el('tr', { class: isCur ? 'current' : null },
        el('td', { class: 'num' }, String(n)),
        el('td', null, el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, nm(e)),
          isCur ? [' ', el('span', { class: 'badge st-record' }, 'current')] : e.status === 'retired' ? [' ', badge('retired')] : null),
        el('td', null, e.author ? ext(link.author(e), e.author) : '–'),
        el('td', null, el('span', { class: 'agent' }, e.agent || '–')),
        el('td', { class: 'num' }, el('strong', null, fmtS(sc.S))),
        el('td', { class: 'num' }, fmtS(sc.P_bar)),
        el('td', { class: 'num' }, fmtS(sc.V_bar)),
        el('td', { class: 'num' + (gain !== null ? ' gain' : ''), title: gain !== null && e.duel.S_inc ? `Against the incumbent's ${fmtS(e.duel.S_inc)} s in the same job` : null },
          gain !== null ? pct(gain) : e.port_of ? 'ported' : 'no duel'),
        el('td', null, timeEl(evaluatedAt(e)))));
    }
  }

  // ---- queue: running first, then confirmations and ports, then the bot's fair order by author ----
  function queueOrder(subs) {
    const running = subs.filter(e => e.status === 'running').sort((a, b) => (a.started || 0) - (b.started || 0));
    // a waiting port first, then the confirmations, each oldest first (the bot's order)
    const front = subs.filter(e => e.status === 'confirming' || (e.status === 'queued' && e.port_of))
      .sort((a, b) => ((a.status === 'confirming') - (b.status === 'confirming')) || (a.queued || 0) - (b.queued || 0));
    const queued = subs.filter(e => e.status === 'queued' && !e.port_of).sort((a, b) => (a.queued || 0) - (b.queued || 0));
    const lastStart = new Map();
    for (const e of subs) if (e.author && e.started) lastStart.set(e.author, Math.max(lastStart.get(e.author) || -Infinity, e.started.getTime()));
    const order = front.slice();
    let clock = Date.now() + 1;
    const byAuthor = new Map();
    for (const e of queued) { if (!byAuthor.has(e.author)) byAuthor.set(e.author, []); byAuthor.get(e.author).push(e); }
    while (byAuthor.size && order.length < 500 + front.length) {
      let best = null;
      for (const [a, list] of byAuthor) {
        const ls = lastStart.has(a) ? lastStart.get(a) : -Infinity, e = list[0];
        if (!best || ls < best.ls || (ls === best.ls && (e.queued || 0) < (best.e.queued || 0))) best = { a, e, ls };
      }
      order.push(best.e);
      const list = byAuthor.get(best.a); list.shift();
      if (!list.length) byAuthor.delete(best.a);
      lastStart.set(best.a, clock++);
    }
    return { running, order, total: queued.length + front.length };
  }
  function queue(subs, nm) {
    const ol = document.getElementById('queue');
    const { running, order, total } = queueOrder(subs);
    ol.replaceChildren();
    document.getElementById('queue-count').textContent = running.length + total ? `${running.length} running, ${total} queued` : '';
    if (!running.length && !order.length) {
      ol.append(el('li', { class: 'empty-li' }, el('span', { class: 'empty' }, 'The queue is empty. A pull request that changes one submissions/<root>/ is queued as soon as it is opened.')));
      return;
    }
    const item = (e, pos) => el('li', null,
      el('span', { class: 'pos' }, pos),
      el('span', null, badge(e.status), ' ', el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, nm(e)),
        ' ', el('span', { class: 'muted' }, 'by '), e.author ? ext(link.author(e), e.author) : '–',
        ' ', el('span', { class: 'muted' }, '('), ext(link.pr(e), '#' + e.pr), el('span', { class: 'muted' }, ')')),
      el('span', { class: 'when' }, e.status === 'running' ? (e.started ? 'started ' + ago(e.started) : 'started')
        : e.status === 'confirming' ? 'won a duel; confirmation next' : (e.queued ? 'queued ' + ago(e.queued) : 'queued')));
    running.forEach(e => ol.append(item(e, '▸')));
    order.forEach((e, i) => ol.append(item(e, String(i + 1))));
    if (total > order.length) ol.append(el('li', { class: 'empty-li' }, el('span', { class: 'empty' }, `and ${total - order.length} more`)));
  }

  // ---- all submissions --------------------------------------------------------------------------
  const PAGE = 200;
  const state = { status: 'all', q: '', limit: PAGE };
  function submissions(data, nm, focusKey) {
    const rel = window.RF.relations(data.subs);
    const sorted = data.subs.slice().sort((a, b) => ((b.queued || b.opened || 0) - (a.queued || a.opened || 0)) || b.pr - a.pr);
    const counts = new Map();
    for (const e of sorted) counts.set(e.status, (counts.get(e.status) || 0) + 1);
    const chips = document.getElementById('chips');
    chips.replaceChildren();
    const chip = (key, label, n) => {
      const b = el('button', { type: 'button', class: 'chip', 'data-key': key, 'aria-pressed': String(state.status === key) }, `${label} ${n}`);
      b.addEventListener('click', () => { state.status = key; state.limit = PAGE; submissions(data, nm, key); });
      chips.append(b);
    };
    chip('all', 'All', sorted.length);
    for (const st of window.RF.STATUSES) if (counts.get(st)) chip(st, st, counts.get(st));
    if (focusKey) { const f = chips.querySelector(`button[data-key="${focusKey}"]`); if (f) f.focus(); }
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
    for (const e of rows.slice(0, state.limit)) {
      const n = rel.citeCount(e.pr);
      const credit = [];
      if (n) credit.push(el('span', { title: 'Pull requests by other authors, with a verdict, that say they build on this one' }, 'cited by ' + n));
      if (e.builds_on.length) credit.push(el('span', { class: 'muted' }, (credit.length ? ', ' : '') + 'builds on ' + e.builds_on.map(k => '#' + k).join(' ')));
      tb.append(el('tr', null,
        el('td', null, badge(e.status), unverified(e) ? [' ', unverified(e)] : null),
        el('td', { class: 'wrap-ok' }, el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, nm(e)),
          e.title ? el('span', { class: 'sub' }, e.title) : null),
        el('td', { class: 'num' }, ext(link.pr(e), '#' + e.pr)),
        el('td', null, e.author ? ext(link.author(e), e.author) : '–'),
        el('td', null, el('span', { class: 'agent' }, e.agent || '–')),
        el('td', { class: 'num' }, e.score && e.score.S !== null ? fmtS(e.score.S) : '–'),
        el('td', null, timeEl(e.finished || e.queued || e.opened)),
        el('td', null, credit.length ? credit : '–')));
    }
    const more = document.getElementById('subs-more');
    more.replaceChildren();
    if (rows.length > state.limit) {
      const b = el('button', { type: 'button', class: 'button ghost' }, `Show ${Math.min(PAGE, rows.length - state.limit)} more`);
      b.addEventListener('click', () => { state.limit += PAGE; submissions(data, nm); });
      more.append(b);
    }
    const notes = [];
    if (data.skipped) notes.push(`${data.skipped} malformed entries were skipped.`);
    if (data.notShown) notes.push(`${data.notShown} older entries beyond the site's 20,000 are not shown.`);
    document.getElementById('subs-count').textContent = sorted.length
      ? `Showing ${Math.min(rows.length, state.limit)} of ${rows.length}` + (rows.length !== sorted.length ? ` matching (${sorted.length} in all)` : '') + '. '
        + (rows.length > state.limit ? 'Refine the search or show more. ' : '') + notes.join(' ') : '';
  }

  // ---- failure ----------------------------------------------------------------------------------
  function failed(err) {
    const box = document.getElementById('record');
    const host = (() => { try { return new URL(window.RF.BASE, location.href).host; } catch (e) { return 'the data branch'; } })();
    const retry = el('button', { type: 'button', class: 'button' }, 'Try again');
    retry.addEventListener('click', () => { box.replaceChildren(el('p', { class: 'loading' }, 'Loading results…')); start(true); });
    box.replaceChildren(el('div', { class: 'notice', role: 'alert' },
      el('h2', null, 'The results did not load'),
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

  let current = null, names = null;
  async function start(force) {
    let data;
    try { data = await window.RF.loadData(force); } catch (err) { failed(err); return; }
    current = data;
    const { section } = window.RF;
    let recs = [];
    section('records', 'record', () => { names = window.RF.nameOf(data.subs); recs = window.RF.records(data.subs); });
    const nm = names || (e => e.root || e.id);
    section('current record', 'record', () => recordCard(recs, data, nm));
    section('progression', 'chart', () => chart(recs, data, nm));
    section('leaderboard', 'leaders', () => leaderboard(recs, data, nm));
    section('queue', 'queue', () => queue(data.subs, nm));
    section('submissions', 'subs', () => submissions(data, nm));
    section('footer', 'pin', () => window.RF.footer(data));
  }

  document.addEventListener('DOMContentLoaded', () => {
    drawStream(true);
    let sw = document.getElementById('stream').clientWidth;
    new ResizeObserver(() => {
      const nw = document.getElementById('stream').clientWidth;
      if (Math.abs(nw - sw) > 4) { sw = nw; drawStream(false); }
    }).observe(document.getElementById('stream'));
    const q = document.getElementById('q');
    let timer = 0;
    q.addEventListener('input', () => {
      clearTimeout(timer);
      timer = setTimeout(() => { state.q = q.value.trim(); state.limit = PAGE; if (current) window.RF.section('submissions', 'subs', () => submissions(current, names || (e => e.root || e.id))); }, 150);
    });
    let w = 0;
    new ResizeObserver(entries => {
      const nw = Math.round(entries[0].contentRect.width);
      if (current && Math.abs(nw - w) > 4) {
        w = nw;
        window.RF.section('progression', 'chart', () => chart(window.RF.records(current.subs), current, names || (e => e.root || e.id)));
      } else w = nw;
    }).observe(document.getElementById('chart'));
    start(false);
  });
})();
