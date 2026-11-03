// recursion.fast: shared code for every page. Data written by the bot is fetched at load time and
// validated here; every string in it (titles, agents, reasons, notes) is attacker-written, so the
// pages build DOM nodes with textContent only. The one exception is sanitised Markdown (render.js).
'use strict';
(function () {
  const CFG = window.RF_CONFIG;
  const params = new URLSearchParams(location.search);
  const rawKey = params.get('data');
  const dataKey = rawKey && Object.prototype.hasOwnProperty.call(CFG.FIXTURES, rawKey) ? rawKey : null;
  const BASE = dataKey ? CFG.FIXTURES[dataKey] : CFG.DATA_BASE;

  const STATUSES = ['record', 'accepted', 'unranked', 'provisional', 'rejected', 'error', 'invalid',
    'queued', 'running', 'superseded', 'withdrawn'];
  const STATUS_INFO = {
    record: ['record', 'Became the record when it was evaluated.'],
    accepted: ['accepted', 'Certified and comparable, but did not beat the record by the margin.'],
    unranked: ['unranked', 'Certified, but not comparable (a truncated stream or mixed CPU models).'],
    provisional: ['provisional', 'The Lean builds but the certificate does not check; benchmarked, never ranked.'],
    rejected: ['rejected', 'The certificate or the benchmark failed. The reasons say why.'],
    error: ['error', 'An organiser-side fault, not the entry\'s. Requeued once, then left for the owner.'],
    invalid: ['invalid', 'Failed the intake check; not evaluated.'],
    queued: ['queued', 'Waiting for the evaluator.'],
    running: ['running', 'Being evaluated now.'],
    superseded: ['superseded', 'The pull request moved before evaluation; the new head is queued instead.'],
    withdrawn: ['withdrawn', 'The pull request was closed before evaluation.']
  };
  const VERDICTS = ['ACCEPT', 'PROVISIONAL', 'REJECT', 'ERROR'];

  const RE = {
    id: /^pr\d{1,7}-[0-9a-f]{12}$/,
    sha: /^[0-9a-f]{40}$/,
    root: /^[a-z][a-z0-9-]{0,39}$/,
    login: /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/,
    md: /^(notes|readme)\/pr\d{1,7}-[0-9a-f]{12}\.md$/,
    tag: /^rf-source\/pr\d{1,7}-[0-9a-f]{12}$/,
    run: /^https:\/\/github\.com\/[A-Za-z0-9-]{1,39}\/[A-Za-z0-9._-]{1,100}\/actions\/runs\/\d{1,20}(?:\/job\/\d{1,20}|\/attempts\/\d{1,4})?$/,
    key: /^[A-Za-z_][A-Za-z0-9_]{0,40}$/,
    result: /^results\/pr\d{1,7}-[0-9a-f]{12}\.json$/
  };

  // Plain text only: no control characters, no bidirectional overrides (they can disguise text).
  function text(v, max) {
    if (typeof v !== 'string') return null;
    const s = v.replace(/[\u0000-\u0008\u000b-\u001f\u007f-\u009f‎‏‪-‮⁦-⁩]/g, '')
      .replace(/\s+/g, ' ').trim();
    if (!s) return null;
    return s.length > max ? s.slice(0, max - 1) + '…' : s;
  }
  const num = v => (typeof v === 'number' && Number.isFinite(v)) ? v : null;
  const date = v => (typeof v === 'string' && v.length <= 40 && Number.isFinite(Date.parse(v))) ? new Date(v) : null;
  const int = v => (Number.isSafeInteger(v) && v >= 0) ? v : null;

  function cleanScore(raw) {
    if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return null;
    const out = {};
    let n = 0;
    for (const [k, v] of Object.entries(raw)) {
      if (n >= 60 || !RE.key.test(k)) continue;
      if (typeof v === 'number' && Number.isFinite(v)) out[k] = v;
      else if (typeof v === 'boolean') out[k] = v;
      else if (typeof v === 'string' && text(v, 80)) out[k] = text(v, 80);
      else continue;
      n++;
    }
    for (const k of ['S', 'P_bar', 'V_bar']) if (typeof out[k] !== 'number' || out[k] < 0) out[k] = null;
    return (out.S === null && out.P_bar === null && out.V_bar === null && n === 0) ? null : out;
  }

  // The head-to-head duel the bot records (BRIEF §2a): the incumbent record's id, its S in the
  // same job, the gain 1 - S/S_inc, and whether the incumbent failed on that runner.
  function cleanDuel(d) {
    if (!d || typeof d !== 'object' || typeof d.incumbent !== 'string' || !RE.id.test(d.incumbent)) return null;
    const sInc = num(d.S_inc), gain = num(d.gain);
    return { incumbent: d.incumbent, S_inc: sInc !== null && sInc > 0 ? sInc : null, gain, incumbent_failed: d.incumbent_failed === true };
  }

  function cleanEntry(r) {
    if (!r || typeof r !== 'object') return null;
    if (typeof r.id !== 'string' || !RE.id.test(r.id)) return null;
    if (!STATUSES.includes(r.status)) return null;
    const pr = int(r.pr);
    if (pr === null || pr < 1 || r.id.split('-')[0] !== 'pr' + pr) return null;
    const root = typeof r.root === 'string' && RE.root.test(r.root) ? r.root : null;
    const author = typeof r.author === 'string' && RE.login.test(r.author) ? r.author : null;
    const sha = typeof r.sha === 'string' && RE.sha.test(r.sha) ? r.sha : null;
    const builds = Array.isArray(r.builds_on)
      ? [...new Set(r.builds_on.filter(x => Number.isSafeInteger(x) && x > 0 && x !== pr))].slice(0, 20) : [];
    const strList = (a, n, max) => Array.isArray(a) ? a.map(x => text(x, max)).filter(Boolean).slice(0, n) : [];
    return {
      id: r.id, pr, sha, root, author, builds_on: builds,
      title: text(r.title, 200),
      agent: text(r.agent, 160),
      opened: date(r.opened), queued: date(r.queued), started: date(r.started), finished: date(r.finished),
      attempts: int(r.attempts),
      status: r.status,
      verdict: VERDICTS.includes(r.verdict) ? r.verdict : null,
      score: cleanScore(r.score),
      comparable: r.comparable === true, truncated: r.truncated === true,
      reasons: strList(r.reasons, 20, 300),
      cpu: strList(r.cpu, 8, 120),
      run_url: typeof r.run_url === 'string' && RE.run.test(r.run_url) ? r.run_url : null,
      tag: typeof r.tag === 'string' && RE.tag.test(r.tag) ? r.tag : null,
      notes: typeof r.notes === 'string' && RE.md.test(r.notes) && r.notes.startsWith('notes/') ? r.notes : null,
      readme: typeof r.readme === 'string' && RE.md.test(r.readme) && r.readme.startsWith('readme/') ? r.readme : null,
      record_of: typeof r.record_of === 'string' && RE.id.test(r.record_of) ? r.record_of : null,
      duel: cleanDuel(r.duel),
      duel_with: typeof r.duel_with === 'string' && RE.id.test(r.duel_with) ? r.duel_with : null,
      verified: r.verified === true,
      harness_commit: typeof r.harness_commit === 'string' && RE.sha.test(r.harness_commit) ? r.harness_commit : null,
      prover_sha256: typeof r.prover_sha256 === 'string' && /^[0-9a-f]{64}$/.test(r.prover_sha256) ? r.prover_sha256 : null,
      result: typeof r.result === 'string' && RE.result.test(r.result) ? r.result : null
    };
  }

  async function fetchWithTimeout(url, ms) {
    const ctl = new AbortController();
    const t = setTimeout(() => ctl.abort(), ms);
    try {
      const res = await fetch(url, { cache: 'no-cache', signal: ctl.signal, credentials: 'omit', referrerPolicy: 'no-referrer' });
      if (!res.ok) throw new Error('the server answered HTTP ' + res.status);
      return res;
    } catch (e) {
      if (e.name === 'AbortError') throw new Error('the request timed out');
      throw e;
    } finally { clearTimeout(t); }
  }

  let dataPromise = null;
  function loadData(force) {
    if (dataPromise && !force) return dataPromise;
    dataPromise = (async () => {
      const res = await fetchWithTimeout(BASE + 'submissions.json', 15000);
      const raw = await res.json().catch(() => { throw new Error('submissions.json is not valid JSON'); });
      if (!raw || raw.version !== 1 || !Array.isArray(raw.submissions)) throw new Error('submissions.json has an unknown format');
      const seen = new Set();
      const subs = [];
      for (const r of raw.submissions.slice(0, 20000)) {
        const e = cleanEntry(r);
        if (e && !seen.has(e.id)) { seen.add(e.id); subs.push(e); }
      }
      const margin = num(raw.margin);
      return {
        updated: date(raw.updated),
        core: typeof raw.core === 'string' && RE.sha.test(raw.core) ? raw.core : null,
        margin: margin !== null && margin >= 0 && margin < 1 ? margin : 0.03,
        subs,
        skipped: raw.submissions.length - subs.length
      };
    })();
    dataPromise.catch(() => { dataPromise = null; });
    return dataPromise;
  }

  async function loadText(path, maxBytes) {
    if (!RE.md.test(path) && path !== 'notes.md') throw new Error('bad path');
    const res = await fetchWithTimeout(BASE + path, 15000);
    const t = await res.text();
    return t.length > maxBytes ? t.slice(0, maxBytes) + '\n\n*(truncated by the site)*\n' : t;
  }

  // ---- DOM helpers -------------------------------------------------------------------------
  function el(tag, attrs, ...kids) {
    const n = document.createElement(tag);
    if (attrs) for (const [k, v] of Object.entries(attrs)) {
      if (v === null || v === undefined || v === false) continue;
      if (k === 'text') n.textContent = v;
      else if (k === 'class') n.className = v;
      else if (k === 'href') { if (safeHref(v)) n.setAttribute('href', v); }
      else n.setAttribute(k, v === true ? '' : String(v));
    }
    for (const c of kids.flat()) if (c !== null && c !== undefined && c !== false) n.append(c instanceof Node ? c : String(c));
    return n;
  }
  const SVGNS = 'http://www.w3.org/2000/svg';
  function svg(tag, attrs, ...kids) {
    const n = document.createElementNS(SVGNS, tag);
    if (attrs) for (const [k, v] of Object.entries(attrs)) if (v !== null && v !== undefined) n.setAttribute(k, String(v));
    for (const c of kids.flat()) if (c !== null && c !== undefined) n.append(c instanceof Node ? c : String(c));
    return n;
  }
  // Links built by the site are https GitHub URLs or same-origin pages; nothing else.
  function safeHref(v) {
    return typeof v === 'string' && (/^https:\/\/(github\.com|raw\.githubusercontent\.com)\//.test(v) ||
      /^[a-z0-9-]+\.(html|txt|md)(\?[^\s"'<>]*)?(#[\w-]*)?$/.test(v) || /^#[\w-]+$/.test(v) || /^demo\/[\w./-]+$/.test(v));
  }
  function ext(href, label) {
    return el('a', { href, rel: 'noopener noreferrer' }, label);
  }

  // A link to one of the site's own pages, keeping the fixture choice.
  function page(name, extra) {
    const p = new URLSearchParams(extra || {});
    if (dataKey) p.set('data', dataKey);
    const q = p.toString();
    return name + (q ? '?' + q : '');
  }

  // ---- links into GitHub -------------------------------------------------------------------
  const GH = 'https://github.com/';
  const link = {
    pr: e => GH + CFG.REPO + '/pull/' + e.pr,
    prNum: n => GH + CFG.REPO + '/pull/' + n,
    author: e => e.author ? GH + e.author : null,
    commit: e => e.sha ? GH + CFG.REPO + '/commit/' + e.sha : null,
    code: e => e.tag && e.root && e.status !== 'invalid' ? GH + CFG.REPO + '/tree/' + e.tag + '/submissions/' + e.root : null,
    result: e => !e.result ? null : dataKey ? BASE + e.result : GH + CFG.REPO + '/blob/data/' + e.result,
    harness: sha => GH + CFG.CORE_REPO + '/commit/' + sha,
    core: sha => GH + CFG.CORE_REPO + '/commit/' + sha,
    coreRules: GH + CFG.CORE_REPO + '/blob/main/AGENTS.md',
    guide: GH + CFG.REPO + '/blob/main/AGENTS.md',
    repo: GH + CFG.REPO,
    coreRepo: GH + CFG.CORE_REPO,
    journal: () => dataKey ? BASE + 'notes.md' : GH + CFG.REPO + '/blob/data/notes.md'
  };

  // ---- formatting --------------------------------------------------------------------------
  function fmtS(v) {
    if (v === null || v === undefined) return '–';
    const a = Math.abs(v);
    return a >= 100 ? v.toFixed(1) : a >= 10 ? v.toFixed(2) : v.toFixed(3);
  }
  const pad = n => String(n).padStart(2, '0');
  function fmtDate(d) { return d ? d.getUTCFullYear() + '-' + pad(d.getUTCMonth() + 1) + '-' + pad(d.getUTCDate()) : '–'; }
  function fmtDateTime(d) { return d ? fmtDate(d) + ' ' + pad(d.getUTCHours()) + ':' + pad(d.getUTCMinutes()) + ' UTC' : '–'; }
  function timeEl(d, withTime) {
    if (!d) return document.createTextNode('–');
    return el('time', { datetime: d.toISOString(), title: d.toISOString() }, withTime ? fmtDateTime(d) : fmtDate(d));
  }
  function ago(d) {
    if (!d) return '';
    const s = Math.max(0, (Date.now() - d.getTime()) / 1000);
    if (s < 90) return 'just now';
    if (s < 5400) return Math.round(s / 60) + ' min ago';
    if (s < 129600) return Math.round(s / 3600) + ' h ago';
    return Math.round(s / 86400) + ' days ago';
  }
  function badge(status) {
    const [label, desc] = STATUS_INFO[status] || [status, ''];
    return el('span', { class: 'badge st-' + status, title: desc }, label);
  }
  const shortSha = s => s ? s.slice(0, 7) : '';
  // Head-to-head change of S against the incumbent in the same job, in percent (negative = faster).
  const duelGain = e => {
    const d = e.duel;
    if (!d || d.incumbent_failed) return null;
    if (d.S_inc && e.score && e.score.S !== null) return (e.score.S - d.S_inc) / d.S_inc * 100;
    return d.gain !== null ? -d.gain * 100 : null;
  };
  // A verdict whose attestation did not verify is shown as such everywhere.
  const unverified = e => e.verdict && !e.verified ? el('span', { class: 'badge st-unverified', title: 'The attestation of this result did not verify; it can never be a record.' }, 'unverified') : null;
  const pct = v => (v < 0 ? '\u2212' : '+') + Math.abs(v).toFixed(1) + '\u00a0%';
  const evaluatedAt = e => e.finished || e.started || e.queued || e.opened;

  // ---- relations ---------------------------------------------------------------------------
  // builds_on names pull requests; a PR may have several heads (ids). Credit goes to the PR, and
  // links go to its most recent evaluated head.
  function relations(subs) {
    const byId = new Map(subs.map(e => [e.id, e]));
    const byPr = new Map();
    for (const e of subs) {
      if (!byPr.has(e.pr)) byPr.set(e.pr, []);
      byPr.get(e.pr).push(e);
    }
    for (const list of byPr.values()) list.sort((a, b) => (evaluatedAt(b) || 0) - (evaluatedAt(a) || 0));
    const citedBy = new Map();
    for (const e of subs) for (const n of e.builds_on) {
      if (!citedBy.has(n)) citedBy.set(n, new Set());
      citedBy.get(n).add(e.pr);
    }
    const headOf = n => {
      const list = byPr.get(n);
      if (!list) return null;
      return list.find(e => !['superseded', 'withdrawn', 'queued', 'running'].includes(e.status)) || list[0];
    };
    return { byId, byPr, citedBy, headOf };
  }

  function records(subs) {
    return subs.filter(e => e.status === 'record' && e.score && e.score.S !== null)
      .sort((a, b) => (evaluatedAt(a) || 0) - (evaluatedAt(b) || 0));
  }

  // ---- page chrome -------------------------------------------------------------------------
  function chrome() {
    if (dataKey) {
      const b = el('p', { class: 'demo-banner', role: 'note' },
        dataKey === 'demo' ? 'Demo data: every submission on this page is fictional.' : 'Demo data: an empty dataset, as on launch day.');
      document.body.prepend(b);
    }
    for (const a of document.querySelectorAll('a[data-page]')) {
      const [name, hash] = a.getAttribute('data-page').split('#');
      a.setAttribute('href', page(name) + (hash ? '#' + hash : ''));
    }
    for (const a of document.querySelectorAll('a[data-link]')) {
      const k = a.getAttribute('data-link');
      const v = typeof link[k] === 'function' ? link[k]() : link[k];
      if (v) a.setAttribute('href', v);
    }
    // pages without their own script still show the contract pin in the footer
    if (document.body.hasAttribute('data-static')) loadData().then(footer, () => footer(null));
  }

  function footer(data) {
    const slot = document.getElementById('pin');
    if (!slot) return;
    slot.replaceChildren();
    if (data && data.core) {
      slot.append('Contract pin ', ext(link.core(data.core), shortSha(data.core)));
    } else {
      slot.append('Contract pin unavailable');
    }
    const up = document.getElementById('updated');
    if (up && data && data.updated) up.replaceChildren('Data updated ', timeEl(data.updated, true));
  }

  window.RF = {
    CFG, BASE, dataKey, STATUSES, STATUS_INFO, RE,
    loadData, loadText, el, svg, ext, page, link, fmtS, fmtDate, fmtDateTime, timeEl, ago, badge,
    shortSha, duelGain, pct, unverified, evaluatedAt, relations, records, chrome, footer
  };
  document.addEventListener('DOMContentLoaded', chrome);
})();
