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

  const STATUSES = ['record', 'retired', 'accepted', 'unranked', 'provisional', 'rejected', 'error',
    'invalid', 'queued', 'running', 'superseded', 'withdrawn'];
  const STATUS_INFO = {
    record: ['record', 'Took the record of a track (or both) when it was evaluated; it keeps this status in the history after it is beaten.'],
    retired: ['retired', 'A record that stood, then was retired by the owner in every track it held; it never stands again.'],
    accepted: ['accepted', 'Certified, comparable and attested, but not a new record: it did not beat either track\'s standing record by more than the margin, or its prover binary is an earlier record\'s.'],
    unranked: ['unranked', 'Certified, but not comparable (a truncated stream, a job plan that did not match, or no positive score).'],
    provisional: ['provisional', 'The Lean builds but the certificate does not check; benchmarked, never ranked.'],
    rejected: ['rejected', 'The certificate or the benchmark failed. The reasons say why.'],
    error: ['error', 'Waiting on the organiser: an organiser-side fault, not the entry\'s. Requeued once, then left for the owner.'],
    invalid: ['invalid', 'Failed the intake check; not evaluated.'],
    queued: ['queued', 'Waiting for the evaluator.'],
    running: ['running', 'Being evaluated now.'],
    superseded: ['superseded', 'The pull request moved before evaluation; the new head is queued instead.'],
    withdrawn: ['withdrawn', 'The pull request was closed, made a draft or put on hold before evaluation.']
  };
  const VERDICTS = ['ACCEPT', 'PROVISIONAL', 'REJECT', 'ERROR'];

  // The two tracks, scored from the one evaluation, each with its own records. `field` is the score
  // field of an older result (one without `score.tracks`, which has the sum alone); a result names
  // each track's field in `score.tracks`. Components: [field, label, unit, note].
  const TRACKS = Object.freeze([
    Object.freeze({ id: 'sum', label: 'Sum', sym: 'S', field: 'S', formula: 'S = P\u0304 + V\u0304',
      blurb: 'Prover time plus a linear charge on verifier time and proof size, in seconds per 2\u00b9\u2078 permutations.',
      parts: [['P_bar', 'P\u0304', 's'], ['V_bar', 'V\u0304', 's'], ['x_bar', 'x\u0304', '']] }),
    Object.freeze({ id: 'product', label: 'Product', sym: 'S\u00d7', field: null, formula: 'S\u00d7 = P\u0304 \u00b7 g',
      blurb: 'Prover time times a verifier factor g = 1 + (mean V / v_ref)\u00b2, in seconds per 2\u00b9\u2078 permutations; proof size is not scored (the 64 MiB file cap bounds it).',
      parts: [['P_bar', 'P\u0304', 's'], ['V_mean_s', 'mean V', 's'], ['g', 'g', ''], ['pi_mean_bytes', 'mean |\u03c0|', 'bytes', 'not scored']] })
  ]);
  const TRACK_IDS = TRACKS.map(t => t.id);
  const trackOf = id => TRACKS.find(t => t.id === id) || TRACKS[0];

  // An id is pr<N>-<12 hex of the head sha>, with -<8 hex of the pin> for a record ported to a new pin.
  const ID = 'pr[1-9]\\d{0,8}-[0-9a-f]{12}(?:-[0-9a-f]{8})?';
  const reEsc = s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const RE = {
    id: new RegExp('^' + ID + '$'),
    sha: /^[0-9a-f]{40}$/,
    root: /^[a-z][a-z0-9-]{0,39}$/,
    login: /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})(?:\[bot\])?$/,
    md: new RegExp('^(notes|readme)/' + ID + '\\.md$'),
    tag: new RegExp('^rf-source/' + ID + '$'),
    run: new RegExp('^https://github\\.com/' + reEsc(CFG.REPO) + '/actions/runs/\\d{1,20}(?:/job/\\d{1,20}|/attempts/\\d{1,4})?$'),
    key: /^[A-Za-z_][A-Za-z0-9_]{0,40}$/,
    result: new RegExp('^results/' + ID + '\\.json$'),
    track: /^[a-z][a-z0-9_]{0,15}$/
  };
  const BAD_KEYS = new Set(['__proto__', 'constructor', 'prototype', 'hasOwnProperty', 'toString', 'valueOf']);

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
    const out = Object.create(null);
    let n = 0;
    // which field is each track's score (`tracks`, written by the core), and those fields, first:
    // the cap on the number of keys below can never drop a track
    const tr = raw.tracks;
    if (tr && typeof tr === 'object' && !Array.isArray(tr)) {
      const t = Object.create(null);
      for (const [k, v] of Object.entries(tr).slice(0, 8)) {
        if (!RE.track.test(k) || typeof v !== 'string' || !RE.key.test(v) || BAD_KEYS.has(v) || v === 'tracks') continue;
        t[k] = v;
        if (typeof raw[v] === 'number' && Number.isFinite(raw[v])) out[v] = raw[v];
      }
      out.tracks = t;
    }
    for (const [k, v] of Object.entries(raw)) {
      if (n >= 60 || !RE.key.test(k) || BAD_KEYS.has(k) || k === 'tracks' || k in out) continue;
      if (typeof v === 'number' && Number.isFinite(v)) out[k] = v;
      else if (typeof v === 'boolean') out[k] = v;
      else if (typeof v === 'string' && text(v, 80)) out[k] = text(v, 80);
      else continue;
      n++;
    }
    for (const k of ['S', 'P_bar', 'V_bar']) if (typeof out[k] !== 'number' || out[k] < 0) out[k] = null;
    return (out.S === null && out.P_bar === null && out.V_bar === null && n === 0) ? null : out;
  }

  // An entry's score in a track (a positive number), or null: the field `score.tracks` names, or for a
  // score without `tracks` the sum's `S` alone.
  function scoreIn(e, track) {
    const sc = e && e.score;
    if (!sc) return null;
    const f = sc.tracks ? sc.tracks[track] : trackOf(track).id === track ? trackOf(track).field : null;
    const v = f && typeof sc[f] === 'number' ? sc[f] : null;
    return v !== null && v > 0 ? v : null;
  }

  // The comparison with the standing record as the bot records it (`against`): the record's id, this
  // entry's S, the record's own S at the pin, the gain 1 - S/S_record and whether it beat the record.
  function cleanAgainst(a) {
    if (!a || typeof a !== 'object' || typeof a.record !== 'string' || !RE.id.test(a.record)) return null;
    const s0 = num(a.S), r0 = num(a.S_record);
    const S = s0 !== null && s0 >= 0 ? s0 : null, S_record = r0 !== null && r0 > 0 ? r0 : null;
    const gain = num(a.gain) !== null ? a.gain : S !== null && S_record !== null ? 1 - S / S_record : null;
    return { record: a.record, S, S_record, gain, beats: a.beats === true };
  }

  // Per-track maps of the bot (`record_of`, `against`, `retired_in`): an object keyed by track; a file
  // of version 1 (one record, the sum's) holds the sum's value alone, not keyed.
  function perTrack(v, legacy, clean) {
    const out = Object.create(null);
    if (legacy) { const c = clean(v); if (c !== null) out.sum = c; return out; }
    if (v && typeof v === 'object' && !Array.isArray(v)) {
      for (const [k, x] of Object.entries(v).slice(0, 8)) if (RE.track.test(k)) { const c = clean(x); if (c !== null) out[k] = c; }
    }
    return out;
  }
  const idOrNull = x => typeof x === 'string' && RE.id.test(x) ? x : null;

  function cleanEntry(r, legacy) {
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
      opened: date(r.opened), queued: date(r.queued), started: date(r.started), counted_at: r.counted_at === null ? null : date(r.counted_at), has_counted: Object.prototype.hasOwnProperty.call(r, 'counted_at'), finished: date(r.finished),
      attempts: int(r.attempts),
      status: r.status,
      verdict: VERDICTS.includes(r.verdict) ? r.verdict : null,
      score: cleanScore(r.score),
      comparable: r.comparable === true, truncated: r.truncated === true,
      reasons: strList(r.reasons, 20, 300),
      run_url: typeof r.run_url === 'string' && RE.run.test(r.run_url) ? r.run_url : null,
      tag: typeof r.tag === 'string' && RE.tag.test(r.tag) ? r.tag : null,
      notes: typeof r.notes === 'string' && RE.md.test(r.notes) && r.notes.startsWith('notes/') ? r.notes : null,
      readme: typeof r.readme === 'string' && RE.md.test(r.readme) && r.readme.startsWith('readme/') ? r.readme : null,
      // the tracks whose record it took, the records it beat and the comparisons, per track
      record_in: legacy ? (['record', 'retired'].includes(r.status) ? ['sum'] : [])
        : Array.isArray(r.record_in) ? [...new Set(r.record_in.filter(t => typeof t === 'string' && RE.track.test(t)))].slice(0, 8) : [],
      retired_in: legacy ? (r.status === 'retired' ? perTrack(r.retired || r.finished, true, date) : Object.create(null)) : perTrack(r.retired_in, false, date),
      record_of: perTrack(r.record_of, legacy, idOrNull),
      against: perTrack(r.against, legacy, cleanAgainst),
      port_tracks: Array.isArray(r.port_tracks) ? r.port_tracks.filter(t => typeof t === 'string' && RE.track.test(t)).slice(0, 8) : null,
      verified: r.verified === true,
      harness_commit: typeof r.harness_commit === 'string' && RE.sha.test(r.harness_commit) ? r.harness_commit : null,
      prover_sha256: typeof r.prover_sha256 === 'string' && /^[0-9a-f]{64}$/.test(r.prover_sha256) ? r.prover_sha256 : null,
      result: typeof r.result === 'string' && RE.result.test(r.result) ? r.result : null,
      retired: date(r.retired),
      port_of: typeof r.port_of === 'string' && RE.id.test(r.port_of) ? r.port_of : null
    };
  }

  async function fetchWithTimeout(url, ms) {
    const ctl = new AbortController();
    const t = setTimeout(() => ctl.abort(), ms);
    try {
      const res = await fetch(url, { cache: 'no-cache', signal: ctl.signal, credentials: 'omit', referrerPolicy: 'no-referrer' });
      if (!res.ok) { const err = new Error('the server answered HTTP ' + res.status); err.status = res.status; throw err; }
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
      let res;
      try { res = await fetchWithTimeout(BASE + 'submissions.json', 15000); } catch (err) {
        // the branch `data` does not exist yet: nothing has been published, which is not an error
        if (err.status === 404) return { updated: null, core: await mainPin(), margin: 0.02, subs: [], skipped: 0, notShown: 0, record: noRecords(), unpublished: true };
        throw err;
      }
      const raw = await res.json().catch(() => { throw new Error('submissions.json is not valid JSON'); });
      // version 2 has a record per track; version 1 (one record, no tracks) is read as the sum's
      if (!raw || (raw.version !== 1 && raw.version !== 2) || !Array.isArray(raw.submissions)) throw new Error('submissions.json has an unknown format');
      const legacy = raw.version === 1;
      const seen = new Set();
      const subs = [];
      const CAP = 20000;
      for (const r of raw.submissions.slice(0, CAP)) {
        const e = cleanEntry(r, legacy);
        if (e && !seen.has(e.id)) { seen.add(e.id); subs.push(e); }
      }
      const margin = num(raw.margin);
      // the standing record of each track is the bot's statement (`record`), never re-derived here
      const named = legacy ? { sum: raw.record } : (raw.record && typeof raw.record === 'object' ? raw.record : {});
      const record = noRecords();
      for (const t of TRACK_IDS) {
        const id = Object.prototype.hasOwnProperty.call(named, t) ? idOrNull(named[t]) : null;
        const rec = id ? subs.find(e => e.id === id) : null;
        record[t] = rec && rec.status === 'record' && rec.record_in.includes(t) && !rec.retired_in[t] && scoreIn(rec, t) !== null && evaluatedAt(rec) ? rec : null;
      }
      return {
        updated: date(raw.updated),
        core: typeof raw.core === 'string' && RE.sha.test(raw.core) ? raw.core : null,
        margin: margin !== null && margin >= 0 && margin < 1 ? margin : 0.02,
        subs,
        skipped: Math.min(raw.submissions.length, CAP) - subs.length,
        notShown: Math.max(0, raw.submissions.length - CAP),
        record,
        // the bot's pause (organiser errors since the last completed benchmark): only its time is shown, never its reason
        paused: raw.paused && typeof raw.paused === 'object' ? { since: date(raw.paused.since) } : null
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
    for (const c of kids.flat(Infinity)) if (c !== null && c !== undefined && c !== false) n.append(c instanceof Node ? c : String(c));
    return n;
  }
  const SVGNS = 'http://www.w3.org/2000/svg';
  function svg(tag, attrs, ...kids) {
    const n = document.createElementNS(SVGNS, tag);
    if (attrs) for (const [k, v] of Object.entries(attrs)) if (v !== null && v !== undefined) n.setAttribute(k, String(v));
    for (const c of kids.flat(Infinity)) if (c !== null && c !== undefined) n.append(c instanceof Node ? c : String(c));
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
    result: e => !e.result ? null : link.resultAt(e.result),
    resultAt: path => dataKey ? BASE + path : GH + CFG.REPO + '/blob/data/' + path,
    harness: sha => GH + CFG.CORE_REPO + '/commit/' + sha,
    core: sha => GH + CFG.CORE_REPO + '/commit/' + sha,
    coreRules: GH + CFG.CORE_REPO + '/blob/main/AGENTS.md',
    guide: GH + CFG.REPO + '/blob/main/AGENTS.md',
    repo: GH + CFG.REPO,
    coreRepo: GH + CFG.CORE_REPO,
    journal: () => dataKey ? BASE + 'notes.md' : GH + CFG.REPO + '/blob/data/notes.md'
  };

  // ---- formatting --------------------------------------------------------------------------
  function fmtBytes(v) {
    if (typeof v !== 'number' || !Number.isFinite(v) || v < 0) return '\u2013';
    return v >= 1048576 ? (v / 1048576).toFixed(2) + '\u00a0MiB' : v >= 1024 ? Math.round(v / 1024) + '\u00a0KiB' : Math.round(v) + '\u00a0B';
  }
  // A component of a score in its unit: seconds, bytes, or a plain number.
  function fmtPart(v, unit) {
    if (typeof v !== 'number' || !Number.isFinite(v)) return '\u2013';
    return unit === 'bytes' ? fmtBytes(v) : unit === 's' ? fmtS(v) : (Math.abs(v) >= 100 ? v.toFixed(0) : Math.abs(v) >= 10 ? v.toFixed(1) : v.toFixed(3));
  }
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
  const noRecords = () => Object.fromEntries(TRACK_IDS.map(t => [t, null]));
  // The gain 1 - S/S_record against the track's standing record, in percent (positive = faster), or null.
  const gainOf = (e, track) => e.against[track] && e.against[track].gain !== null ? e.against[track].gain * 100 : null;
  const retiredIn = (e, track) => e.status === 'retired' || !!e.retired_in[track];
  const marginText = data => Math.round(data.margin * 1000) / 10 + '\u00a0%';
  // A verdict whose attestation did not verify is shown as such everywhere.
  const unverified = e => e.verdict && !e.verified ? el('span', { class: 'badge st-unverified', title: 'The attestation of this result did not verify; it can never be a record.' }, 'unverified') : null;
  const pct = v => typeof v !== 'number' || !Number.isFinite(v) ? '\u2013' : (v < 0 ? '\u2212' : '+') + Math.abs(v).toFixed(1) + '\u00a0%';
  const evaluatedAt = e => e.finished || e.started || e.queued || e.opened;

  // Before the bot's first write (no branch `data`), the pin comes from records.json on main.
  async function mainPin() {
    if (dataKey) return null;
    try {
      const res = await fetchWithTimeout(CFG.MAIN_BASE + 'records.json', 10000);
      const j = await res.json();
      return j && typeof j.core === 'string' && RE.sha.test(j.core) ? j.core : null;
    } catch (err) { return null; }
  }

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
    const headOf = n => {
      const list = byPr.get(n);
      if (!list) return null;
      return list.find(e => !['superseded', 'withdrawn', 'queued', 'running'].includes(e.status)) || list[0];
    };
    // A citation is listed from a pull request whose newest head is evaluated or waiting (not
    // invalid, superseded or withdrawn), once per citing PR. It counts only if that head has a
    // verdict (ACCEPT, PROVISIONAL or REJECT; not an organiser error) and is by another author:
    // `self` and `pending` mark the citations that are listed but not counted.
    const citedBy = new Map();
    for (const [pr, list] of byPr) {
      const newest = list.slice().sort((a, b) => (b.queued || b.opened || 0) - (a.queued || a.opened || 0))[0];
      if (!newest || ['invalid', 'superseded', 'withdrawn'].includes(newest.status)) continue;
      const pending = !['ACCEPT', 'PROVISIONAL', 'REJECT'].includes(newest.verdict) || ['queued', 'running', 'error'].includes(newest.status);
      for (const n of newest.builds_on) {
        const cited = headOf(n);
        if (!cited) continue;
        if (!citedBy.has(n)) citedBy.set(n, []);
        citedBy.get(n).push({ pr, self: !!cited.author && cited.author === newest.author, pending });
      }
    }
    const citeCount = n => (citedBy.get(n) || []).filter(c => !c.self && !c.pending).length;
    return { byId, byPr, citedBy, citeCount, headOf };
  }

  // Every record ever taken in a track (`record` or `retired`, the track in `record_in`), oldest
  // first; entries without a score in the track or a date are left out rather than allowed to break a page.
  function records(subs, track) {
    return subs.filter(e => (e.status === 'record' || e.status === 'retired') && e.record_in.includes(track) && scoreIn(e, track) !== null && evaluatedAt(e))
      .sort((a, b) => evaluatedAt(a) - evaluatedAt(b));
  }

  // The selected track: `?track=`, else the viewer's last choice (localStorage, which may be
  // unavailable), else the sum.
  const TRACK_KEY = 'rf-track';
  function chosenTrack() {
    const q = params.get('track');
    if (q && TRACK_IDS.includes(q)) return q;
    try { const v = window.localStorage.getItem(TRACK_KEY); if (v && TRACK_IDS.includes(v)) return v; } catch (e) { /* storage blocked */ }
    return TRACK_IDS[0];
  }
  function rememberTrack(id) {
    try { window.localStorage.setItem(TRACK_KEY, id); } catch (e) { /* storage blocked */ }
    try {
      const p = new URLSearchParams(location.search);
      p.set('track', id);
      history.replaceState(null, '', location.pathname + '?' + p.toString() + location.hash);
    } catch (e) { /* history unavailable */ }
  }

  // A root name that two authors use is shown with its pull request, so it cannot pass as the other.
  function nameOf(subs) {
    const authors = new Map();
    for (const e of subs) if (e.root) {
      if (!authors.has(e.root)) authors.set(e.root, new Set());
      authors.get(e.root).add(e.author);
    }
    return e => !e.root ? e.id : authors.get(e.root).size > 1 ? `${e.root} (#${e.pr})` : e.root;
  }

  // Runs one section's render; a failure shows a message in that section only.
  function section(name, target, fn) {
    try { fn(); } catch (err) {
      const box = typeof target === 'string' ? document.getElementById(target) : target;
      if (box) {
        const msg = el('p', { class: 'section-error', role: 'alert' }, `This section could not be shown (${name}): the data has an unexpected shape.`);
        if (box.tagName === 'TBODY') box.replaceChildren(el('tr', { class: 'empty-row' }, el('td', { colspan: 9 }, msg)));
        else if (box.tagName === 'OL' || box.tagName === 'UL') box.replaceChildren(el('li', { class: 'empty-li' }, msg));
        else box.replaceChildren(msg);
      }
      if (window.console) console.warn('recursion.fast: ' + name + ': ' + (err && err.message));
    }
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
    CFG, BASE, dataKey, STATUSES, STATUS_INFO, RE, TRACKS, TRACK_IDS, trackOf, scoreIn, retiredIn, chosenTrack, rememberTrack,
    loadData, loadText, el, svg, ext, page, link, fmtS, fmtPart, fmtBytes, fmtDate, fmtDateTime, timeEl, ago, badge,
    shortSha, gainOf, marginText, pct, unverified, evaluatedAt, relations, records, nameOf, section, chrome, footer
  };
  document.addEventListener('DOMContentLoaded', chrome);
})();
