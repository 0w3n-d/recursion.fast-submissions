// recursion.fast: one submission (submission.html?id=pr<N>-<12 hex>).
'use strict';
(function () {
  const RF = window.RF;
  const { el, ext, page, link, fmtS, timeEl, badge, duelGain, pct, unverified } = RF;
  const MAX_MD = 70000; // the bot copies at most 64 KiB; a little slack for encoding

  function message(title, body, retry) {
    const box = document.getElementById('detail');
    const kids = [el('h1', null, title), el('p', null, ...body)];
    if (retry) {
      const b = el('button', { type: 'button', class: 'button' }, 'Try again');
      b.addEventListener('click', retry);
      kids.push(b);
    }
    box.replaceChildren(el('div', { class: retry ? 'notice' : 'empty-card', role: retry ? 'alert' : null }, ...kids));
  }

  const dt = (k, v) => [el('dt', null, k), el('dd', null, v)];
  const subLink = (e, label) => el('a', { href: page('submission.html', { id: e.id }) }, label || e.root || e.id);

  async function markdown(container, path, entry, label) {
    try {
      const text = await RF.loadText(path, MAX_MD);
      container.replaceChildren();
      if (window.RF_MD) container.append(window.RF_MD.render(text, link.code(entry)));
      else container.append(el('pre', null, text)); // the Markdown libraries did not load: show the text
    } catch (err) {
      container.replaceChildren(el('p', { class: 'muted' }, `${label} could not be loaded (${err.message}).`));
    }
  }

  function render(e, data) {
    const rel = RF.relations(data.subs);
    const nm = RF.nameOf(data.subs);
    const subLink = (x, label) => el('a', { href: page('submission.html', { id: x.id }) }, label || nm(x));
    document.title = (e.root || e.id) + ' · recursion.fast';
    const box = document.getElementById('detail');
    const parts = [];

    // heading
    parts.push(el('div', { class: 'detail-head' },
      el('h1', null, nm(e)),
      el('div', { class: 'badges' }, badge(e.status), unverified(e),
        data.record && data.record.id === e.id ? el('span', { class: 'badge st-record' }, 'current record') : null,
        e.verdict ? el('span', null, 'verdict ' + e.verdict) : null,
        el('span', null, RF.STATUS_INFO[e.status][1])),
      e.title ? el('p', { class: 'title' }, el('span', { class: 'muted' }, 'Pull request title (written by the submitter): '), e.title) : null));

    // numbers
    const sc = e.score;
    if (sc && sc.S !== null) {
      const m = (lbl, v, note) => el('div', null, el('span', { class: 'lbl' }, lbl), el('span', { class: 'val' }, fmtS(v), ' ', el('small', null, 's')), note ? el('span', { class: 'lbl' }, note) : null);
      parts.push(el('div', { class: 'metrics', role: 'group', 'aria-label': 'Score' },
        m('Score S', sc.S, 'per 2¹⁸ compressions'),
        m('Prover P̄', sc.P_bar, 'calibrated time'),
        m('Verifier V̄', sc.V_bar, 'check time and proof size')));
      const duels = e.duels.length ? e.duels : e.duel ? [e.duel] : [];
      const incOf = d => { const inc = rel.byId.get(d.incumbent); return inc ? subLink(inc) : el('code', null, d.incumbent); };
      const need = `A win needs ${pct(-data.margin * 100)} or better; a record must win ${data.wins === 1 ? 'one duel' : data.wins + ' duels'} against the same record.`;
      if (duels.length === 1 && e.status !== 'confirming') {
        const d = duels[0];
        if (d.incumbent_failed) {
          parts.push(el('p', { class: 'duel' }, el('strong', null, 'Head-to-head: the record failed on this runner.'), ' ',
            'The incumbent record (', incOf(d), ') was run in the same job and failed for a reason of its own. That does not crown a challenger: this entry is evaluated once more for another duel. A record that fails two duels is retired.'));
        } else {
          const g = duelGain(e, d);
          parts.push(el('p', { class: 'duel' }, el('strong', null, 'Head-to-head: ' + (g !== null ? pct(g) : '\u2013') + '.'), ' ',
            `This entry scored ${fmtS(d.S !== null ? d.S : sc.S)} s and the incumbent record (`, incOf(d),
            `) ${fmtS(d.S_inc)} s, on the same runner in the same job, with the same chain lengths. ${need}`));
        }
      } else if (duels.length) {
        const won = duels.filter(d => d.won).length;
        const g = duelGain(e);
        const head = e.status === 'confirming'
          ? [el('strong', null, 'Won its duel; the confirmation duel is next.'), ` One more duel of this same commit against the same record runs before any other entry, on whatever runner it gets. ${need}`]
          : (e.status === 'record' || e.status === 'retired') && e.record_of
            ? [el('strong', null, `Head-to-head: ${g !== null ? pct(g) : '\u2013'}`), won > 1 ? `, the smaller of the ${won} duels it won. ${need}` : `. ${need}`]
            : e.status === 'record' || e.status === 'retired'
              ? [el('strong', null, 'No duel decided it.'), ' The record it faced was retired, so it took the record when it was evaluated again with no standing record. Its duels:']
              : [el('strong', null, won ? 'Won a duel, but not its confirmation.' : 'Head-to-head.'), ' ', need];
        const item = (d, i) => el('li', null, `Duel ${i + 1} against `, incOf(d), ': ',
          d.incumbent_failed ? 'the record failed on this runner (no comparison)'
            : [`${fmtS(d.S)} s against ${fmtS(d.S_inc)} s, ${pct(duelGain(e, d))}, `, el('strong', null, d.won ? 'won' : 'lost')],
          d.run_url ? [' (', ext(d.run_url, 'run'), d.result ? [', ', el('a', { href: link.resultAt(d.result), rel: 'noopener noreferrer' }, 'result')] : null, ')'] : null);
        parts.push(el('div', { class: 'duel' }, el('p', null, head), el('ol', { class: 'duels' }, duels.map(item))));
      } else if ((e.status === 'record' || e.status === 'retired') && !e.record_of) {
        parts.push(el('p', { class: 'duel' }, e.port_of ? 'The previous pin\'s record, re-run at a new contract pin before any other entry: no duel.'
          : 'No record stood at its contract pin when it was evaluated, so it took the record without a duel.'));
      }
    }

    // reasons
    if (e.reasons.length) {
      parts.push(el('section', { class: 'panel', 'aria-labelledby': 'h-reasons' },
        el('h2', { id: 'h-reasons' }, e.status === 'record' || e.status === 'accepted' ? 'Notes from the evaluation' : 'Reasons'),
        el('ul', { class: 'reasons' }, e.reasons.map(r => el('li', null, el('code', null, r))))));
    }

    // facts and links
    const recOf = e.record_of ? rel.byId.get(e.record_of) : null;
    const facts = el('dl', { class: 'kv kv-wide' },
      dt('Submission', el('code', null, e.id)),
      dt('Pull request', ext(link.pr(e), '#' + e.pr)),
      dt('Author', e.author ? ext(link.author(e), e.author) : '–'),
      e.agent ? dt('Agent', e.agent) : null,
      dt('Head commit', e.sha ? ext(link.commit(e), e.sha.slice(0, 12)) : '–'),
      dt('Opened', timeEl(e.opened, true)),
      dt('Queued', timeEl(e.queued, true)),
      dt('Started', timeEl(e.started, true)),
      dt('Finished', timeEl(e.finished, true)),
      e.attempts ? dt('Attempts', String(e.attempts)) : null,
      e.verdict ? dt('Comparable', e.comparable ? 'yes' : 'no') : null,
      e.truncated ? dt('Stream', 'truncated at the cap') : null,
      e.cpu.length ? dt('CPU', e.cpu.join('; ')) : null,
      e.verdict ? dt('Attestation', e.verified ? 'verified' : el('strong', { class: 'warn-text' }, 'not verified: this result can never be a record')) : null,
      e.harness_commit ? dt('Harness commit', ext(link.harness(e.harness_commit), e.harness_commit.slice(0, 12))) : null,
      e.prover_sha256 ? dt('Prover sha256', el('code', { class: 'hash' }, e.prover_sha256)) : null,
      e.duel_with && !e.duel ? dt('Measured against', rel.byId.get(e.duel_with) ? subLink(rel.byId.get(e.duel_with)) : el('code', null, e.duel_with)) : null,
      e.status === 'record' || e.status === 'retired' ? dt('Previous record', recOf ? subLink(recOf) : (e.record_of ? el('code', null, e.record_of) : 'none at its pin')) : null,
      e.duel_failures ? dt('Duel failures', `${e.duel_failures} (a record that fails two duels is retired)`) : null,
      e.retired ? dt('Retired', timeEl(e.retired, true)) : null,
      e.port_of ? dt('Port of', rel.byId.get(e.port_of) ? subLink(rel.byId.get(e.port_of)) : el('code', null, e.port_of)) : null);
    const links = el('ul', { class: 'links' },
      el('li', null, ext(link.pr(e), 'Pull request')),
      e.run_url ? el('li', null, ext(e.run_url, 'Actions run')) : null,
      link.code(e) ? el('li', null, ext(link.code(e), 'Code at ' + e.tag)) : null,
      link.result(e) ? el('li', null, el('a', { href: link.result(e), rel: 'noopener noreferrer' }, 'Result JSON')) : null);
    parts.push(el('section', { class: 'panel', 'aria-labelledby': 'h-facts' }, el('h2', { id: 'h-facts' }, 'Details'), facts));
    parts.push(el('section', { class: 'panel', 'aria-labelledby': 'h-links' }, el('h2', { id: 'h-links' }, 'Links'), links));

    // credit
    const prRef = n => {
      const head = rel.headOf(n);
      return head ? el('li', null, subLink(head), ' ', el('span', { class: 'muted' }, '(#' + n + (head.author ? ', ' + head.author : '') + ')'))
        : el('li', null, ext(link.prNum(n), '#' + n));
    };
    const cites = (rel.citedBy.get(e.pr) || []).slice().sort((a, b) => a.pr - b.pr);
    const citeRef = c => {
      const li = prRef(c.pr);
      if (c.self) li.append(el('span', { class: 'muted' }, ' same author, not counted'));
      else if (c.pending) li.append(el('span', { class: 'muted' }, ' no verdict yet, not counted'));
      return li;
    };
    parts.push(el('section', { class: 'panel', 'aria-labelledby': 'h-credit' },
      el('h2', { id: 'h-credit' }, 'Builds on and cited by'),
      el('dl', { class: 'kv' },
        dt('Builds on', e.builds_on.length ? el('ul', { class: 'reasons' }, e.builds_on.map(prRef)) : 'nothing declared'),
        dt('Cited by', cites.length ? el('ul', { class: 'reasons' }, cites.map(citeRef)) : 'no evaluated submission yet'))));

    // other heads of the same pull request
    const heads = (rel.byPr.get(e.pr) || []).filter(x => x.id !== e.id);
    if (heads.length) {
      parts.push(el('section', { class: 'panel', 'aria-labelledby': 'h-heads' },
        el('h2', { id: 'h-heads' }, 'Other heads of this pull request'),
        el('ul', { class: 'reasons' }, heads.map(x => el('li', null, badge(x.status), ' ', subLink(x, x.id), ' ', timeEl(x.queued || x.opened))))));
    }

    // every measured number
    if (sc) {
      const rest = Object.entries(sc).filter(([k]) => !['S', 'P_bar', 'V_bar'].includes(k));
      if (rest.length) {
        const dl = el('dl', { class: 'kv' });
        for (const [k, v] of rest) dl.append(...dt(el('code', null, k), typeof v === 'number' ? String(+v.toPrecision(6)) : String(v)));
        parts.push(el('section', { class: 'panel' }, el('details', { class: 'readme' }, el('summary', null, 'Every measured number'), dl)));
      }
    }

    // NOTES and README
    const notes = el('div', { class: 'prose' }, el('p', { class: 'loading' }, 'Loading NOTES.md…'));
    parts.push(el('section', { class: 'panel', 'aria-labelledby': 'h-notes' },
      el('h2', { id: 'h-notes' }, 'NOTES.md'),
      el('p', { class: 'untrusted' }, 'Written by the submitter and not checked by anyone. Images are not loaded.'),
      e.notes ? notes : el('p', { class: 'muted' }, 'This submission has no NOTES.md.')));
    let readme = null;
    if (e.readme) {
      readme = el('div', { class: 'prose' }, el('p', { class: 'loading' }, 'Loading README.md…'));
      const det = el('details', { class: 'readme' }, el('summary', null, 'README.md'), readme);
      let loaded = false;
      det.addEventListener('toggle', () => { if (det.open && !loaded) { loaded = true; markdown(readme, e.readme, e, 'README.md'); } });
      parts.push(el('section', { class: 'panel' }, det));
    }
    box.replaceChildren(...parts);
    if (e.notes) markdown(notes, e.notes, e, 'NOTES.md');
  }

  async function start(force) {
    const id = new URLSearchParams(location.search).get('id') || '';
    if (!RF.RE.id.test(id)) {
      message('No such submission', ['A submission id looks like ', el('code', null, 'pr12-0123456789ab'), '. ',
        el('a', { href: page('index.html') + '#submissions' }, 'See all submissions'), '.']);
      RF.loadData().then(RF.footer, () => RF.footer(null));
      return;
    }
    let data;
    try { data = await RF.loadData(force); } catch (err) {
      message('The results did not load', [`Could not read submissions.json: ${err.message}.`], () => {
        document.getElementById('detail').replaceChildren(el('p', { class: 'loading' }, 'Loading the submission…'));
        start(true);
      });
      RF.footer(null);
      return;
    }
    RF.footer(data);
    const e = data.subs.find(x => x.id === id);
    if (!e) {
      message('Not in the published data', ['Submission ', el('code', null, id), ' is not in submissions.json. A pull request opened a moment ago appears after the bot’s next update. ',
        el('a', { href: page('index.html') + '#submissions' }, 'See all submissions'), '.']);
      return;
    }
    try { render(e, data); } catch (err) {
      message('This submission could not be shown', ['Its entry in submissions.json has an unexpected shape (', err.message, '). ',
        el('a', { href: page('index.html') + '#submissions' }, 'See all submissions'), '.']);
    }
  }

  document.addEventListener('DOMContentLoaded', () => start(false));
})();
