// recursion.fast: Markdown from submitters (NOTES.md, README.md), rendered safely.
//
// The policy:
// - raw HTML in the Markdown is shown as text, never parsed (marked's html renderer escapes it);
// - images are never loaded (no tracking pixels, no remote fetches): each becomes a plain link
//   labelled with its alt text, and only if its URL is https;
// - links keep only https:// and in-page #anchors; a relative link resolves to the entry's code at
//   its retention tag on github.com; every link gets rel="noopener noreferrer nofollow ugc";
// - DOMPurify then removes everything outside a small allowlist of tags and attributes;
// - headings are shifted down two levels so a note cannot fake the page's own outline.
'use strict';
(function () {
  if (!window.marked || !window.DOMPurify) return; // submission.js then shows the text as it is
  const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
  // an https URL with a host and no user name or password (https://github.com@evil.example/ reads as GitHub)
  const isHttps = u => {
    if (!/^https:\/\/[^\s/]+/i.test(u || '')) return false;
    try { const x = new URL(u); return x.protocol === 'https:' && !x.username && !x.password; } catch (e) { return false; }
  };
  // bidirectional overrides and marks reorder rendered text; they never reach the page
  const BIDI = /[\u200e\u200f\u202a-\u202e\u2066-\u2069]/g;

  const md = new window.marked.Marked({
    gfm: true,
    breaks: false,
    renderer: {
      html(token) { return esc(token.text || token.raw || ''); },
      image(token) {
        const alt = token.text || 'image';
        return isHttps(token.href) ? `<a href="${esc(token.href)}">[image: ${esc(alt)}]</a>` : esc('[image: ' + alt + ']');
      }
    }
  });

  const ALLOWED_TAGS = ['p', 'br', 'hr', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'ul', 'ol', 'li', 'blockquote', 'pre', 'code',
    'em', 'strong', 'del', 's', 'a', 'table', 'thead', 'tbody', 'tr', 'th', 'td', 'sup', 'sub'];
  const ALLOWED_ATTR = ['href', 'title', 'start', 'align', 'colspan', 'rowspan'];

  let codeBase = null;
  const purify = window.DOMPurify;
  purify.addHook('uponSanitizeAttribute', (node, data) => {
    if (data.attrName !== 'href') return;
    const v = (data.attrValue || '').trim();
    if (isHttps(v) || /^#[\w-]{1,80}$/.test(v)) return;
    // relative link inside the entry: resolve it on github.com at the entry's retention tag
    if (codeBase && /^[\w./-]{1,200}(#[\w-]{0,80})?$/.test(v) && !v.startsWith('/') && !v.startsWith('//')) {
      try {
        const u = new URL(v, codeBase + '/');
        if (u.href.startsWith(codeBase + '/')) { data.attrValue = u.href; return; } // never above the entry's root
      } catch (e) { /* fall through */ }
    }
    data.keepAttr = false;
  });
  purify.addHook('afterSanitizeAttributes', node => {
    if (node.tagName === 'A') {
      if (node.hasAttribute('href') && !node.getAttribute('href').startsWith('#')) node.setAttribute('rel', 'noopener noreferrer nofollow ugc');
    }
  });

  // Markdown text -> a DocumentFragment that is safe to insert.
  function render(text, base) {
    codeBase = base || null;
    // keep the header lines (Agent:, Builds on:, ...) on their own lines
    const src = String(text).replace(BIDI, '').replace(/^((?:[A-Z][A-Za-z -]{1,30}:[^\n]*\n)+)/, h => h.replace(/\n/g, '  \n'));
    const html = md.parse(src, { async: false });
    const frag = purify.sanitize(html, {
      ALLOWED_TAGS, ALLOWED_ATTR, ALLOW_DATA_ATTR: false, ALLOW_ARIA_ATTR: false,
      ALLOWED_URI_REGEXP: /^(?:https:|#)/i, RETURN_DOM_FRAGMENT: true
    });
    codeBase = null;
    for (const h of frag.querySelectorAll('h1, h2, h3, h4, h5, h6')) {
      const n = document.createElement('h' + Math.min(6, Number(h.tagName[1]) + 2));
      n.append(...h.childNodes);
      h.replaceWith(n);
    }
    // a link that leaves github.com shows where it goes, so a note cannot label it as something else
    for (const a of frag.querySelectorAll('a[href]')) {
      try {
        const u = new URL(a.getAttribute('href'));
        if (u.hostname !== 'github.com') {
          const h = document.createElement('span');
          h.className = 'ext-host';
          h.textContent = ' (' + u.hostname + ')';
          a.after(h);
        }
      } catch (e) { /* in-page anchor */ }
    }
    for (const t of frag.querySelectorAll('table')) {
      const w = document.createElement('div');
      w.className = 'table-scroll';
      t.replaceWith(w);
      w.append(t);
    }
    return frag;
  }

  window.RF_MD = { render };
})();
