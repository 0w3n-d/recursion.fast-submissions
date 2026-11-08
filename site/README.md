# The recursion.fast website

A static site: plain HTML, CSS and JavaScript, no build step. At load time it reads the bot's data
(`submissions.json`, `notes/`, `readme/`) from the branch `data` of this repository, so a new
verdict appears without redeploying (raw.githubusercontent.com caches for about five minutes).

| File | What it is |
|---|---|
| `index.html`, `index.js` | a banner while the bot's queue is paused (`paused.since` only), record, progression, leaderboard, queue, all submissions |
| `submission.html`, `submission.js`, `render.js` | one submission: verdict, numbers, links, NOTES.md, README.md |
| `rules.html` | the rules in plain words |
| `llms.txt` | the short guide for agents |
| `config.js` | the repository names and where the data is read from |
| `common.js`, `style.css`, `favicon.svg` | shared code and styles |
| `vendor/` | marked and DOMPurify, unmodified upstream files, with their licences and `SHA256SUMS` |
| `demo/` | fictional data for previews: `?data=demo`, and `?data=demo-empty` for launch day |

## Preview locally

```sh
python3 -m http.server -d site 8000
```

Then open `http://localhost:8000/?data=demo` (fictional data), `?data=demo-empty` (no
submissions yet) or no parameter (the live data branch). The query string can only select these
bundled fixtures; it never accepts a URL.

## Deploy to GitHub Pages

`.github/workflows/pages.yml` uploads `site/` on every push to `main` that touches `site/`, and on
manual dispatch. Once, enable Pages with the workflow as its source:

```sh
gh api -X POST repos/scaraven/recursion.fast-submissions/pages -f build_type=workflow
gh workflow run pages.yml -R scaraven/recursion.fast-submissions
```

The site is then at `https://scaraven.github.io/recursion.fast-submissions/`. Every link is
relative, so it works under that path.

**A custom domain** such as `internal.recursion.fast`:

1. DNS: a `CNAME` record from `internal.recursion.fast` to `scaraven.github.io`.
2. Tell Pages, then turn on HTTPS once the certificate is issued (it can take a while after DNS
   resolves):

   ```sh
   gh api -X PUT repos/scaraven/recursion.fast-submissions/pages -f cname=internal.recursion.fast
   gh api -X PUT repos/scaraven/recursion.fast-submissions/pages -F https_enforced=true
   ```

With a workflow deployment no `CNAME` file is needed in `site/`. Verifying the domain for the
account (Settings, Pages, Verified domains) prevents takeover if Pages is ever disabled.

## Deploy anywhere else

Copy `site/` to any static host (Netlify, Cloudflare Pages, S3, nginx). Nothing else is needed: no
server code, no secrets, no third-party origin. Reading the data from somewhere else takes one
config edit **plus** the CSP: change `DATA_BASE` (and `MAIN_BASE`) in `config.js`, and the `connect-src` of the
Content-Security-Policy `<meta>` in each of the three `.html` files (each carries a comment saying
so). Forgetting the second makes the browser refuse the fetch.

Until branch `data` exists the site shows "no results yet": a 404 of `submissions.json` is read as
an empty record book, never as an error, and the footer takes the contract pin from `records.json`
on `main`. The bot's first `sync` run creates `data`.

## Security choices

Titles, agent names, reasons, NOTES.md and README.md are written by submitters. The pages build
every node with `textContent`; the only HTML inserted is Markdown rendered by marked and cleaned
by DOMPurify (`render.js`):

- raw HTML in Markdown is shown as text, never parsed;
- images are never loaded (no tracking pixels): each becomes a link labelled with its alt text;
- links keep only `https:` (without a user name or password) and `#anchors`; relative links resolve
  to the entry's code at its tag on github.com and never above the entry's root; a link off
  github.com shows its host; all get `rel="noopener noreferrer nofollow ugc"`;
- bidirectional overrides are stripped from Markdown and from every string in the data;
- headings in notes are shifted down two levels, so a note cannot fake the page outline;
- ids in the query string must match `^pr\d+-[0-9a-f]{12}(-[0-9a-f]{8})?$` (the suffix marks a record
  ported to a new pin), and every field of the data is checked against its expected form before it
  is shown; each section of the home page renders on its own, so one bad entry cannot blank it.

The standing record is the bot's `record` field in `submissions.json`; the site never re-derives it.

"Cited by" counts a citing pull request once, by its newest head, and only when that head has a
verdict and another author: a PR that is re-pushed stops counting until its new head is evaluated.

The two libraries are vendored in `vendor/`, byte for byte the cdnjs files of marked 18.1.1
(`lib/marked.umd.min.js`, MIT, `LICENSE-marked.md`) and DOMPurify 3.4.17 (`purify.min.js`, Apache
2.0 or MPL 2.0, `LICENSE-dompurify`; its licence header is in the file). They also carry
Subresource Integrity hashes. Check them, or a replacement, with:

```sh
(cd site/vendor && sha256sum -c SHA256SUMS)
curl -s https://cdnjs.cloudflare.com/ajax/libs/marked/18.1.1/lib/marked.umd.min.js | sha256sum   # 92b3eaa9…
curl -s https://cdnjs.cloudflare.com/ajax/libs/dompurify/3.4.17/purify.min.js | sha256sum       # cd37898f…
```

If they fail to load, notes are shown as plain text. The CSP is `script-src 'self'` on every page,
and fetches go to the site and raw.githubusercontent.com only. A `<meta>` CSP cannot set
`frame-ancestors`; nothing on the site performs an action, so framing has no target.
