// recursion.fast site configuration. Edit these values to deploy elsewhere.
//
// DATA_BASE is where the bot's branch `data` is served from (raw files, trailing slash), and
// MAIN_BASE the branch `main` (its records.json names the pin before `data` exists). If you change
// their origin, also change `connect-src` in the Content-Security-Policy <meta> of every *.html
// file, or the browser will refuse the fetch.
//
// The query string can only switch to the bundled fixtures below (same origin); it can never
// point the site at an arbitrary URL.
'use strict';
window.RF_CONFIG = Object.freeze({
  REPO: 'scaraven/recursion.fast-submissions',
  CORE_REPO: 'scaraven/recursion.fast',
  DATA_BASE: 'https://raw.githubusercontent.com/scaraven/recursion.fast-submissions/data/',
  MAIN_BASE: 'https://raw.githubusercontent.com/scaraven/recursion.fast-submissions/main/',
  // ?data=<key> selects one of these fixtures instead of DATA_BASE.
  FIXTURES: Object.freeze({ 'demo': 'demo/', 'demo-empty': 'demo/empty/' })
});
