"""A thin GitHub REST client on urllib with the job's GITHUB_TOKEN (TRUSTED). The tests and the
simulation replace it with a fake of the same interface (`tests/fakes.py`)."""
import json
import time
import urllib.error
import urllib.parse
import urllib.request

from common import STATUS_CONTEXT


class GHError(Exception):
    def __init__(self, status, msg):
        super().__init__(f"GitHub API {status}: {msg}")
        self.status = status


class GitHub:
    def __init__(self, token, repo, api="https://api.github.com"):
        self.token, self.repo, self.api = token, repo, api.rstrip("/")

    def _req(self, method, path, body=None, tries=3):
        url = path if path.startswith("https://") else f"{self.api}/{path.lstrip('/')}"
        if not url.startswith(self.api + "/"):
            raise GHError(0, "refusing a URL outside the API")
        data = None if body is None else json.dumps(body).encode()
        for k in range(tries):
            req = urllib.request.Request(url, data=data, method=method, headers={
                "Authorization": f"Bearer {self.token}", "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "recursion-fast-bot"})
            try:
                with urllib.request.urlopen(req, timeout=60) as r:
                    raw = r.read(32 << 20)
                    return (json.loads(raw) if raw else None), r.headers.get("Link", "")
            except urllib.error.HTTPError as e:
                if e.code in (500, 502, 503, 504) and k + 1 < tries:
                    time.sleep(5 * (k + 1))
                    continue
                raise GHError(e.code, e.read(2000).decode("utf-8", "replace")) from None
            except urllib.error.URLError as e:
                if k + 1 < tries:
                    time.sleep(5 * (k + 1))
                    continue
                raise GHError(0, str(e)) from None

    def _repo(self, rest):
        return f"repos/{self.repo}/{rest}"

    def pr(self, n):
        return self._req("GET", self._repo(f"pulls/{int(n)}"))[0]

    def pr_files(self, n, limit=3000):
        """The changed files ({filename, previous_filename?, status}), at most `limit` (the API's
        own cap is 3000); None if there are more."""
        out, url = [], self._repo(f"pulls/{int(n)}/files?per_page=100")
        while url:
            page, link = self._req("GET", url)
            out += page
            if len(out) > limit:
                return None
            url = next((p.split(";")[0].strip(" <>") for p in link.split(",") if 'rel="next"' in p), None)
        return out

    def permission(self, login):
        """The user's permission on this repository: admin, write, read or none."""
        try:
            r = self._req("GET", self._repo(f"collaborators/{urllib.parse.quote(login)}/permission"))[0]
        except GHError as e:
            if e.status == 404:
                return "none"
            raise
        return r.get("permission") or "none"

    def comment(self, n, body):
        self._req("POST", self._repo(f"issues/{int(n)}/comments"), {"body": body})

    def issue(self, title, body):
        """An owner-facing notice (a new issue)."""
        self._req("POST", self._repo("issues"), {"title": title, "body": body})

    def set_status(self, sha, state, description, target_url=None):
        body = {"state": state, "context": STATUS_CONTEXT, "description": description[:140]}
        if target_url:
            body["target_url"] = target_url
        self._req("POST", self._repo(f"statuses/{sha}"), body)

    def dispatch(self, workflow, ref, inputs=None):
        self._req("POST", self._repo(f"actions/workflows/{workflow}/dispatches"),
                  {"ref": ref, "inputs": inputs or {}})

    def caches(self, prefix):
        """The Actions caches whose key starts with `prefix`."""
        out, url = [], self._repo(f"actions/caches?per_page=100&key={urllib.parse.quote(prefix)}")
        while url:
            page, link = self._req("GET", url)
            out += (page or {}).get("actions_caches", [])
            url = next((p.split(";")[0].strip(" <>") for p in link.split(",") if 'rel="next"' in p), None)
        return out

    def delete_cache(self, key):
        self._req("DELETE", self._repo(f"actions/caches?key={urllib.parse.quote(key)}"))

    def statuses(self, sha):
        """The commit statuses of `sha` (newest first; the first 100 suffice for the bot's context)."""
        return self._req("GET", self._repo(f"commits/{sha}/statuses?per_page=100"))[0] or []

    def open_prs(self):
        """Every open pull request (the list payload: number, head, base, user, draft, labels)."""
        out, url = [], self._repo("pulls?state=open&per_page=100")
        while url:
            page, link = self._req("GET", url)
            out += page or []
            url = next((p.split(";")[0].strip(" <>") for p in link.split(",") if 'rel="next"' in p), None)
        return out
