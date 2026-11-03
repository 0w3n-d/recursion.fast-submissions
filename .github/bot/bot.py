#!/usr/bin/env python3
"""The bot's command line, for the workflows (TRUSTED; Python 3 standard library only).

  python3 -I .github/bot/bot.py intake  --pr N
  python3 -I .github/bot/bot.py select  [--pr N]            outputs id, sha, path, pr, ref (or nothing)
  python3 -I .github/bot/bot.py publish --id ID [--result result/result.json] [--core core]
  python3 -I .github/bot/bot.py sync-main

Environment: GITHUB_TOKEN, GITHUB_REPOSITORY, GITHUB_RUN_ID, GITHUB_SERVER_URL, GITHUB_API_URL and
GITHUB_OUTPUT (set by Actions); RF_CHECKOUT, the checkout of `main` this code and the pin come from
(default: the repository holding this file). The pin is read from that checkout (`pin.py`) and must
agree in its three places, or nothing runs."""
import argparse
import base64
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import attest  # noqa: E402
import flows  # noqa: E402
import pin as pinmod  # noqa: E402
from common import ID_RE  # noqa: E402
from gh import GitHub  # noqa: E402


def output(**kv):
    path = os.environ.get("GITHUB_OUTPUT")
    lines = "".join(f"{k}={v}\n" for k, v in kv.items() if "\n" not in str(v) and "\r" not in str(v))
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write(lines)
    else:
        sys.stdout.write(lines)


def make_ctx(core_dir=None):
    env = os.environ
    checkout = env.get("RF_CHECKOUT") or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    pin, problems = pinmod.read(checkout)
    if not pin:
        sys.exit("bot: the pin is inconsistent: " + "; ".join(problems))
    token, repo = env["GITHUB_TOKEN"], env["GITHUB_REPOSITORY"]
    server = env.get("GITHUB_SERVER_URL", "https://github.com")
    b64 = base64.b64encode(f"x-access-token:{token}".encode()).decode()
    print(f"::add-mask::{b64}")
    run_id = env.get("GITHUB_RUN_ID", "0")
    return flows.Ctx(GitHub(token, repo, env.get("GITHUB_API_URL", "https://api.github.com")), repo,
                     f"{server}/{repo}.git", pin, token=token, run_id=run_id, server=server,
                     verify=lambda path, result: attest.verify(path, result, repo, run_id, core_dir))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["intake", "select", "publish", "sync-main", "record-build"])
    ap.add_argument("--dir", default="")
    ap.add_argument("--pr", default="")
    ap.add_argument("--id", default="")
    ap.add_argument("--result", default="")
    ap.add_argument("--core", default=None)
    a = ap.parse_args()
    pr = None
    if a.pr.strip():
        if not a.pr.strip().isdigit() or not 0 < int(a.pr) < 10 ** 9:
            sys.exit(f"bot: --pr must be a pull-request number, not {a.pr[:40]!r}")
        pr = int(a.pr)
    ctx = make_ctx(a.core)
    if a.cmd == "intake":
        if pr is None:
            sys.exit("bot: intake needs --pr")
        print(f"intake: #{pr}: {flows.intake(ctx, pr)}")
    elif a.cmd == "select":
        e = flows.select(ctx, pr)
        if e:
            print(f"select: {e['id']} (#{e['pr']}, {e['root']}, attempt {e['attempts']})")
            output(id=e["id"], sha=e["sha"], path=f"submissions/{e['root']}", pr=e["pr"], ref=f"refs/tags/{e['tag']}",
                   record_cache="true" if e.get("record_cache", True) else "false")
            inc = e.get("incumbent")
            if inc:   # the standing record, re-run in the same job (brief §2a)
                output(incumbent_id=inc["id"], incumbent_sha=inc["sha"], incumbent_path=f"submissions/{inc['root']}",
                       incumbent_ref=f"refs/tags/{inc['tag']}")
    elif a.cmd == "publish":
        if not ID_RE.match(a.id):
            sys.exit(f"bot: --id must be an entry id, not {a.id[:40]!r}")
        e = flows.publish(ctx, a.id, a.result or None)
        if e:
            print(f"publish: {e['id']}: {e['status']} ({e.get('verdict')})")
            output(status=e["status"], record="true" if e["status"] == "record" else "false")
    elif a.cmd == "record-build":
        if not ID_RE.match(a.id):
            sys.exit("bot: --id must be an entry id")
        _, result = flows.load_result(a.result)
        key = flows.record_build(ctx, result, a.dir, ctx.pin, a.id)
        output(key=key or "")
    elif a.cmd == "sync-main":
        st = flows.rfqueue.load(ctx.git().snapshot(flows.DATA).read("submissions.json"), ctx.repo, ctx.pin)
        print(f"sync-main: {flows.sync_main(ctx, st)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
