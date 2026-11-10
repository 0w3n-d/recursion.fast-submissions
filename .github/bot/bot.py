#!/usr/bin/env python3
"""The bot's command line, for the workflows (TRUSTED; Python 3 standard library only).

  python3 -I .github/bot/bot.py intake  --pr N [--force]    prechecks and admits a head (no `data` write)
  python3 -I .github/bot/bot.py sync                        the single writer of new queue entries
  python3 -I .github/bot/bot.py select  [--pr N] [--retire ID --track T] [--resume true]
                                    outputs id, sha, path, ref, record_cache, record_manifest_sha256 (or nothing)
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
from common import ID_RE, TRACK_RE  # noqa: E402
from gh import GitHub  # noqa: E402


def output(**kv):
    path = os.environ.get("GITHUB_OUTPUT")
    for k, v in kv.items():
        if "\n" in str(v) or "\r" in str(v):
            raise SystemExit(f"bot: output {k} holds a line break")      # never a silently missing output
    lines = "".join(f"{k}={v}\n" for k, v in kv.items())
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
                     f"{server}/{repo}.git", pin, token=token, run_id=run_id,
                     run_attempt=int(env.get("GITHUB_RUN_ATTEMPT", "1") or 1), server=server,
                     verify=lambda path, result, min_attempt: attest.verify(path, result, repo, run_id, core_dir,
                                                                            min_attempt=min_attempt))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["intake", "sync", "select", "publish", "sync-main", "record-build"])
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--retire", default="")
    ap.add_argument("--track", default="")
    ap.add_argument("--resume", default="")
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
        try:
            print(f"intake: #{pr}: {flows.intake(ctx, pr, a.force)}")
        except Exception:
            flows.intake_failed(ctx, pr)
            raise
    elif a.cmd == "sync":
        flows.sync(ctx)
    elif a.cmd == "select":
        if a.retire and not ID_RE.match(a.retire):
            sys.exit("bot: --retire must be an entry id")
        if a.retire and not TRACK_RE.match(a.track):
            sys.exit("bot: --retire needs --track, the track of the record to retire (sum or product)")
        if a.resume not in ("", "true", "false"):
            sys.exit("bot: --resume must be true or false")
        e = flows.select(ctx, pr, a.retire or None, a.resume == "true", (a.track if a.retire else None))
        if e:
            print(f"select: {e['id']} (#{e['pr']}, {e['root']}, attempt {e['attempts']})")
            output(id=e["id"], sha=e["sha"], path=f"submissions/{e['root']}", ref=f"refs/tags/{e['tag']}",
                   record_cache="true" if e.get("record_cache", True) else "false",
                   record_manifest_sha256=e.get("record_manifest") or "")
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
        st = flows._state(ctx, ctx.git().snapshot(flows.DATA))
        print(f"sync-main: {flows.sync_main(ctx, st)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
