"""Rule 4's bypass and false-reject shapes, verbatim: `cases` = [(name, VIOLATION | fine, workflow text)].
KNOWN_BYPASS and KNOWN_FALSE_REJECT are accepted: wfcheck is an advisory lint (the hard guarantee is the
server's job-started hook), and the false rejects need the allowlist extended when a workflow needs them."""
PRT = "on:\n  pull_request_target:\n"
CO = "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1"
T = "${{ github.event.pull_request.title }}"
VIOLATION, FINE = "VIOLATION", "fine"
J = "jobs:\n  a:\n    runs-on: rf-light\n"


def job(env=None, steps="", extra=""):
    s = PRT + "jobs:\n  a:\n    runs-on: rf-light\n" + extra
    if env:
        s += "    env:\n" + "".join(f"      {k}: {v}\n" for k, v in env.items())
    return s + "    steps:\n" + steps


cases = [
    # --- laundering PR data through an allowed atom back into run:/with: ---
    ("env.X in run (job env from PR title)", VIOLATION,
     job({"T": T}, "      - run: echo \"${{ env.T }}\"\n")),
    ("env.X in run (step env from PR title)", VIOLATION,
     job(None, "      - env:\n          T: " + T + "\n        run: echo \"${{ env.T }}\"\n")),
    ("GITHUB_ENV written from $T, then env.X in a later run", VIOLATION,
     job({"T": T}, "      - run: echo \"U=$T\" >> \"$GITHUB_ENV\"\n      - run: echo \"${{ env.U }}\"\n")),
    ("steps.X.outputs.Y in run (output written from $T)", VIOLATION,
     job({"T": T}, "      - id: s\n        run: echo \"t=$T\" >> \"$GITHUB_OUTPUT\"\n      - run: echo \"${{ steps.s.outputs.t }}\"\n")),
    ("needs.X.outputs.Y in run (job output from a PR-fed step)", VIOLATION,
     PRT + "jobs:\n  a:\n    runs-on: rf-light\n    outputs:\n      t: ${{ steps.s.outputs.t }}\n    env:\n      T: " + T +
     "\n    steps:\n      - id: s\n        run: echo \"t=$T\" >> \"$GITHUB_OUTPUT\"\n"
     "  b:\n    needs: a\n    runs-on: rf-light\n    steps:\n      - run: echo \"${{ needs.a.outputs.t }}\"\n"),
    ("env.X into github-script's script input", VIOLATION,
     job({"T": T}, "      - uses: actions/github-script@0000000000000000000000000000000000000000\n        with:\n          script: ${{ env.T }}\n")),
    ("checkout of the own repository at a step output derived from head.sha", VIOLATION,
     job({"H": "${{ github.event.pull_request.head.sha }}"},
         "      - id: s\n        run: echo \"sha=$H\" >> \"$GITHUB_OUTPUT\"\n"
         f"      - uses: {CO}\n        with:\n          repository: scaraven/recursion.fast-submissions\n          ref: ${{{{ steps.s.outputs.sha }}}}\n          path: x\n      - run: ./x/run.sh\n")),
    # --- the PR picks where / in what the job runs ---
    ("runs-on from the PR title under pull_request_target", VIOLATION,
     PRT + "jobs:\n  a:\n    runs-on: " + T + "\n    steps:\n      - run: echo hi\n"),
    ("runs-on from head_ref under pull_request_target", VIOLATION,
     PRT + "jobs:\n  a:\n    runs-on: ${{ github.head_ref }}\n    steps:\n      - run: echo hi\n"),
    ("container image from the PR title", VIOLATION,
     PRT + "jobs:\n  a:\n    runs-on: ubuntu-latest\n    container:\n      image: " + T + "\n    steps:\n      - run: echo hi\n"),
    ("container (string form) from the PR title", VIOLATION,
     PRT + "jobs:\n  a:\n    runs-on: ubuntu-latest\n    container: " + T + "\n    steps:\n      - run: echo hi\n"),
    ("services image from the PR title", VIOLATION,
     PRT + "jobs:\n  a:\n    runs-on: ubuntu-latest\n    services:\n      db:\n        image: " + T + "\n    steps:\n      - run: echo hi\n"),
    ("step shell from env (PR title)", VIOLATION,
     job({"T": T}, "      - shell: ${{ env.T }}\n        run: echo hi\n")),
    ("job defaults.run.shell from the PR title", VIOLATION,
     PRT + "jobs:\n  a:\n    runs-on: rf-light\n    defaults:\n      run:\n        shell: " + T + "\n    steps:\n      - run: echo hi\n"),
    ("working-directory from env", VIOLATION,
     job({"T": T}, "      - working-directory: ${{ env.T }}\n        run: ./x\n")),
    ("strategy.matrix from fromJSON(PR body), matrix.x in run", VIOLATION,
     PRT + "jobs:\n  a:\n    runs-on: rf-light\n    strategy:\n      matrix: ${{ fromJSON(github.event.pull_request.body) }}\n    steps:\n      - run: echo ${{ matrix.x }}\n"),
    # --- hiding `${{` from the YAML subset ---
    ("double-quoted \\x24 escape hides ${{ in run", VIOLATION,
     job(None, "      - run: \"echo \\x24{{ github.event.pull_request.title }}\"\n")),
    ("double-quoted \\u0024 escape hides ${{ in run", VIOLATION,
     job(None, "      - run: \"echo \\u0024{{ github.event.pull_request.title }}\"\n")),
    ("double-quoted \\u007b escapes hide the braces", VIOLATION,
     job(None, "      - run: \"echo $\\u007b\\u007b github.event.pull_request.title }}\"\n")),
    ("double-quoted escape in with: ref", VIOLATION,
     job(None, f"      - uses: {CO}\n        with:\n          ref: \"\\x24{{{{ github.event.pull_request.head.sha }}}}\"\n")),
    ("${{ split across lines in a | block", VIOLATION,
     job(None, "      - run: |\n          echo \"${{\n          github.event.pull_request.title }}\"\n")),
    ("${{ split across lines in a > block", VIOLATION,
     job(None, "      - run: >\n          echo \"${{\n          github.event.pull_request.title\n          }}\"\n")),
    ("expression with a tab inside", VIOLATION,
     job(None, "      - run: echo \"${{\tgithub.event.pull_request.title }}\"\n")),
    # --- functions, nesting, operators (all must be refused) ---
    ("toJSON(github.event.pull_request)", VIOLATION, job(None, "      - run: echo '${{ toJSON(github.event.pull_request) }}'\n")),
    ("format('{0}', title)", VIOLATION, job(None, "      - run: echo \"${{ format('{0}', github.event.pull_request.title) }}\"\n")),
    ("fromJSON(body).x", VIOLATION, job(None, "      - run: echo \"${{ fromJSON(github.event.pull_request.body).x }}\"\n")),
    ("contains(title, 'x') && title", VIOLATION, job(None, "      - run: echo \"${{ contains(github.event.pull_request.title, 'x') && github.event.pull_request.title }}\"\n")),
    ("title || github.sha", VIOLATION, job(None, "      - run: echo \"${{ github.event.pull_request.title || github.sha }}\"\n")),
    ("github.sha == title", VIOLATION, job(None, "      - run: echo \"${{ github.sha == github.event.pull_request.title }}\"\n")),
    ("parenthesised", VIOLATION, job(None, "      - run: echo \"${{ (github.event.pull_request.title) }}\"\n")),
    ("github.event.pull_request.title in with: of an action", VIOLATION,
     job(None, "      - uses: some/action@0000000000000000000000000000000000000000\n        with:\n          x: " + T + "\n")),
    ("github.event in env with index syntax", VIOLATION, job({"T": "${{ github.event['pull_request']['title'] }}"}, "      - run: echo \"$T\"\n")),
    ("github['token'] in run", VIOLATION, job(None, "      - run: echo ${{ github['token'] }}\n")),
    ("env.X in a job-level with of a reusable workflow under workflow_dispatch", VIOLATION,
     "on: workflow_dispatch\njobs:\n  a:\n    uses: ./.github/workflows/x.yml\n    with:\n      r: ${{ github.event.inputs.r }}\n"),
    ("reusable under issue_comment with needs output and secrets inherit", VIOLATION,
     "on: issue_comment\njobs:\n  a:\n    runs-on: ubuntu-latest\n    outputs:\n      t: ${{ steps.s.outputs.t }}\n    steps:\n      - id: s\n        run: echo t=x >> $GITHUB_OUTPUT\n"
     "  b:\n    needs: a\n    uses: ./.github/workflows/x.yml\n    with:\n      r: ${{ needs.a.outputs.t }}\n    secrets: inherit\n"),
    # --- run: text that executes fetched code past RUN_CODE_RE ---
    ("git \\ newline checkout", VIOLATION, job({"N": "${{ github.event.number }}"}, "      - run: |\n          git fetch origin refs/pull/$N/head\n          git \\\n            checkout FETCH_HEAD\n          ./x\n")),
    ("git pull", VIOLATION, job({"N": "${{ github.event.number }}"}, "      - run: git pull origin refs/pull/$N/head && ./x\n")),
    ("git show FETCH_HEAD:x | bash", VIOLATION, job({"N": "${{ github.event.number }}"}, "      - run: git fetch origin refs/pull/$N/head && git show FETCH_HEAD:x.sh | bash\n")),
    ("git cat-file | sh", VIOLATION, job({"N": "${{ github.event.number }}"}, "      - run: git fetch origin refs/pull/$N/head && git cat-file -p FETCH_HEAD:x.sh | sh\n")),
    ("$g checkout via a variable", VIOLATION, job({"N": "${{ github.event.number }}"}, "      - run: g=git; $g fetch origin refs/pull/$N/head; $g checkout FETCH_HEAD; ./x\n")),
    ("git -C with --work-tree reset", VIOLATION, job({"N": "${{ github.event.number }}"}, "      - run: git fetch origin refs/pull/$N/head && git --work-tree=w reset --hard FETCH_HEAD && ./w/x\n")),
    ("gh pr diff | patch", VIOLATION, job({"N": "${{ github.event.number }}"}, "      - run: gh pr diff $N | patch -p1 && ./x\n")),
    ("curl raw fork file | bash", VIOLATION, job({"R": "${{ github.event.pull_request.head.repo.full_name }}", "S": "${{ github.event.pull_request.head.sha }}"},
                                                 "      - run: curl -sL https://raw.githubusercontent.com/$R/$S/x.sh | bash\n")),
    ("gh api contents | base64 -d | bash", VIOLATION, job({"S": "${{ github.event.pull_request.head.sha }}"},
                                                          "      - run: gh api repos/$GITHUB_REPOSITORY/contents/x.sh?ref=$S -q .content | base64 -d | bash\n")),
    ("GITHUB_EVENT_PATH read and eval'd", VIOLATION, job(None, "      - run: eval \"$(jq -r .pull_request.title \"$GITHUB_EVENT_PATH\")\"\n")),
    ("GITHUB_EVENT_PATH read as data", FINE, job(None, "      - run: jq -r .pull_request.number \"$GITHUB_EVENT_PATH\"\n")),
    ("git fetch of refs/pull as data (intake style)", FINE, job({"N": "${{ github.event.number }}"}, "      - run: git init -q --bare pr.git && git --git-dir pr.git fetch -q origin refs/pull/$N/head && git --git-dir pr.git ls-tree FETCH_HEAD\n")),
    # --- shapes that should stay allowed (false rejects) ---
    ("intake-style: base checkout, PR number via env", FINE,
     job(None, f"      - uses: {CO}\n        with:\n          ref: ${{{{ github.sha }}}}\n          path: bot-src\n      - env:\n          PR: ${{{{ github.event.pull_request.number || inputs.pr }}}}\n        run: python3 -I bot-src/bot.py --pr \"$PR\"\n")),
    ("pin-check pr job guarded to pull_request: base.sha checkout", FINE,
     "on: [pull_request, push]\njobs:\n  pr:\n    if: github.event_name == 'pull_request'\n    runs-on: ubuntu-24.04\n    steps:\n"
     f"      - uses: {CO}\n        with:\n          ref: ${{{{ github.event.pull_request.base.sha }}}}\n"),
    ("checkout with a literal 40-hex ref of a fixed repository", FINE,
     "on: workflow_dispatch\njobs:\n  a:\n    runs-on: rf-light\n    steps:\n" + f"      - uses: {CO}\n        with:\n          repository: scaraven/recursion.fast\n          ref: 0000000000000000000000000000000000000000\n          path: core\n"),
    ("github.actor in env (a plausible organiser need)", FINE,
     job({"WHO": "${{ github.actor }}"}, "      - run: echo \"$WHO\"\n")),
    ("github.event.issue.number in env under issue_comment", FINE,
     "on: issue_comment\njobs:\n  a:\n    runs-on: ubuntu-latest\n    env:\n      N: ${{ github.event.issue.number }}\n    steps:\n      - run: echo \"$N\"\n"),
    ("vars.X in env", FINE, job({"V": "${{ vars.SEASON }}"}, "      - run: echo \"$V\"\n")),
    ("secrets.OTHER in env under workflow_dispatch", FINE,
     "on: workflow_dispatch\njobs:\n  a:\n    runs-on: rf-light\n    env:\n      K: ${{ secrets.DEPLOY }}\n    steps:\n      - run: echo \"$K\"\n"),
    ("step if: with a PR field (boolean only)", FINE,
     job(None, "      - if: contains(github.event.pull_request.labels.*.name, 'hold')\n        run: echo held\n")),
    ("concurrency group with a PR field", FINE,
     PRT + "concurrency:\n  group: intake-${{ github.event.pull_request.number }}\njobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - run: echo hi\n"),
    ("job name with a PR field", FINE,
     PRT + "jobs:\n  a:\n    name: intake ${{ github.event.pull_request.number }}\n    runs-on: rf-light\n    steps:\n      - run: echo hi\n"),
]

KNOWN_BYPASS = {"$g checkout via a variable"}
KNOWN_FALSE_REJECT = {"github.actor in env (a plausible organiser need)", "github.event.issue.number in env under issue_comment",
                      "vars.X in env", "secrets.OTHER in env under workflow_dispatch"}
