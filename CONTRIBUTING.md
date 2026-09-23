# Contributing

Set up the environment with `nix develop`; see the root [README.md](README.md#install)'s Install
section for the supported path, [docs/installation.md](docs/installation.md) for the step-by-step
version, and [docs/setup-without-nix.md](docs/setup-without-nix.md) for a machine without Nix.

For the development loop -- the fast pre-check, the full gate, when to run each refresh script,
approvals and certificate regeneration -- see [docs/development.md](docs/development.md). For
what each CI workflow runs and certifies, see [docs/ci.md](docs/ci.md). For adding a new
protocol-scoped unit to `framed_channel`, see
[framed_channel/docs/adding-a-unit.md](framed_channel/docs/adding-a-unit.md).

Two standing constraints apply to every contribution:

- Every tracked source and script file carries an SPDX license header; the gate's SPDX stage
  (`framed_channel/scripts/check-spdx.sh`, exercised by
  `framed_channel/tests/spdx/run.sh`) enforces this.
- Never reference a locally-ignored working directory from a tracked file. Private working
  material lives outside the shipped tree and is excluded through both the tracked `.gitignore`
  and the untracked `.git/info/exclude` -- never name either file's private entries in a tracked
  file.
- This repository is public: set a repo-local (never `--global`) GitHub-provided noreply author
  address once per clone, `git config user.email "<id>+<user>@users.noreply.github.com"`, and
  confirm it after your next commit with `git log -1 --format='%ae %ce'`.

## Navigation

- [docs/README.md](docs/README.md)
- [README.md](README.md)
