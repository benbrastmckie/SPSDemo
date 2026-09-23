# docs/

Installation, development and CI documentation for this example.

- [installation.md](installation.md) -- installing step by step: prerequisites, what
  `install.sh` and `nix develop` do and do not do, the `install.sh` flags and every dev shell.
- [consuming.md](consuming.md) -- what is actually here, what you can run, and what should not be
  treated as fixed.
- [trust-model.md](trust-model.md) -- what a green badge, a green `full-gate.sh` run and a valid
  certificate do and do not certify, per platform.
- [ci.md](ci.md) -- the CI workflows: triggers and path filters, jobs, what each badge
  certifies, the platform matrix, runner images, cache strategy, timeouts, and the repository
  settings the pipeline depends on.
- [development.md](development.md) -- the development loop end to end, from a clean checkout to
  a committed certificate.
- [setup-without-nix.md](setup-without-nix.md) -- best-effort setup for a machine without Nix.

See also the root [CONTRIBUTING.md](../CONTRIBUTING.md) for the short contributor entry point.

## Navigation

- [Back to README](../README.md)
