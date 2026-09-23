# Changelog

Notable changes to this example are documented in this file.

## [0.1.0]

First public release of SPSDemo, the worked example behind the talk "Verified Components from
Rust to Lean".

- The `framed_channel` example: a Rust implementation translated to Lean 4 through Charon/Aeneas,
  with a certificate over the resulting proof obligations and an independent recheck path.
- A Nix-based gate (`full-gate.sh`) and a CI workflow matrix covering build, verification and
  recheck across the platforms in `docs/ci.md`'s platform matrix.
- `docs/trust-model.md`, describing what the certificate and the gate do and do not establish.

The certificate identity is a content fingerprint over a gate run's inputs, not a version number:
it changes on every source edit. Compare a checkout against its committed records with
`bash framed_channel/scripts/certificate-identity.sh --check` rather than against another
release's digest.
