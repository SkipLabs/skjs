## Summary

<!-- What does this change do, and why? Keep it to summary + motivation. -->

## Checklist

<!-- See docs/commits-and-prs.md for the full policy. -->

- [ ] Bumped the version in `Skargo.toml` (patch = bug fix, minor = feature/behavior change, major = breaking)
- [ ] `make test-in-docker` passes
- [ ] `make fmt` run; formatting is clean
- [ ] Each commit is one logical change (an "and"/"also"/";" in a subject is a red flag)
- [ ] Tests introduced in a commit _before_ the code change that flips their annotations
- [ ] Updated `skjs-rules.md` if this changes what SKJS accepts or rejects
- [ ] AI-assisted changes carry a `Co-Authored-By` disclosure trailer (see [docs/commits-and-prs.md](../docs/commits-and-prs.md))
