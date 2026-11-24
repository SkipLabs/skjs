Except for README.txt, the files in this directory are copied VERBATIM (no
modifications) from the official TypeScript repository:
https://github.com/microsoft/TypeScript
(tsc/testdata/tests/cases/conformance for the cases, and
tsc/testdata/baselines/reference/conformance for the .errors.txt references).

They fall under Microsoft copyright, see CopyrightNotice.txt, and
the Apache license, see LICENSE.txt.

Layout: cases/ holds files that check as-is (in conformance mode).
not-supported/ holds verbatim files we tried to support but could not yet —
files are moved there manually, never copied in directly.
See docs/testing.md "TypeScript Conformance Tests".
