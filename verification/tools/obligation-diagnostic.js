"use strict";

// Optional explanatory metadata, never evidence. Unknown versions are left in
// the human diagnostic; they must not change the verification outcome.
function readDiagnostic(detail) {
  const lines = detail
    .split(/\r?\n/)
    .filter((line) => line.startsWith("obligation-diagnostic: "));
  if (lines.length !== 1) return undefined;
  let d;
  try {
    d = JSON.parse(lines[0].slice("obligation-diagnostic: ".length));
  } catch {
    return undefined;
  }
  if (
    d?.version !== 1 ||
    !["proof-search", "certificate-check", "request-validation"].includes(d.phase) ||
    d.outcome !== "not-established" ||
    !Array.isArray(d.types) ||
    !Number.isSafeInteger(d.fuel) ||
    d.fuel < 0
  )
    return undefined;
  if (
    ![
      "node-typing",
      "edge-coverage",
      "expression-claim",
      "production-failure",
    ].includes(d.kind)
  )
    return undefined;
  if (d.kind !== "production-failure" && typeof d.id !== "string")
    return undefined;
  if (
    d.kind === "edge-coverage" &&
    (!d.source || !d.destination || !d.transfer)
  )
    return undefined;
  if (["node-typing", "expression-claim"].includes(d.kind) && !d.sequent)
    return undefined;
  return d;
}
module.exports = { readDiagnostic };
