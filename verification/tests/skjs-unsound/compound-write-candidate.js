"use strict";

// Diagnostic candidate, not a soundness repair. Preserve the false singleton
// expression claim while removing the earlier cell-contract/export obstacles.
// Use fresh AST/claims: spans and producer metadata must match the source revision.
function candidate(ast, original, file) {
  const source = ast.functions.find((f) => f.name === "staleCompound");
  const claims = structuredClone(original);
  const f = claims
    .find((f) => f.file === file)
    ?.functions.find(
      (f) =>
        f.name === source?.name &&
        JSON.stringify(f.namePos) === JSON.stringify(source.namePos),
    );
  if (!source || !f || source.body[0].name !== "cell" || !source.body[0].annot)
    throw Error(
      "expected the current staleCompound fixture and matching claims",
    );
  const edits = [];
  function forget(type) {
    if (!type || typeof type !== "object") return;
    if (type.a === "record")
      for (const field of type.fields)
        field.read = structuredClone(field.write);
    for (const value of Object.values(type)) forget(value);
  }
  function change(holder, site) {
    const before = structuredClone(holder.type);
    // The exit union is already interpreted by exact absorption. Preserve its
    // alternatives; isolate only the remaining standalone refined contracts.
    if (holder.type.atoms?.length > 1) return;
    forget(holder.type);
    if (JSON.stringify(before) !== JSON.stringify(holder.type))
      edits.push({
        ...site,
        before,
        after: structuredClone(holder.type),
        reason: "forget cell read refinement",
      });
  }
  for (const entry of f.envs)
    for (const binding of entry.vars)
      change(binding, {
        kind: "entry",
        span: entry.pos,
        binding: binding.name,
      });
  for (const expr of f.exprs)
    change(expr, { kind: "expression", span: expr.pos });
  return { claims, edits };
}
module.exports = { candidate };

// node compound-write-candidate.js ast.json original.json file-key > candidate.json
if (require.main === module) {
  const fs = require("node:fs");
  const [ast, claims, file] = process.argv.slice(2);
  if (!ast || !claims || !file)
    throw Error("expected ast.json original.json file-key");
  const result = candidate(
    JSON.parse(fs.readFileSync(ast)),
    JSON.parse(fs.readFileSync(claims)),
    file,
  );
  process.stdout.write(JSON.stringify(result.claims, null, 2) + "\n");
  process.stderr.write(JSON.stringify(result.edits, null, 2) + "\n");
}
