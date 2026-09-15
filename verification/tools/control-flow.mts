/** Native program-graph syntax, matching ControlFlow.lean and its derived JSON
 * codec. A node is one term plus the continuation that follows it, and every
 * destination states its label and slot map, so the graph is explicit program
 * data the reader validates rather than structure it infers from terms. */
import { decodeTerm, fields, isTag, nat, type Tag, type Term } from "./calculus-language.mts";

export interface Target { label: number; mapping: number[] | null }
export type Continuation = "ret"
  | {bind: {next: Target}} | {effect: {next: Target}}
  | {branch: {yes: Target; no: Target}}
  | {branchBind: {yes: Target; no: Target}}
  | {tagBind: {test: Tag; yes: Target; no: Target}};
export interface ProgramNode { expression: Term; continuation: Continuation }
export function decodeTarget(value: unknown): Target {
  const t = fields(value,["label","mapping"]); nat(t.label);
  if (t.mapping !== null) {
    if (!Array.isArray(t.mapping)) throw Error("invalid slot mapping");
    t.mapping.forEach(nat);
  }
  return value as Target;
}
export function decodeNode(value: unknown): ProgramNode {
  const n = fields(value,["expression","continuation"]); decodeTerm(n.expression);
  if (n.continuation === "ret") return value as ProgramNode;
  if (!n.continuation || typeof n.continuation !== "object") throw Error("invalid continuation");
  const k = Object.keys(n.continuation)[0], outer = fields(n.continuation,[k]);
  switch (k) {
    case "bind": case "effect": decodeTarget(fields(outer[k],["next"]).next); break;
    case "branch": case "branchBind": case "tagBind": {
      const c = fields(outer[k], k === "tagBind" ? ["test","yes","no"] : ["yes","no"]);
      decodeTarget(c.yes); decodeTarget(c.no);
      if (k === "tagBind" && !isTag(c.test)) throw Error("invalid tag");
      break;
    }
    default: throw Error("unknown continuation");
  }
  return value as ProgramNode;
}
