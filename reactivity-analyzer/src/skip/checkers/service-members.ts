/**
 * Checker: validate required/allowed members on SkipService.
 */

import { withEndCol } from "../../infra/ast-inspection.js";
import type { Violation } from "../../infra/checker.js";
import type { Checker } from "./types.js";

const NAME = "service-members";

export const serviceMembersChecker: Checker = {
  name: NAME,
  onMergedReport: (report) => {
    if (report.serviceClasses.length !== 1) return [];

    const svc = report.serviceClasses[0]!;
    const violations: Violation[] = [];
    const required = new Set(["resources", "createGraph"]);
    const optional = new Set(["initialData", "externalServices"]);
    const allowed = new Set([...required, ...optional]);

    const members = new Map<string, typeof svc.members[0]>();
    for (const member of svc.members) {
      if (member.kind === "unknown") {
        violations.push({
          checker: NAME,
          message: "Service class has an unrecognized member.",
          file: svc.file,
          pos: member.pos,
          details: { kind: member.kind },
        });
        continue;
      }

      if (member.kind === "constructor") {
        continue;
      }

      const name = member.name;
      if (!name) {
        violations.push({
          checker: NAME,
          message: "Service class has a member with a non-identifier name.",
          file: svc.file,
          pos: member.pos,
          details: { kind: member.kind },
        });
        continue;
      }

      if (!allowed.has(name)) {
        violations.push({
          checker: NAME,
          message: "Unexpected member on SkipService class: " + name,
          file: svc.file,
          pos: withEndCol(member.pos, name),
        });
        continue;
      }

      if (!members.has(name)) members.set(name, member);
    }

    for (const name of required) {
      if (!members.has(name)) {
        violations.push({
          checker: NAME,
          message: "Missing required service member: " + name,
          file: svc.file,
          pos: svc.pos,
        });
      }
    }

    return violations;
  },
};
