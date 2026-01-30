/**
 * Checker: require exactly one SkipService class in the project.
 */

import type { Checker } from "./types.js";

const NAME = "service-count";

export const serviceCountChecker: Checker = {
  name: NAME,
  onMergedReport: (report) => {
    const count = report.serviceClasses.length;
    if (count === 1) return [];

    const first = report.serviceClasses[0];
    const file = first ? first.file : report.sourceFile;
    const pos = first ? first.pos : undefined;

    return [
      {
        checker: NAME,
        message: "Expected exactly one SkipService class, found " + count + ".",
        file,
        pos,
        details: {
          count,
          serviceClasses: report.serviceClasses.map((s) => ({
            name: s.name,
            file: s.file,
            pos: s.pos,
          })),
        },
      },
    ];
  },
};
