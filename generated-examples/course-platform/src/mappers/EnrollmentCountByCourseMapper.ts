import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Course_skip_id_,
  Enrollment,
  CountAccum,
  Course,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry (keyed by courseId, values are the Enrollment records under that course), emit one output pair whose key is the entry's key and whose value is the number of Enrollment values associated with that key (values.length). This computes the per-course enrollment count directly in a single mapper — no reducer needed because the values are already grouped by courseId.
export class EnrollmentCountByCourseMapper implements Mapper<
  Course_skip_id_,
  Enrollment,
  Course_skip_id_,
  CountAccum
> {
  mapEntry(
    key: Course_skip_id_,
    values: Values<Enrollment>,
    context: Context,
  ): Iterable<[Course_skip_id_, CountAccum]> {
    // > body
    let count = 0;
    for (const _ of values) count++;
    return [[key, count]];
    // < body
  }
}
