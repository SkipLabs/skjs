import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  EnrollmentKey,
  Enrollment_skip_value_,
  Course_skip_id_,
  Enrollment,
  Course,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each enrollment entry, emit one output pair whose key is sourced from the entry's key's courseId field, paired with an Enrollment value listing every required field explicitly: courseId sourced from the entry's key's courseId field; userId sourced from the entry's key's userId field; enrolledAt sourced from the entry's value's enrolledAt field. The original userId component of the entry's key is re-injected into the value's userId field so the downstream consumer can reconstruct the full Enrollment entity.
export class EnrollmentByCourseMapper implements Mapper<
  EnrollmentKey,
  Enrollment_skip_value_,
  Course_skip_id_,
  Enrollment
> {
  mapEntry(
    key: EnrollmentKey,
    values: Values<Enrollment_skip_value_>,
    context: Context,
  ): Iterable<[Course_skip_id_, Enrollment]> {
    // > body
    const emits: [Course_skip_id_, Enrollment][] = [];
    for (const value of values.toArray()) {
      const enrollment: Enrollment = {
        courseId: key.courseId,
        userId: key.userId,
        enrolledAt: value.enrolledAt,
      };
      emits.push([key.courseId, enrollment]);
    }
    return emits;
    // < body
  }
}
