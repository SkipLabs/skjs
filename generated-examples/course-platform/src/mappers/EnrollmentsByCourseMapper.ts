import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  EnrollmentKey,
  Enrollment_skip_value_,
  Course_skip_id_,
  EnrollmentByCourseValue,
  Enrollment,
  Course,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each enrollment entry, emit one output pair whose key is sourced from the entry's key's courseId field, paired with a new EnrollmentByCourseValue value whose courseId field is sourced from the entry's key's courseId field, whose userId field is sourced from the entry's key's userId field, and whose status, progressPercent, enrolledAt, completedAt fields are sourced from the corresponding fields of the entry's value.
export class EnrollmentsByCourseMapper implements Mapper<
  EnrollmentKey,
  Enrollment_skip_value_,
  Course_skip_id_,
  EnrollmentByCourseValue
> {
  mapEntry(
    key: EnrollmentKey,
    values: Values<Enrollment_skip_value_>,
    context: Context,
  ): Iterable<[Course_skip_id_, EnrollmentByCourseValue]> {
    // > body
    const emits: [Course_skip_id_, EnrollmentByCourseValue][] = [];
    for (const value of values) {
      const out: EnrollmentByCourseValue = {
        courseId: key.courseId,
        userId: key.userId,
        status: value.status,
        progressPercent: value.progressPercent,
        enrolledAt: value.enrolledAt,
        ...(value.completedAt !== undefined && {
          completedAt: value.completedAt,
        }),
      };
      emits.push([key.courseId, out]);
    }
    return emits;
    // < body
  }
}
