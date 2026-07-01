import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  EnrollmentKey,
  Enrollment_skip_value_,
  User_skip_id_,
  Enrollment,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each enrollment entry, emit one output pair whose key is sourced from the entry's key's userId field, paired with an Enrollment value listing every required field explicitly: courseId sourced from the entry's key's courseId field; userId sourced from the entry's key's userId field; enrolledAt sourced from the entry's value's enrolledAt field. The original courseId component of the entry's key is re-injected into the value's courseId field so the downstream consumer can reconstruct the full Enrollment entity.
export class EnrollmentByUserMapper implements Mapper<
  EnrollmentKey,
  Enrollment_skip_value_,
  User_skip_id_,
  Enrollment
> {
  mapEntry(
    key: EnrollmentKey,
    values: Values<Enrollment_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Enrollment]> {
    // > body
    const emits: [User_skip_id_, Enrollment][] = [];
    for (const value of values.toArray()) {
      const enrollment: Enrollment = {
        courseId: key.courseId,
        userId: key.userId,
        enrolledAt: value.enrolledAt,
      };
      emits.push([key.userId, enrollment]);
    }
    return emits;
    // < body
  }
}
