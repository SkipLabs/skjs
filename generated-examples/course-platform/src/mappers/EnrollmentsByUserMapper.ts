import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  EnrollmentKey,
  Enrollment_skip_value_,
  User_skip_id_,
  EnrollmentByUserValue,
  Enrollment,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each enrollment entry, when the entry's key's userId field does not equal the userId param, emit nothing. Otherwise, when the status param is present AND the entry's value's status field does not equal the status param, emit nothing. Otherwise emit one output pair whose key is sourced from the entry's key's userId field, paired with a new EnrollmentByUserValue value whose courseId field is sourced from the entry's key's courseId field, whose userId field is sourced from the entry's key's userId field, and whose status, progressPercent, enrolledAt, completedAt fields are sourced from the corresponding fields of the entry's value.
export class EnrollmentsByUserMapper implements Mapper<
  EnrollmentKey,
  Enrollment_skip_value_,
  User_skip_id_,
  EnrollmentByUserValue
> {
  constructor(
    private userId: string,
    private status: string | null,
  ) {}

  mapEntry(
    key: EnrollmentKey,
    values: Values<Enrollment_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, EnrollmentByUserValue]> {
    // > body
    const emits: [User_skip_id_, EnrollmentByUserValue][] = [];
    if (key.userId !== this.userId) return emits;
    for (const value of values.toArray()) {
      if (this.status !== null && value.status !== this.status) continue;
      const out: EnrollmentByUserValue = {
        courseId: key.courseId,
        userId: key.userId,
        status: value.status,
        progressPercent: value.progressPercent,
        enrolledAt: value.enrolledAt,
        ...(value.completedAt !== undefined && {
          completedAt: value.completedAt,
        }),
      };
      emits.push([key.userId, out]);
    }
    return emits;
    // < body
  }
}
