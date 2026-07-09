import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Course_skip_id_,
  CourseStored,
  Course_skip_value_,
  CountAccum,
  Course,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each course entry, consult lessonCountByCourse for the count indexed by the entry's key of type Course_skip_id_ (default zero when no values are consulted; otherwise take the first consulted value). Consult enrollmentCountByCourse for the count indexed by the entry's key of type Course_skip_id_ (default zero when no values are consulted; otherwise take the first consulted value). Emit one output pair whose key is the entry's key and whose value lists every required field of Course_skip_value_ explicitly: instructorId sourced from the entry's value's instructorId field; title sourced from the entry's value's title field; published sourced from the entry's value's published field; createdAt sourced from the entry's value's createdAt field; updatedAt sourced from the entry's value's updatedAt field; lessonCount sourced from the resolved lesson count; enrollmentCount sourced from the resolved enrollment count. Optional field description: present when the entry's value's description field is present, sourced from the entry's value's description field, absent otherwise. Preserve empty strings and explicit-absent verbatim — no sentinel substitution.
export class AssembleCourseWithCountsMapper implements Mapper<
  Course_skip_id_,
  CourseStored,
  Course_skip_id_,
  Course_skip_value_
> {
  constructor(
    private lessonCountByCourse: EagerCollection<Course_skip_id_, CountAccum>,
    private enrollmentCountByCourse: EagerCollection<
      Course_skip_id_,
      CountAccum
    >,
  ) {}

  mapEntry(
    key: Course_skip_id_,
    values: Values<CourseStored>,
    context: Context,
  ): Iterable<[Course_skip_id_, Course_skip_value_]> {
    // > body
    const emits: [Course_skip_id_, Course_skip_value_][] = [];
    for (const value of values.toArray()) {
      const lessonCounts = this.lessonCountByCourse.getArray(key);
      const lessonCount =
        lessonCounts.length === 0 ? 0 : (lessonCounts[0] ?? 0);
      const enrollmentCounts = this.enrollmentCountByCourse.getArray(key);
      const enrollmentCount =
        enrollmentCounts.length === 0 ? 0 : (enrollmentCounts[0] ?? 0);
      const out: Course_skip_value_ = {
        instructorId: value.instructorId,
        title: value.title,
        published: value.published,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        lessonCount,
        enrollmentCount,
        ...(value.description !== undefined && {
          description: value.description,
        }),
      };
      emits.push([key, out]);
    }
    return emits;
    // < body
  }
}
