import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Course_skip_id_, Course_skip_value_, Course } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each course entry, emit the entry unchanged when (the instructorId param is absent OR the entry's value's instructorId field equals the instructorId param) AND (the published param is absent OR (the published param is true AND the entry's value's status field equals the literal 'PUBLISHED') OR (the published param is false AND the entry's value's status field equals the literal 'DRAFT')). Otherwise emit nothing.
export class FilterCoursesMapper implements Mapper<
  Course_skip_id_,
  Course_skip_value_,
  Course_skip_id_,
  Course_skip_value_
> {
  constructor(
    private instructorId: string | null,
    private published: boolean | null,
  ) {}

  mapEntry(
    key: Course_skip_id_,
    values: Values<Course_skip_value_>,
    context: Context,
  ): Iterable<[Course_skip_id_, Course_skip_value_]> {
    // > body
    const emits: [Course_skip_id_, Course_skip_value_][] = [];
    for (const value of values.toArray()) {
      const instructorOk =
        this.instructorId === null || value.instructorId === this.instructorId;
      const publishedOk =
        this.published === null ||
        (this.published === true && value.status === "PUBLISHED") ||
        (this.published === false && value.status === "DRAFT");
      if (instructorOk && publishedOk) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
